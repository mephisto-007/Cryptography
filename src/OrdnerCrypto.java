import javax.crypto.Cipher;
import javax.crypto.Mac;
import javax.crypto.SecretKey;
import javax.crypto.SecretKeyFactory;
import javax.crypto.spec.GCMParameterSpec;
import javax.crypto.spec.PBEKeySpec;
import javax.crypto.spec.SecretKeySpec;

import java.io.*;
import java.nio.ByteBuffer;
import java.nio.file.*;
import java.security.SecureRandom;
import java.util.Scanner;
import java.util.stream.Stream;

/**
 * OrdnerCrypto – Passwortbasierte Verschlüsselung ganzer Ordner (und damit auch
 * ganzer Laufwerke, sofern man deren Wurzelverzeichnis als Quelle angibt).
 * *
 * WICHTIGER HINWEIS ZU "LAUFWERKEN":
 * Dieses Programm arbeitet auf Dateiebene, d.h. es liest jede Datei über das
 * normale Dateisystem und verschlüsselt sie einzeln. Das ist etwas anderes als
 * "echte" Festplattenverschlüsselung wie BitLocker oder LUKS, die auf Ebene der
 * Speicherblöcke arbeitet und z.B. auch das Betriebssystem selbst verschlüsseln
 * kann. Für ein laufendes System-/Boot-Laufwerk ist dieses Tool NICHT geeignet
 * (Dateien, die gerade vom Betriebssystem benutzt werden, lassen sich nicht
 * einfach lesen/überschreiben). Für Daten-Laufwerke oder externe Datenträger
 * funktioniert es aber sehr gut.
 *
 * AUFRUF:
 *   java OrdnerCrypto verschluesseln <Quellordner> <Zielordner>
 *   java OrdnerCrypto entschluesseln <Quellordner> <Zielordner>
 *
 * Das Passwort wird interaktiv (nach Möglichkeit ohne Bildschirmanzeige) abgefragt.
 */
public class OrdnerCrypto {

    // ============================================================
    // 1) KONSTANTEN – zentrale Stellschrauben der Kryptografie
    // ============================================================

    // "Magic Bytes" am Anfang jeder verschlüsselten Datei, damit wir beim
    // Entschlüsseln erkennen, ob es sich überhaupt um eine von uns erzeugte
    // Datei im richtigen Format handelt.
    private static final byte[] MAGIC = {'J', 'F', 'C', '1'};

    private static final int SALT_LEN = 16;              // 128 Bit Salt je Datei
    private static final int NONCE_PREFIX_LEN = 4;        // zufälliger Teil des Nonces je Datei
    private static final int GCM_TAG_LEN_BIT = 128;        // Länge des Auth-Tags von AES-GCM
    private static final int GCM_TAG_LEN_BYTE = GCM_TAG_LEN_BIT / 8;

    // Größe der Blöcke ("Chunks"), in denen eine Datei ver-/entschlüsselt wird.
    // Wichtig für große Dateien (mehrere GB): So muss nie die komplette Datei
    // auf einmal im Arbeitsspeicher liegen, sondern immer nur ein 8-MB-Block.
    private static final int CHUNK_SIZE = 8 * 1024 * 1024; // 8 MB

    // Iterationszahl für PBKDF2 – bewusst hoch gewählt (OWASP-Empfehlung 2023),
    // damit das Ausprobieren vieler Passwörter (Brute-Force) teuer/langsam ist.
    // Wird nur EINMAL pro Ordner ausgeführt, nicht pro Datei (siehe Abschnitt 3).
    private static final int PBKDF2_ITERATIONEN = 480_000;
    private static final int MASTERSCHLUESSEL_BIT = 256;

    // Name der kleinen Metadatendatei, die im Zielordner abgelegt wird und
    // das (zufällige) Salt für die Masterschlüssel-Ableitung enthält. Dieses
    // Salt ist kein Geheimnis, es macht nur sicher, dass zwei Ordner mit dem
    // gleichen Passwort trotzdem unterschiedliche Schlüssel bekommen.
    private static final String ORDNER_META_DATEI = "ordner.meta";

    private static final SecureRandom ZUFALLSGENERATOR = new SecureRandom();

    // ============================================================
    // 2) EINSTIEGSPUNKT
    // ============================================================

    public static void main(String[] args) {
        if (args.length != 3) {
            System.err.println("Verwendung:");
            System.err.println("  java OrdnerCrypto verschluesseln <Quellordner> <Zielordner>");
            System.err.println("  java OrdnerCrypto entschluesseln <Quellordner> <Zielordner>");
            System.exit(1);
        }

        String modus = args[0];
        Path quelle = Paths.get(args[1]);
        Path ziel = Paths.get(args[2]);

        if (!Files.isDirectory(quelle)) {
            System.err.println("Fehler: Quellordner existiert nicht oder ist kein Verzeichnis: " + quelle);
            System.exit(1);
        }

        // Passwort interaktiv abfragen. System.console() liefert null, wenn das
        // Programm z.B. aus einer IDE gestartet wird, die kein "echtes" Terminal
        // bereitstellt – dann weichen wir auf eine sichtbare Eingabe über
        // Scanner aus und weisen den Nutzer darauf hin.
        char[] passwort = passwortAbfragen(modus.equals("verschluesseln"));

        try {
            long start = System.currentTimeMillis();
            if (modus.equals("verschluesseln")) {
                ordnerVerschluesseln(quelle, ziel, passwort);
            } else if (modus.equals("entschluesseln")) {
                ordnerEntschluesseln(quelle, ziel, passwort);
            } else {
                System.err.println("Unbekannter Modus: " + modus);
                System.exit(1);
            }
            long dauer = System.currentTimeMillis() - start;
            System.out.println("Fertig in " + dauer + " ms.");
        } catch (Exception e) {
            System.err.println("Fehler: " + e.getMessage());
            System.exit(1);
        } finally {
            // Passwort so früh wie möglich aus dem Speicher löschen (überschreiben).
            // char[] lässt sich im Gegensatz zu String gezielt überschreiben –
            // deshalb verwenden wir bewusst char[] statt String für das Passwort.
            java.util.Arrays.fill(passwort, '\0');
        }
    }

    /**
     * Fragt das Passwort interaktiv ab. Nutzt, wenn verfügbar, die Konsole
     * (verdeckte Eingabe ohne Anzeige auf dem Bildschirm). Bei Verschlüsselung
     * wird das Passwort zusätzlich zur Bestätigung ein zweites Mal abgefragt,
     * um Tippfehler zu vermeiden (sonst verliert man sonst später alle Daten!).
     */
    // Eine einzige, wiederverwendete Scanner-Instanz für den Fallback ohne
    // echtes Terminal. Mehrere neue Scanner-Objekte auf demselben System.in
    // können sich beim internen Puffern gegenseitig ins Gehege kommen.
    private static Scanner fallbackScanner;

    private static char[] passwortAbfragen(boolean mitBestaetigung) {
        Console console = System.console();
        char[] passwort;
        if (console != null) {
            passwort = console.readPassword("Passwort: ");
        } else {
            if (fallbackScanner == null) {
                fallbackScanner = new Scanner(System.in);
            }
            System.out.print("Passwort (Achtung: wird evtl. sichtbar angezeigt): ");
            passwort = fallbackScanner.nextLine().toCharArray();
        }

        if (mitBestaetigung) {
            char[] bestaetigung;
            if (console != null) {
                bestaetigung = console.readPassword("Passwort bestätigen: ");
            } else {
                System.out.print("Passwort bestätigen: ");
                bestaetigung = fallbackScanner.nextLine().toCharArray();
            }
            if (!java.util.Arrays.equals(passwort, bestaetigung)) {
                System.err.println("Fehler: Passwörter stimmen nicht überein.");
                System.exit(1);
            }
            java.util.Arrays.fill(bestaetigung, '\0');
        }

        if (passwort.length < 8) {
            System.out.println("Warnung: Sehr kurzes Passwort – 12+ Zeichen sind empfohlen.");
        }
        return passwort;
    }

    // ============================================================
    // 3) SCHLÜSSELABLEITUNG (Schlüssel-Hierarchie)
    // ============================================================
    //
    // Warum eine Hierarchie aus Master- und Dateischlüsseln?
    // - PBKDF2 mit 480.000 Iterationen ist absichtlich LANGSAM (Schutz gegen
    //   Brute-Force). Bei einem Ordner mit tausenden Dateien dürfen wir das
    //   aber nicht pro Datei wiederholen, sonst dauert die Verschlüsselung
    //   eines ganzen Laufwerks Stunden.
    // - Deshalb: PBKDF2 wird NUR EINMAL pro Ordner ausgeführt und erzeugt einen
    //   "Masterschlüssel". Für jede einzelne Datei wird daraus mit einer
    //   schnellen Operation (HMAC-SHA256) ein eigener, einzigartiger
    //   Dateischlüssel abgeleitet. Das ist ein etabliertes Muster (ähnlich zu
    //   HKDF) und stellt sicher, dass ein Angriff auf eine Datei nicht die
    //   anderen Dateien gefährdet.

    /** Leitet aus dem Passwort und einem Ordner-Salt den Masterschlüssel ab (PBKDF2). */
    private static SecretKey masterschluesselAbleiten(char[] passwort, byte[] ordnerSalt) throws Exception {
        SecretKeyFactory factory = SecretKeyFactory.getInstance("PBKDF2WithHmacSHA256");
        PBEKeySpec spec = new PBEKeySpec(passwort, ordnerSalt, PBKDF2_ITERATIONEN, MASTERSCHLUESSEL_BIT);
        byte[] keyBytes = factory.generateSecret(spec).getEncoded();
        spec.clearPassword(); // Kopie des Passworts innerhalb des Specs löschen
        return new SecretKeySpec(keyBytes, "AES");
    }

    /**
     * Leitet aus dem Masterschlüssel und einem zufälligen Datei-Salt einen
     * eigenen 256-Bit-Schlüssel für genau EINE Datei ab. Verwendet HMAC-SHA256
     * als schnelle, kryptographisch sichere Ableitungsfunktion.
     */
    private static SecretKey dateischluesselAbleiten(SecretKey masterschluessel, byte[] dateiSalt) throws Exception {
        Mac hmac = Mac.getInstance("HmacSHA256");
        hmac.init(masterschluessel);
        byte[] abgeleitet = hmac.doFinal(dateiSalt);
        return new SecretKeySpec(abgeleitet, "AES");
    }

    /**
     * Berechnet den 12-Byte-Nonce für einen bestimmten Block ("Chunk") einer
     * Datei: 4 zufällige Bytes (pro Datei einmal gewürfelt) + 8 Bytes
     * fortlaufender Zähler. So ist garantiert, dass innerhalb einer Datei nie
     * derselbe Nonce zweimal mit demselben Schlüssel verwendet wird – das wäre
     * bei AES-GCM ein schwerwiegender Sicherheitsfehler.
     */
    private static byte[] nonceFuerChunk(byte[] noncePrefix, long chunkNummer) {
        ByteBuffer buf = ByteBuffer.allocate(NONCE_PREFIX_LEN + 8);
        buf.put(noncePrefix);
        buf.putLong(chunkNummer);
        return buf.array();
    }

    // ============================================================
    // 4) ORDNER VERSCHLÜSSELN
    // ============================================================

    private static void ordnerVerschluesseln(Path quelle, Path ziel, char[] passwort) throws Exception {
        Files.createDirectories(ziel);

        // Zufälliges Salt für diesen Ordner erzeugen und in einer kleinen
        // Metadatendatei ablegen. Ohne dieses Salt kann man später beim
        // Entschlüsseln nicht mehr den richtigen Masterschlüssel berechnen.
        byte[] ordnerSalt = new byte[SALT_LEN];
        ZUFALLSGENERATOR.nextBytes(ordnerSalt);
        Files.write(ziel.resolve(ORDNER_META_DATEI), ordnerSalt);

        SecretKey masterschluessel = masterschluesselAbleiten(passwort, ordnerSalt);

        // Alle Dateien im Quellordner rekursiv einsammeln (inkl. Unterordner).
        try (Stream<Path> alleEintraege = Files.walk(quelle)) {
            long[] zaehler = {0}; // Array als "veränderlicher" Zähler in der Lambda-Funktion
            alleEintraege
                    .filter(Files::isRegularFile)
                    .forEach(datei -> {
                        try {
                            // Relativen Pfad berechnen, damit die Ordnerstruktur im
                            // Zielverzeichnis identisch nachgebildet wird.
                            Path relativ = quelle.relativize(datei);
                            Path zielDatei = ziel.resolve(relativ.toString() + ".enc");
                            Files.createDirectories(zielDatei.getParent());

                            datei_Verschluesseln(datei, zielDatei, masterschluessel);
                            zaehler[0]++;
                            System.out.println("[" + zaehler[0] + "] verschlüsselt: " + relativ);
                        } catch (Exception e) {
                            System.err.println("Fehler bei Datei " + datei + ": " + e.getMessage());
                        }
                    });
        }
    }

    /**
     * Verschlüsselt genau EINE Datei blockweise ("Chunking"), sodass auch
     * mehrere GB große Dateien nur wenige MB Arbeitsspeicher benötigen.
     *
     * Aufbau der Ausgabedatei:
     *   MAGIC (4 Byte)
     *   Datei-Salt (16 Byte)          -> für die Dateischlüssel-Ableitung
     *   Nonce-Prefix (4 Byte)         -> für die Nonce-Berechnung je Chunk
     *   Originallänge (8 Byte, long)  -> zur Prüfung nach dem Entschlüsseln
     *   danach pro Chunk:
     *     Chunk-Länge (4 Byte, int)   -> Länge des verschlüsselten Chunks
     *     Chunk-Daten (Chunk-Länge Byte, inkl. 16 Byte GCM-Auth-Tag am Ende)
     */
    private static void datei_Verschluesseln(Path eingabe, Path ausgabe, SecretKey masterschluessel) throws Exception {
        byte[] dateiSalt = new byte[SALT_LEN];
        ZUFALLSGENERATOR.nextBytes(dateiSalt);
        byte[] noncePrefix = new byte[NONCE_PREFIX_LEN];
        ZUFALLSGENERATOR.nextBytes(noncePrefix);

        SecretKey dateischluessel = dateischluesselAbleiten(masterschluessel, dateiSalt);
        long originalLaenge = Files.size(eingabe);

        try (InputStream in = new BufferedInputStream(Files.newInputStream(eingabe));
             OutputStream out = new BufferedOutputStream(Files.newOutputStream(ausgabe))) {

            // --- Kopfbereich (Header) schreiben ---
            out.write(MAGIC);
            out.write(dateiSalt);
            out.write(noncePrefix);
            out.write(langZuBytes(originalLaenge));

            byte[] puffer = new byte[CHUNK_SIZE];
            long chunkNummer = 0;
            int gelesen;

            // --- Datei blockweise lesen, verschlüsseln, schreiben ---
            while ((gelesen = vollstaendigLesen(in, puffer)) > 0) {
                byte[] nonce = nonceFuerChunk(noncePrefix, chunkNummer);

                Cipher cipher = Cipher.getInstance("AES/GCM/NoPadding");
                GCMParameterSpec gcmSpec = new GCMParameterSpec(GCM_TAG_LEN_BIT, nonce);
                cipher.init(Cipher.ENCRYPT_MODE, dateischluessel, gcmSpec);

                // doFinal() verschlüsselt EINEN Chunk komplett und hängt am Ende
                // automatisch den 16-Byte-Authentifizierungs-Tag an. Dieser Tag
                // erkennt später jede Manipulation dieses Chunks.
                byte[] chiffretext = cipher.doFinal(puffer, 0, gelesen);

                out.write(intZuBytes(chiffretext.length));
                out.write(chiffretext);

                chunkNummer++;
            }
        }
    }

    // ============================================================
    // 5) ORDNER ENTSCHLÜSSELN
    // ============================================================

    private static void ordnerEntschluesseln(Path quelle, Path ziel, char[] passwort) throws Exception {
        Path metaDatei = quelle.resolve(ORDNER_META_DATEI);
        if (!Files.exists(metaDatei)) {
            throw new IOException("Metadatendatei '" + ORDNER_META_DATEI + "' nicht gefunden. " +
                    "Ist das wirklich ein mit diesem Programm verschlüsselter Ordner?");
        }
        byte[] ordnerSalt = Files.readAllBytes(metaDatei);
        SecretKey masterschluessel = masterschluesselAbleiten(passwort, ordnerSalt);

        Files.createDirectories(ziel);

        try (Stream<Path> alleEintraege = Files.walk(quelle)) {
            long[] zaehler = {0};
            alleEintraege
                    .filter(Files::isRegularFile)
                    .filter(p -> p.toString().endsWith(".enc"))
                    .forEach(datei -> {
                        try {
                            Path relativ = quelle.relativize(datei);
                            String relativStr = relativ.toString();
                            String ohneEndung = relativStr.substring(0, relativStr.length() - ".enc".length());
                            Path zielDatei = ziel.resolve(ohneEndung);
                            Files.createDirectories(zielDatei.getParent());

                            datei_Entschluesseln(datei, zielDatei, masterschluessel);
                            zaehler[0]++;
                            System.out.println("[" + zaehler[0] + "] entschlüsselt: " + ohneEndung);
                        } catch (Exception e) {
                            System.err.println("Fehler bei Datei " + datei + " (falsches Passwort oder " +
                                    "beschädigte Datei?): " + e.getMessage());
                        }
                    });
        }
    }

    private static void datei_Entschluesseln(Path eingabe, Path ausgabe, SecretKey masterschluessel) throws Exception {
        try (InputStream in = new BufferedInputStream(Files.newInputStream(eingabe));
             OutputStream out = new BufferedOutputStream(Files.newOutputStream(ausgabe))) {

            // --- Kopfbereich (Header) lesen und prüfen ---
            byte[] magic = new byte[MAGIC.length];
            vollstaendigLesen(in, magic);
            if (!java.util.Arrays.equals(magic, MAGIC)) {
                throw new IOException("Ungültiges Dateiformat (falsche/beschädigte Datei).");
            }

            byte[] dateiSalt = new byte[SALT_LEN];
            vollstaendigLesen(in, dateiSalt);
            byte[] noncePrefix = new byte[NONCE_PREFIX_LEN];
            vollstaendigLesen(in, noncePrefix);
            byte[] laengeBytes = new byte[8];
            vollstaendigLesen(in, laengeBytes);
            long originalLaenge = bytesZuLang(laengeBytes);

            SecretKey dateischluessel = dateischluesselAbleiten(masterschluessel, dateiSalt);

            long chunkNummer = 0;
            long geschriebeneBytes = 0;
            byte[] laengePuffer = new byte[4];

            // --- Chunks nacheinander lesen, entschlüsseln, schreiben ---
            while (vollstaendigLesen(in, laengePuffer) == 4) {
                int chiffretextLaenge = bytesZuInt(laengePuffer);
                byte[] chiffretext = new byte[chiffretextLaenge];
                int tatsaechlichGelesen = vollstaendigLesen(in, chiffretext);
                if (tatsaechlichGelesen != chiffretextLaenge) {
                    throw new IOException("Datei ist unvollständig oder beschädigt.");
                }

                byte[] nonce = nonceFuerChunk(noncePrefix, chunkNummer);
                Cipher cipher = Cipher.getInstance("AES/GCM/NoPadding");
                GCMParameterSpec gcmSpec = new GCMParameterSpec(GCM_TAG_LEN_BIT, nonce);
                cipher.init(Cipher.DECRYPT_MODE, dateischluessel, gcmSpec);

                // doFinal() prüft hier automatisch den Auth-Tag. Stimmt er nicht
                // (falsches Passwort ODER manipulierte/beschädigte Daten), wirft
                // Java eine AEADBadTagException – das fangen wir weiter oben ab.
                byte[] klartext = cipher.doFinal(chiffretext);

                out.write(klartext);
                geschriebeneBytes += klartext.length;
                chunkNummer++;
            }

            if (geschriebeneBytes != originalLaenge) {
                throw new IOException("Entschlüsselte Datenmenge stimmt nicht mit der " +
                        "erwarteten Originallänge überein – Datei evtl. beschädigt.");
            }
        }
    }

    // ============================================================
    // 6) HILFSFUNKTIONEN
    // ============================================================

    /**
     * Liest so lange aus dem Stream, bis entweder der Puffer voll ist oder das
     * Streamende erreicht wurde. Der normale InputStream.read() garantiert
     * NICHT, dass er den Puffer in einem Aufruf komplett füllt – deshalb diese
     * kleine Schleife, die das für uns übernimmt.
     */
    private static int vollstaendigLesen(InputStream in, byte[] puffer) throws IOException {
        int gesamtGelesen = 0;
        while (gesamtGelesen < puffer.length) {
            int n = in.read(puffer, gesamtGelesen, puffer.length - gesamtGelesen);
            if (n == -1) break; // Stream zu Ende
            gesamtGelesen += n;
        }
        return gesamtGelesen;
    }

    private static byte[] intZuBytes(int wert) {
        return ByteBuffer.allocate(4).putInt(wert).array();
    }

    private static byte[] langZuBytes(long wert) {
        return ByteBuffer.allocate(8).putLong(wert).array();
    }

    private static int bytesZuInt(byte[] bytes) {
        return ByteBuffer.wrap(bytes).getInt();
    }

    private static long bytesZuLang(byte[] bytes) {
        return ByteBuffer.wrap(bytes).getLong();
    }
}