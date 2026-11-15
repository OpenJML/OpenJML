package org.jmlspecs.openjml.utils;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.HexFormat;

/** Checksums of file contents, used to detect that a file changed (e.g. between Strongarm inference rounds). */
public class FileChecksum {

    /** Returns the SHA-256 digest of the file's contents. */
    public static byte[] createChecksum(String filename) throws IOException {
        MessageDigest digest;
        try {
            digest = MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException e) {
            throw new AssertionError("SHA-256 is always available", e);
        }
        try (InputStream in = Files.newInputStream(Paths.get(filename))) {
            byte[] buffer = new byte[8192];
            int n;
            while ((n = in.read(buffer)) != -1) {
                digest.update(buffer, 0, n);
            }
        }
        return digest.digest();
    }

    /** Returns the SHA-256 digest of the file's contents, as lowercase hex. */
    public static String getChecksum(String filename) throws IOException {
        return HexFormat.of().formatHex(createChecksum(filename));
    }
}
