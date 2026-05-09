package org.openjml.lsp;

import java.io.InputStream;
import java.util.Properties;

/** OpenJML LSP server version, loaded from the bundled {@code version.properties} resource. */
public final class LspVersion {

    public static final String VERSION;

    static {
        String v = "(unknown)";
        try (InputStream is = LspVersion.class.getResourceAsStream("version.properties")) {
            if (is != null) {
                Properties p = new Properties();
                p.load(is);
                v = p.getProperty("version", "(unknown)");
            }
        } catch (Exception ignored) {}
        VERSION = v;
    }

    private LspVersion() {}
}
