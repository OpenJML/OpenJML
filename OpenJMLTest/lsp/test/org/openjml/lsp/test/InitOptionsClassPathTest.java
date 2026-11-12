package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.nio.file.Files;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * A {@code classPath} given in {@code initializationOptions}, with no {@code projects}
 * list (VS Code, Neovim and other plain LSP clients), reaches the check (issue #1089).
 */
public class InitOptionsClassPathTest extends ProtocolTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    @Test
    public void classPathFromInitializationOptionsIsUsed() throws Exception {
        // A compiled library class, reachable only through the class path.
        File libSrc = tmp.newFolder("libsrc");
        File libClasses = tmp.newFolder("libclasses");
        File libFile = new File(libSrc, "LibThing.java");
        Files.writeString(libFile.toPath(),
                "package lib;\npublic class LibThing { public static int one() { return 1; } }\n");
        // A separate process (an in-process javac would share OpenJML's compiler classes),
        // with JML processing off (NOJML) so it is a plain javac.
        String javac = System.getProperty("java.home") + File.separator + "bin" + File.separator + "javac";
        ProcessBuilder pb = new ProcessBuilder(javac, "-d", libClasses.getAbsolutePath(), libFile.getAbsolutePath())
                .inheritIO();
        pb.environment().put("NOJML", "1");
        assertEquals("compiling the library", 0, pb.start().waitFor());
        assertTrue("library class written", new File(libClasses, "lib/LibThing.class").isFile());

        createServerAndClient();
        client.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":null,\"capabilities\":{},"
                + "\"initializationOptions\":{\"classPath\":\""
                + jsonEscape(libClasses.getAbsolutePath()) + "\"}}");
        assertNotNull("Server must respond to initialize",
                client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS));
        client.sendNotification("initialized", "{}");

        File src = tmp.newFolder("src");
        File user = new File(src, "UsesLib.java");
        String source = "import lib.LibThing;\n"
                + "public class UsesLib { public int m() { return LibThing.one(); } }\n";
        Files.writeString(user.toPath(), source);
        JsonObject note = openAndWaitForCheck(user.toPath().toUri().toString(), source);
        assertNotNull("Expected publishDiagnostics for UsesLib", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertEquals("no diagnostics expected, got: " + diags, 0, diags.size());
    }
}
