package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.OpenJMLCommands;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Code lenses after {@code openjml.checkJML} in a workspace with manual triggers, as the
 * VS Code extension sends it.  That check is a directory check, whose ASTs go to the nav
 * tier of the AST cache; the codeLens handler must find them there.
 */
public class CodeLensAfterCheckJmlTest extends ProtocolTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    @Before
    @Override
    public void setUp() throws Exception {
        startServer();
    }

    @Test
    public void testCodeLensesAfterCheckJml() throws Exception {
        Path root = tmp.getRoot().toPath();
        String source = "public class LensAfterCheck {\n"
                + "    //@ ensures \\result == a;\n"
                + "    public int id(int a) { return a; }\n"
                + "    public int two() { return 2; }\n"
                + "}\n";
        Path file = root.resolve("LensAfterCheck.java");
        Files.writeString(file, source);
        String uri = file.toUri().toString();

        client.sendNotification("workspace/didChangeConfiguration",
                "{\"settings\":{\"openjml\":{\"checkTriggerOn\":\"manual\",\"escTriggerOn\":\"manual\","
                + "\"projects\":[{\"id\":\"__workspace__\",\"rootPaths\":[\"" + jsonEscape(root.toString()) + "\"]}]}}}");
        Thread.sleep(200);
        didOpen(uri, source);

        executeCommand(OpenJMLCommands.CHECK_JML,
                "[\"\",\"" + jsonEscape(file.toString()) + "\"]");
        assertNotNull("Expected publishDiagnostics after Check JML",
                nextDiagsFor("LensAfterCheck", TIMEOUT_SECONDS, TimeUnit.SECONDS));

        JsonArray lenses = null;
        long deadline = System.currentTimeMillis() + 10_000;
        while (System.currentTimeMillis() < deadline) {
            lenses = requestCodeLens(uri);
            if (lenses != null && lenses.size() >= 3) break;
            Thread.sleep(250);
        }
        assertNotNull("No codeLens response", lenses);
        // One per method, including the default constructor.
        assertEquals("Expected one lens per method after Check JML", 3, lenses.size());
    }
}
