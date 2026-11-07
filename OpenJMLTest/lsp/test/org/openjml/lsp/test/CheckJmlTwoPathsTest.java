package org.openjml.lsp.test;

import com.google.gson.JsonObject;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.OpenJMLCommands;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Two {@code openjml.checkJML} commands for different paths sent back to back, as the
 * Eclipse plugin does when several projects are selected (one command per project).
 * Both checks must run; the debounce may only collapse repeats of the same request.
 */
public class CheckJmlTwoPathsTest extends ProtocolTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    @Before
    @Override
    public void setUp() throws Exception {
        startServer();
    }

    @Test
    public void testBothChecksRun() throws Exception {
        Path root = tmp.getRoot().toPath();
        Path dirA = Files.createDirectories(root.resolve("projA"));
        Path dirB = Files.createDirectories(root.resolve("projB"));
        Files.writeString(dirA.resolve("BadA.java"),
                "public class BadA {\n    //@ requires x > \"a\";\n    public void m(int x) {}\n}\n");
        Files.writeString(dirB.resolve("BadB.java"),
                "public class BadB {\n    //@ requires x > \"b\";\n    public void m(int x) {}\n}\n");

        executeCommand(OpenJMLCommands.CHECK_JML, "[\"\",\"" + jsonEscape(dirA.toString()) + "\"]");
        executeCommand(OpenJMLCommands.CHECK_JML, "[\"\",\"" + jsonEscape(dirB.toString()) + "\"]");

        Set<String> withErrors = new HashSet<>();
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(TIMEOUT_SECONDS);
        while (withErrors.size() < 2) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) break;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) break;
            JsonObject p = msg.getAsJsonObject("params");
            String uri = p.get("uri").getAsString();
            if (p.getAsJsonArray("diagnostics").size() == 0) continue;
            if (uri.endsWith("BadA.java")) withErrors.add("BadA");
            if (uri.endsWith("BadB.java")) withErrors.add("BadB");
        }
        assertEquals("Files with diagnostics", Set.of("BadA", "BadB"), withErrors);
    }
}
