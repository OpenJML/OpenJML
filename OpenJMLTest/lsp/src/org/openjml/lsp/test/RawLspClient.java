package org.openjml.lsp.test;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;

/**
 * Minimal synchronous JSON-RPC client for LSP protocol testing.
 *
 * Instead of using LSP4J's client-side serialization (which fails in this JVM
 * environment because jdk.compiler bundles a reflection-disabled Gson), this
 * class writes and reads raw Content-Length-framed JSON messages.  This lets
 * tests exercise the server's full JSON-RPC receive / process / respond path
 * without depending on LSP4J's client-side Gson adapters.
 *
 * Notifications (method calls with no {@code id}) sent by the server are
 * queued and retrieved via {@link #nextNotification(String, long, TimeUnit)}.
 */
public class RawLspClient {

    private final OutputStream out;
    private final InputStream  in;
    private int nextId = 1;

    /** Queue of server-to-client notifications keyed by method. */
    private final BlockingQueue<JsonObject> notifications = new LinkedBlockingQueue<>();

    /** Background thread that reads server output and routes it. */
    private final Thread reader;
    private volatile boolean running = true;

    public RawLspClient(OutputStream serverInput, InputStream serverOutput) {
        this.out = serverInput;
        this.in  = serverOutput;

        reader = new Thread(() -> {
            while (running) {
                try {
                    String raw = readMessage();
                    if (raw == null) break;
                    JsonObject msg = JsonParser.parseString(raw).getAsJsonObject();
                    // Notifications have "method" but no "id"
                    if (msg.has("method") && !msg.has("id")) {
                        notifications.offer(msg);
                    }
                    // Responses (have "id") could be queued here if needed.
                } catch (IOException e) {
                    break;
                }
            }
        }, "RawLspClient-reader");
        reader.setDaemon(true);
        reader.start();
    }

    /**
     * Send a JSON-RPC request (with an auto-assigned id).
     *
     * @param method JSON-RPC method name
     * @param params params object as a raw JSON string, or {@code null}
     */
    public void sendRequest(String method, String params) throws IOException {
        int id = nextId++;
        String body = params == null
                ? "{\"jsonrpc\":\"2.0\",\"id\":" + id + ",\"method\":\"" + method + "\"}"
                : "{\"jsonrpc\":\"2.0\",\"id\":" + id + ",\"method\":\"" + method + "\",\"params\":" + params + "}";
        writeMessage(body);
    }

    /**
     * Send a JSON-RPC notification (no id, no response expected).
     *
     * @param method JSON-RPC method name
     * @param params params object as a raw JSON string, or {@code null}
     */
    public void sendNotification(String method, String params) throws IOException {
        String body = params == null
                ? "{\"jsonrpc\":\"2.0\",\"method\":\"" + method + "\"}"
                : "{\"jsonrpc\":\"2.0\",\"method\":\"" + method + "\",\"params\":" + params + "}";
        writeMessage(body);
    }

    /**
     * Wait for the next notification with the given method.
     *
     * Ignores notifications with other methods; retries until the matching
     * one arrives or the timeout expires.
     *
     * @return the full notification JSON object, or {@code null} on timeout
     */
    public JsonObject nextNotification(String method, long timeout, TimeUnit unit)
            throws InterruptedException {
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = notifications.poll(remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            if (method.equals(msg.get("method").getAsString())) return msg;
        }
    }

    public void stop() {
        running = false;
        reader.interrupt();
    }

    // --- framing ---

    private void writeMessage(String body) throws IOException {
        byte[] bytes = body.getBytes(StandardCharsets.UTF_8);
        String header = "Content-Length: " + bytes.length + "\r\n\r\n";
        synchronized (out) {
            out.write(header.getBytes(StandardCharsets.US_ASCII));
            out.write(bytes);
            out.flush();
        }
    }

    private String readMessage() throws IOException {
        // Read headers until blank line
        StringBuilder headerBuf = new StringBuilder();
        int contentLength = -1;
        while (true) {
            String line = readLine();
            if (line == null) return null;       // EOF
            if (line.isEmpty()) break;           // end of headers
            if (line.startsWith("Content-Length:")) {
                contentLength = Integer.parseInt(line.substring("Content-Length:".length()).trim());
            }
        }
        if (contentLength < 0) return null;

        // Read body
        byte[] buf = new byte[contentLength];
        int read = 0;
        while (read < contentLength) {
            int n = in.read(buf, read, contentLength - read);
            if (n < 0) return null;
            read += n;
        }
        return new String(buf, StandardCharsets.UTF_8);
    }

    /** Read a CRLF-terminated line from the input stream. Returns null on EOF. */
    private String readLine() throws IOException {
        StringBuilder sb = new StringBuilder();
        int prev = -1;
        while (true) {
            int b = in.read();
            if (b < 0) return sb.length() == 0 ? null : sb.toString();
            if (b == '\n' && prev == '\r') {
                // Remove trailing CR
                sb.setLength(sb.length() - 1);
                return sb.toString();
            }
            sb.append((char) b);
            prev = b;
        }
    }
}
