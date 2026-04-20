package org.openjml.lsp;

import com.google.gson.JsonPrimitive;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Maps LSP {@code workspace/executeCommand} command names to their handlers.
 *
 * <p>Registration helpers extract arguments from the raw {@code List<?>} and
 * call back into typed lambdas, hiding the Gson {@link JsonPrimitive} unwrapping.
 */
public final class CommandRegistry {

    /** Generic handler: receives the raw args list, returns a result (or {@code null}). */
    @FunctionalInterface
    public interface Handler {
        Object handle(List<?> args);
    }

    private final Map<String, Handler> map = new LinkedHashMap<>();

    /** Register {@code name} → {@code handler}.  Silently ignored when {@code name} is null/empty. */
    public void on(String name, Handler handler) {
        if (name != null && !name.isEmpty()) map.put(name, handler);
    }

    /** Command with a single URI arg: {@code action.accept(uri)}. */
    public void onUri(String name, Consumer<String> action) {
        on(name, args -> {
            String uri = str(args, 0);
            if (uri != null) action.accept(uri);
            return null;
        });
    }

    /** Command with URI + optional second string arg (e.g. method name or output dir). */
    public void onUriStr(String name, BiConsumer<String, String> action) {
        on(name, args -> {
            String uri = str(args, 0);
            if (uri != null) action.accept(uri, str(args, 1));  // second arg may be null
            return null;
        });
    }

    /** Command whose args are all treated as a list of strings (e.g. path list). */
    public void onStringList(String name, Consumer<List<String>> action) {
        on(name, args -> {
            if (args != null && !args.isEmpty()) {
                List<String> paths = args.stream()
                        .map(CommandRegistry::extractString)
                        .filter(s -> s != null && !s.isEmpty())
                        .collect(Collectors.toList());
                if (!paths.isEmpty()) action.accept(paths);
            }
            return null;
        });
    }

    /** No-argument command. */
    public void onNoArgs(String name, Runnable action) {
        on(name, args -> { action.run(); return null; });
    }

    /**
     * Command with a single URI arg whose result is returned to the client.
     * Use this for request/response commands like {@code getSemanticTokens}.
     */
    public void onUriReturn(String name, Function<String, Object> fn) {
        on(name, args -> {
            String uri = str(args, 0);
            return uri != null ? fn.apply(uri) : null;
        });
    }

    /**
     * Returns the names of all registered commands, in registration order.
     * Used by {@link OpenJMLLanguageServer} to populate {@code executeCommandProvider}
     * in the LSP {@code initialize} response.
     */
    public List<String> commandNames() {
        return new java.util.ArrayList<>(map.keySet());
    }

    /**
     * Dispatch {@code cmd} to the registered handler.
     *
     * @return the handler's return value, or {@code null} if no handler is registered
     */
    Object dispatch(String cmd, List<?> args) {
        Handler h = map.get(cmd);
        return h != null ? h.handle(args != null ? args : List.of()) : null;
    }

    // -----------------------------------------------------------------------
    // Argument extraction helpers
    // -----------------------------------------------------------------------

    /** Extract the string at {@code index} from {@code args}, or {@code null}. */
    private static String str(List<?> args, int index) {
        return (args != null && args.size() > index) ? extractString(args.get(index)) : null;
    }

    /** Unwrap a Gson {@link JsonPrimitive} or fall back to {@link String#valueOf}. */
    static String extractString(Object arg) {
        if (arg instanceof JsonPrimitive jp) return jp.getAsString();
        if (arg != null) return String.valueOf(arg);
        return null;
    }
}
