package org.openjml.lsp;

import java.util.List;

/**
 * Parameters for the {@code $/openjml/actionMessage} custom notification.
 *
 * <p>This notification is sent from the server to capable clients as a richer
 * alternative to {@code window/logMessage}.  Capable clients (Eclipse, VS Code)
 * declare support via {@code supportsActionMessages: true} in
 * {@code initializationOptions}; the server then sends this notification instead
 * of {@code window/logMessage} for advisory and error messages.
 *
 * <p>Generic clients that do not declare the capability continue to receive
 * {@code window/logMessage} and are unaffected.
 *
 * <p>Clients that receive this notification should:
 * <ol>
 *   <li>Log {@link #message} to their output/console surface (using {@link #type}
 *       for severity-based coloring).</li>
 *   <li>If {@link #actions} is non-null and non-empty, show a dialog presenting
 *       each action as a button.  On click, execute the action's {@code kind}.</li>
 * </ol>
 *
 * <h2>Action kinds</h2>
 * <dl>
 *   <dt>{@code "openPreferences"}</dt>
 *   <dd>Open the client's preferences/settings UI, optionally navigated to the
 *       page identified by {@link ActionItem#target}:
 *       <ul>
 *         <li>{@code "settings"}    — top-level OpenJML settings page</li>
 *         <li>{@code "toolOptions"} — OpenJML tool options page (--warn, --esc flags, etc.)</li>
 *       </ul>
 *   </dd>
 *   <dt>{@code "dismiss"}</dt>
 *   <dd>No-op — the user acknowledged the message.  Always present in dialogs as
 *       the cancel / close button.</dd>
 * </dl>
 */
public class ActionMessageParams {

    /**
     * Message severity, using LSP {@code MessageType} integer values:
     * 1=Error, 2=Warning, 3=Info, 4=Log.
     */
    public int type;

    /** Human-readable message text. */
    public String message;

    /**
     * Optional list of actions to offer the user as dialog buttons.
     * {@code null} or empty means "log only, no dialog".
     */
    public List<ActionItem> actions;

    /** A single action button in the dialog. */
    public static class ActionItem {
        /**
         * Action kind — determines what happens when the button is clicked.
         * Known values: {@code "openPreferences"}, {@code "dismiss"}.
         */
        public String kind;

        /**
         * Kind-specific target, e.g. {@code "toolOptions"} or {@code "settings"}
         * for {@code openPreferences}.  May be {@code null} when not applicable.
         */
        public String target;

        /** Button label shown to the user. */
        public String title;
    }
}
