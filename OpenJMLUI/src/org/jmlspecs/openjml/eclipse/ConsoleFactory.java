package org.jmlspecs.openjml.eclipse;

import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleFactory;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;

public class ConsoleFactory implements IConsoleFactory {

    /** The name to use to identify the JML Console */
    public final static /* @ non_null */ String consoleName = Messages.OpenJMLUI_Activator_JmlConsoleTitle;

    /** The Factory method invoked by Eclipse when asked to create a new console */
    @Override
    public void openConsole() {
        /* @ non_null */ IConsoleManager consoleManager = ConsolePlugin.getDefault().getConsoleManager();
        /* @ non_null */ MessageConsole console = getJMLConsole(true);

    }

    /** Returns the JML Console, creating it if necessary; 'show's it if the argument is true. */
    public static /* @ non_null */ MessageConsole getJMLConsole(boolean show) {
        MessageConsole console = null;
        IConsoleManager consoleManager = ConsolePlugin.getDefault().getConsoleManager();
        IConsole[] existing = consoleManager.getConsoles();
        for (int i = 0; i < existing.length; ++i) {
            if (existing[i].getName().equals(consoleName)) {
                console = (MessageConsole) existing[i];
                break;
            }
        }
        if (console == null) {
            console = new MessageConsole(consoleName, null);
            consoleManager.addConsoles(new IConsole[] { console });
        }
        if (show)
            consoleManager.showConsoleView(console);

        // cap it at 10M
        console.setWaterMarks(10000, 10000000);
        return console;
    }
}