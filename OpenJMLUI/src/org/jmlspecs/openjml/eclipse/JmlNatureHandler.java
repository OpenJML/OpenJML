/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * Eclipse command handlers for adding and removing the OpenJML project nature.
 *
 * <p>Both handlers operate on the currently selected project(s) in any view
 * (Package Explorer, Project Explorer, Navigator, etc.).  They are registered
 * in {@code plugin.xml} via the {@code org.eclipse.ui.handlers} extension point.
 */
public class JmlNatureHandler {

    private JmlNatureHandler() {}

    // -----------------------------------------------------------------------
    // Helper: extract IProject from selection
    // -----------------------------------------------------------------------

    /**
     * Returns all distinct {@link IProject}s derivable from the selection,
     * one per selected element.  Returns an empty list if the selection is
     * empty or contains no recognisable project references.
     */
    private static List<IProject> projectsFromSelection(ISelection selection) {
        List<IProject> result = new ArrayList<>();
        if (!(selection instanceof IStructuredSelection ss)) return result;
        for (Object element : ss.toList()) {
            IProject p = projectFromElement(element);
            if (p != null && !result.contains(p)) result.add(p);
        }
        return result;
    }

    /** Derives an {@link IProject} from a single selection element, or {@code null}. */
    private static IProject projectFromElement(Object element) {
        if (element instanceof IProject p) return p;
        if (element instanceof IResource r) return r.getProject();
        if (element instanceof IAdaptable adaptable) {
            IProject p = adaptable.getAdapter(IProject.class);
            if (p != null) return p;
            IResource r = adaptable.getAdapter(IResource.class);
            if (r != null) return r.getProject();
        }
        return null;
    }

    // -----------------------------------------------------------------------
    // Shared helper
    // -----------------------------------------------------------------------

    /**
     * If the JML Decoration is currently disabled, shows a warning dialog
     * giving the user three choices:
     * <ul>
     *   <li><b>OK</b> — proceed without enabling the decoration</li>
     *   <li><b>Enable Decoration</b> — enable the decoration and proceed</li>
     *   <li><b>Cancel</b> — abort the nature change entirely</li>
     * </ul>
     *
     * @return {@code true} if the caller should proceed with the nature change,
     *         {@code false} if the user cancelled
     */
    private static boolean checkDecoratorAndPrompt(Shell shell) {
        var dm = PlatformUI.getWorkbench().getDecoratorManager();
        if (dm.getEnabled(OpenJMLConstants.DECORATOR_ID)) return true;

        MessageDialog dialog = new MessageDialog(
                shell,
                "JML Decoration Disabled",
                null,
                "The JML Decoration overlay is currently disabled in your Eclipse "
                + "preferences (Window > Preferences > General > Appearance > "
                + "Label Decorations).\n\n"
                + "Without it, JML-natured projects will not show the JML overlay "
                + "icon in the Package/Project Explorer.",
                MessageDialog.WARNING,
                new String[] { "OK", "Enable Decoration", "Cancel" },
                1);
        int choice = dialog.open();
        if (choice < 0 || choice == 2) return false;  // Cancel or dialog closed
        if (choice == 1) {  // Enable Decoration
            try {
                dm.setEnabled(OpenJMLConstants.DECORATOR_ID, true);
            } catch (CoreException e) {
                Console.errorlog("Failed to enable JML decoration: " + e.getMessage(), e);
            }
        }
        return true;
    }

    // -----------------------------------------------------------------------
    // Concrete handlers
    // -----------------------------------------------------------------------

    /**
     * Adds the OpenJML nature to the selected project(s).
     *
     * <p>Registered as the handler for {@code org.jmlspecs.openjml.commands.enableJmlNature}.
     */
    public static final class EnableJmlNature extends AbstractHandler {
        @Override
        public Object execute(ExecutionEvent event) throws ExecutionException {
            List<IProject> projects = projectsFromSelection(HandlerUtil.getCurrentSelection(event));
            if (projects.isEmpty()) {
                MessageDialog.openWarning(HandlerUtil.getActiveShell(event),
                        "OpenJML — No Project Selected",
                        "No project is selected.\n\nSelect a project in the Package Explorer or Project Explorer first.");
                return null;
            }
            if (!checkDecoratorAndPrompt(HandlerUtil.getActiveShell(event))) return null;
            for (IProject p : projects) JmlNature.enable(p);
            return null;
        }
    }

    /**
     * Removes the OpenJML nature from the selected project(s).
     *
     * <p>Registered as the handler for {@code org.jmlspecs.openjml.commands.disableJmlNature}.
     */
    public static final class DisableJmlNature extends AbstractHandler {
        @Override
        public Object execute(ExecutionEvent event) throws ExecutionException {
            List<IProject> projects = projectsFromSelection(HandlerUtil.getCurrentSelection(event));
            if (projects.isEmpty()) {
                MessageDialog.openWarning(HandlerUtil.getActiveShell(event),
                        "OpenJML — No Project Selected",
                        "No project is selected.\n\nSelect a project in the Package Explorer or Project Explorer first.");
                return null;
            }
            if (!checkDecoratorAndPrompt(HandlerUtil.getActiveShell(event))) return null;
            for (IProject p : projects) JmlNature.disable(p);
            return null;
        }
    }
}
