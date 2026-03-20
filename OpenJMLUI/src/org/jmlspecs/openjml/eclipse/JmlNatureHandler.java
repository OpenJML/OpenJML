/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
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
     * Returns the {@link IProject} for the first selected element, or
     * {@code null} if no project can be derived from the selection.
     */
    private static IProject projectFromSelection(ISelection selection) {
        if (!(selection instanceof IStructuredSelection ss)) return null;
        Object first = ss.getFirstElement();
        if (first == null) return null;

        // Direct IProject
        if (first instanceof IProject p) return p;

        // IResource (file, folder) → containing project
        if (first instanceof IResource r) return r.getProject();

        // IJavaProject and similar adaptable types
        if (first instanceof IAdaptable adaptable) {
            IProject p = adaptable.getAdapter(IProject.class);
            if (p != null) return p;
            IResource r = adaptable.getAdapter(IResource.class);
            if (r != null) return r.getProject();
        }
        return null;
    }

    // -----------------------------------------------------------------------
    // Concrete handlers
    // -----------------------------------------------------------------------

    /**
     * Adds the OpenJML nature to the selected project.
     *
     * <p>Registered as the handler for {@code org.jmlspecs.openjml.commands.enableJmlNature}.
     */
    public static final class EnableJmlNature extends AbstractHandler {
        @Override
        public Object execute(ExecutionEvent event) throws ExecutionException {
            IProject project = projectFromSelection(HandlerUtil.getCurrentSelection(event));
            if (project == null) {
                Console.log("[OpenJML] EnableJmlNature: no project in current selection.");
                return null;
            }
            JmlNature.enable(project);
            return null;
        }
    }

    /**
     * Removes the OpenJML nature from the selected project.
     *
     * <p>Registered as the handler for {@code org.jmlspecs.openjml.commands.disableJmlNature}.
     */
    public static final class DisableJmlNature extends AbstractHandler {
        @Override
        public Object execute(ExecutionEvent event) throws ExecutionException {
            IProject project = projectFromSelection(HandlerUtil.getCurrentSelection(event));
            if (project == null) {
                Console.log("[OpenJML] DisableJmlNature: no project in current selection.");
                return null;
            }
            JmlNature.disable(project);
            return null;
        }
    }
}
