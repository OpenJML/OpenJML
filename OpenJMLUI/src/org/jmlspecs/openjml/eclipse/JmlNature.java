/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.lsp4e.LanguageServers;
import org.eclipse.lsp4j.ExecuteCommandParams;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PlatformUI;

/**
 * Eclipse project nature that marks a project as an OpenJML project.
 *
 * <p>Adding this nature to a project opts it in to OpenJML checking:
 * the LSP server is notified of the updated project list, and all ESC/RAC
 * commands check for this nature before forwarding requests to the server.
 *
 * <p>This is a marker nature only — no incremental builder is attached.
 * All checking is driven on demand via the OpenJML LSP server.
 *
 * <p>The nature ID is {@value #NATURE_ID}.
 */
public class JmlNature implements IProjectNature {

    /** The Eclipse nature ID for OpenJML projects. */
    public static final String NATURE_ID = "org.openjml.OpenJMLUI.JMLNatureID";

    /** The Eclipse Java nature ID — required before JML nature can be added. */
    private static final String JAVA_NATURE_ID = "org.eclipse.jdt.core.javanature";

    private IProject project;

    // -----------------------------------------------------------------------
    // IProjectNature implementation
    // -----------------------------------------------------------------------

    @Override
    public void configure() throws CoreException {
        // Marker nature — nothing extra to configure.
    }

    @Override
    public void deconfigure() throws CoreException {
        // Marker nature — nothing extra to deconfigure.
    }

    @Override
    public IProject getProject() {
        return project;
    }

    @Override
    public void setProject(IProject project) {
        this.project = project;
    }

    // -----------------------------------------------------------------------
    // Static helpers
    // -----------------------------------------------------------------------

    /**
     * Returns {@code true} if {@code project} has the OpenJML nature.
     */
    public static boolean hasNature(IProject project) {
        if (project == null || !project.isOpen()) return false;
        try {
            return project.hasNature(NATURE_ID);
        } catch (CoreException e) {
            Console.log("[OpenJML] hasNature check failed for " + project.getName() + ": " + e);
            return false;
        }
    }

    /**
     * Refreshes the JML decorator in the Package/Project Explorer so the
     * overlay icon appears or disappears immediately after a nature change,
     * without requiring a manual F5 refresh.
     */
    private static void refreshDecorator() {
        Display.getDefault().asyncExec(() -> {
            if (PlatformUI.isWorkbenchRunning()) {
                PlatformUI.getWorkbench().getDecoratorManager()
                        .update("org.openjml.OpenJMLUI.JMLDecoration");
            }
        });
    }

    /**
     * Adds the OpenJML nature to {@code project}.
     *
     * <p>Does nothing if the project is not a Java project or already has the nature.
     */
    public static void enable(IProject project) {
        if (project == null || !project.isOpen()) return;
        try {
            if (!project.hasNature(JAVA_NATURE_ID)) {
                Console.log("[OpenJML] Cannot add JML nature: " + project.getName()
                        + " is not a Java project.");
                return;
            }
            if (project.hasNature(NATURE_ID)) return; // already present

            IProjectDescription desc = project.getDescription();
            String[] natures = desc.getNatureIds();
            String[] newNatures = new String[natures.length + 1];
            System.arraycopy(natures, 0, newNatures, 0, natures.length);
            newNatures[natures.length] = NATURE_ID;
            desc.setNatureIds(newNatures);
            project.setDescription(desc, null);
            Console.log("[OpenJML] JML nature added to " + project.getName());
            refreshDecorator();
        } catch (CoreException e) {
            Console.log("[OpenJML] Failed to enable JML nature on " + project.getName() + ": " + e);
        }
    }

    /**
     * Removes the OpenJML nature from {@code project}.
     *
     * <p>Does nothing if the project does not have the nature.
     */
    public static void disable(IProject project) {
        if (project == null || !project.isOpen()) return;
        try {
            if (!project.hasNature(NATURE_ID)) return; // not present

            IProjectDescription desc = project.getDescription();
            String[] natures = desc.getNatureIds();
            int idx = -1;
            for (int i = 0; i < natures.length; i++) {
                if (NATURE_ID.equals(natures[i])) { idx = i; break; }
            }
            if (idx < 0) return;

            String[] newNatures = new String[natures.length - 1];
            System.arraycopy(natures, 0, newNatures, 0, idx);
            System.arraycopy(natures, idx + 1, newNatures, idx, natures.length - idx - 1);
            desc.setNatureIds(newNatures);
            project.setDescription(desc, null);
            Console.log("[OpenJML] JML nature removed from " + project.getName());
            refreshDecorator();
            cleanupForProject(project);
        } catch (CoreException e) {
            Console.log("[OpenJML] Failed to disable JML nature on " + project.getName() + ": " + e);
        }
    }

    private static final String LSP4E_MARKER = "org.eclipse.lsp4e.diagnostic";
    private static final String SERVER_ID    = "org.jmlspecs.openjml.lsp.server";

    /**
     * Cleans up all Eclipse-side and server-side state for {@code project}
     * after its JML nature has been removed:
     * <ul>
     *   <li>Deletes all OpenJML markers on the project.</li>
     *   <li>Disposes JML folding managers for any open editors in the project.</li>
     *   <li>Sends {@code openjml.clearAndReindex} to the server so it discards
     *       cached data and rebuilds its workspace index.</li>
     * </ul>
     */
    private static void cleanupForProject(IProject project) {
        // 1. Delete all OpenJML markers on this project.
        try {
            IMarker[] markers = project.findMarkers(
                    LSP4E_MARKER, /*includeSubtypes=*/ false, IResource.DEPTH_INFINITE);
            for (IMarker m : markers) {
                if (SERVER_ID.equals(m.getAttribute("languageServerId"))) {
                    m.delete();
                }
            }
        } catch (CoreException e) {
            Console.log("[OpenJML] Warning: could not clear markers for "
                    + project.getName() + ": " + e.getMessage());
        }

        // 2. Dispose folding managers for any open editors in this project.
        LspPartListener.disposeFoldingManagersForProject(project);

        // 3. Tell the server to clear its caches and reindex.
        ExecuteCommandParams p = new ExecuteCommandParams(
                "openjml.clearAndReindex", List.of());
        LanguageServers.forProject(project).computeFirst(
                server -> server.getWorkspaceService().executeCommand(p));
    }
}
