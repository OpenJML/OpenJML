/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IWorkingSet;

/**
 * Resolves the set of targets for an OpenJML command from the current workbench
 * selection, with a fallback to the active editor.
 *
 * <p>A {@link Target} is one of:
 * <ul>
 *   <li>{@link Target.File} — a single Java source file</li>
 *   <li>{@link Target.Method} — a specific method within a file</li>
 *   <li>{@link Target.Dir} — a container (project, package, folder) whose
 *       directory path is passed directly to the OpenJML server via {@code --dirs}</li>
 * </ul>
 *
 * <p>Containers are <em>not</em> expanded recursively to their member files;
 * instead they become {@link Target.Dir} entries so the server can handle
 * directory-level operations efficiently.
 *
 * <p>Resolution order:
 * <ol>
 *   <li>Non-empty {@link IStructuredSelection} — each element is converted to
 *       the most specific target type.</li>
 *   <li>Empty selection — falls back to the file open in the active editor.</li>
 * </ol>
 */
public class SelectionResolver {

    private SelectionResolver() {}

    // -----------------------------------------------------------------------
    // Target type
    // -----------------------------------------------------------------------

    /**
     * A resolution target for an OpenJML command.
     */
    public sealed interface Target permits Target.File, Target.Method, Target.Dir {

        /** A single Java source file. */
        record File(IFile file) implements Target {}

        /**
         * A specific method within a source file.
         *
         * @param file      the source file containing the method
         * @param methodFqn fully-qualified name, e.g. {@code com.example.Foo.bar}
         */
        record Method(IFile file, String methodFqn) implements Target {}

        /**
         * A container (project, package, or folder).
         * The directory's OS path is passed to the server via {@code --dirs}.
         */
        record Dir(IContainer container) implements Target {}
    }

    // -----------------------------------------------------------------------
    // Public API
    // -----------------------------------------------------------------------

    /**
     * Resolve targets from {@code selection}, falling back to the active
     * {@code editor} when the selection is empty or contains no targets.
     *
     * @param selection   the current workbench selection (may be {@code null})
     * @param editor      the currently active editor (may be {@code null})
     * @return a non-null, possibly-empty list of resolved targets
     */
    public static List<Target> resolve(ISelection selection, IEditorPart editor) {
        List<Target> result = new ArrayList<>();

        if (selection instanceof IStructuredSelection ss && !ss.isEmpty()) {
            for (Object element : ss.toList()) {
                collectTarget(element, result);
            }
        }

        // Fall back to the active editor.
        if (result.isEmpty() && editor != null
                && editor.getEditorInput() instanceof IFileEditorInput fi) {
            result.add(new Target.File(fi.getFile()));
        }

        return result;
    }

    // -----------------------------------------------------------------------
    // Internal helpers
    // -----------------------------------------------------------------------

    private static void collectTarget(Object element, List<Target> result) {
        if (element instanceof IMethod m) {
            // Method selected (e.g. in Outline) — method-level target.
            IResource r = m.getResource();
            if (r instanceof IFile f) {
                result.add(new Target.Method(f, buildFqn(m)));
            }
        } else if (element instanceof IFile f) {
            result.add(new Target.File(f));
        } else if (element instanceof IWorkingSet ws) {
            for (IAdaptable a : ws.getElements()) {
                collectTarget(a, result);
            }
        } else if (element instanceof IJavaElement je) {
            // Other Java element (package, compilation unit, class, …).
            IResource r = je.getResource();
            if (r instanceof IFile f) {
                result.add(new Target.File(f));
            } else if (r instanceof IContainer c) {
                result.add(new Target.Dir(c));
            }
        } else if (element instanceof IProject p) {
            result.add(new Target.Dir(p));
        } else if (element instanceof IContainer c) {
            result.add(new Target.Dir(c));
        } else if (element instanceof IAdaptable a) {
            IResource r = a.getAdapter(IResource.class);
            if (r instanceof IFile f) {
                result.add(new Target.File(f));
            } else if (r instanceof IContainer c) {
                result.add(new Target.Dir(c));
            }
        }
    }

    /**
     * Build the fully-qualified method name {@code pkg.ClassName.methodName}
     * from a JDT {@link IMethod}.
     */
    private static String buildFqn(IMethod method) {
        IType type = method.getDeclaringType();
        if (type == null) return method.getElementName();
        return type.getFullyQualifiedName('.') + "." + method.getElementName();
    }
}
