/*
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2006-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.JavaCore;
import org.jmlspecs.annotation.*;

/** This class implements the JML Nature that can be associated with Java Projects.
 *  The effects of this nature are to enable an additional decoration on Java
 *  Projects in the UI and to enable a Builder that will run JML tools as 
 *  part of the compilation cycle.
 */
public class JMLNature implements IProjectNature {

    /** The project to which this nature applies. */
    private IProject project;

    /** Creates a JML Builder in the project.  This is automatically called by
     * Eclipse when a project becomes a JML project.
     * @see org.eclipse.core.resources.IProjectNature#configure()
     */
    @Override
    public void configure() throws CoreException {
        // This code records whether the internal runtime library was automatically
        // configured into the project classpath. We remember what was done, so it 
        // can be undone on deconfiguring.
        if (Options.isOption(Options.useInternalRuntimeKey)) {
            Activator.utils().addRuntimeToProjectClasspath(JavaCore.create(project));
        }

        // Now add the JML builder

        IProjectDescription desc = project.getDescription();
        ICommand[] commands = desc.getBuildSpec();

        for (int i = 0; i < commands.length; ++i) {
            if (commands[i].getBuilderName().equals(Env.JML_BUILDER_ID)) {
                return; // There already is a JML Builder
            }
        }

        ICommand[] newCommands = new ICommand[commands.length + 1];
        System.arraycopy(commands, 0, newCommands, 0, commands.length);
        ICommand command = desc.newCommand();
        command.setBuilderName(Env.JML_BUILDER_ID);
        newCommands[newCommands.length - 1] = command;
        desc.setBuildSpec(newCommands);
        project.setDescription(desc, null);
    }

    /** Removes the JML Builder from the project if present.  This is
     * automatically called by Eclipse when a project's JML Nature is removed.
     * @see org.eclipse.core.resources.IProjectNature#deconfigure()
     */
    @Override
    public void deconfigure() throws CoreException {
        if (Options.isOption(Options.useInternalRuntimeKey)) {
            Activator.utils().removeFromClasspath(JavaCore.create(project),null);
        }
        IProjectDescription description = getProject().getDescription();
        ICommand[] commands = description.getBuildSpec();
        // Note: Only removes one instance - there should never be more than one.
        for (int i = 0; i < commands.length; ++i) {
            if (commands[i].getBuilderName().equals(Env.JML_BUILDER_ID)) {
                ICommand[] newCommands = new ICommand[commands.length - 1];
                System.arraycopy(commands, 0, newCommands, 0, i);
                System.arraycopy(commands, i + 1, newCommands, i,
                                        commands.length - i - 1);
                description.setBuildSpec(newCommands);
                return;
            }
        }
    }

    /* Returns the project associated with this instance of the JML Nature.
     * @see org.eclipse.core.resources.IProjectNature#getProject()
     */
    @Query @NonNull @Override
    public IProject getProject() {
        return project;
    }

    /* Sets the project associated with this instance of the JML Nature (called
     * by Eclipse and not by clients).
     * @see org.eclipse.core.resources.IProjectNature#setProject(org.eclipse.core.resources.IProject)
     */
    //@ ensures getProject() == project;
    @Override
    public void setProject(@NonNull IProject project) {
        this.project = project;
    }

    static public boolean isJMLNature(@NonNull IProject project) throws CoreException {
        IProjectDescription description = project.getDescription();
        String[] natures = description.getNatureIds();
        for (int i = 0; i < natures.length; ++i) {
            if (Env.JML_NATURE_ID.equals(natures[i])) {
                return true;
            }
        }
        return false;
    }

    static boolean autoEnable = false;
    
    static public void autoJMLEnable(@NonNull IProject project) {
        if (autoEnable) enableJMLNature(project, false);
    }

    static public void enableJMLNature(@NonNull IProject project) {
        enableJMLNature(project, true);
    }

    /**
     * Enables the JML nature on a project
     * @param project project to have nature enabled
     */
    static public void enableJMLNature(@NonNull IProject project, boolean warn) {
        try {
            if (Options.uiverboseness) Log.log("Enabling JML nature for project " + project.getName()); //$NON-NLS-1$
            IProjectDescription description = project.getDescription();
            String[] natures = description.getNatureIds();

            boolean hasJava = false;
            for (int i = 0; i < natures.length; ++i) {
                if (Env.JML_NATURE_ID.equals(natures[i])) {
                    if (warn && Options.uiverboseness) Log.log("JML Nature already present in " + project.getName()); //$NON-NLS-1$
                    return;
                }
                if (Env.JAVA_NATURE_ID.equals(natures[i])) hasJava = true;
            }
            if (!hasJava) {
                if (Options.uiverboseness) Log.log("Non-Java project: " + project.getName()); //$NON-NLS-1$
                return; // Was not a Java project after all
            } else {
                if (warn && Options.uiverboseness) Log.log("JML Nature already present in " + project.getName()); //$NON-NLS-1$
            }

            // Add the nature
            String[] newNatures = new String[natures.length + 1];
            System.arraycopy(natures, 0, newNatures, 0, natures.length);
            newNatures[natures.length] = Env.JML_NATURE_ID;
            description.setNatureIds(newNatures);
            project.setDescription(description, null);
            if (Options.uiverboseness) Log.log("JML Nature added to " + project.getName()); //$NON-NLS-1$

        } catch (CoreException e) {
            Log.errorKey("openjml.ui.failed.to.enable.jml", e, project.getProject()); //$NON-NLS-1$
        }
    }

    /**
     * Disables the JML nature on a project
     * @param project project to have nature disabled
     */
    static public void disableJMLNature(@NonNull IProject project) {
        try {
            if (Options.uiverboseness) Log.log("Disabling nature on project " + project.getName()); //$NON-NLS-1$
            IProjectDescription description = project.getDescription();
            String[] natures = description.getNatureIds();

            // Note: Presumes the Nature is present at most once.
            for (int i = 0; i < natures.length; ++i) {
                if (Env.JML_NATURE_ID.equals(natures[i])) {
                    // Remove the nature
                    String[] newNatures = new String[natures.length - 1];
                    System.arraycopy(natures, 0, newNatures, 0, i);
                    System.arraycopy(natures, i + 1, newNatures, i,
                                            natures.length - i - 1);
                    description.setNatureIds(newNatures);
                    project.setDescription(description, null);

                    if (Options.uiverboseness) Log.log("JML Nature removed from " + project.getName()); //$NON-NLS-1$
                    return;
                }
            }
            if (Options.uiverboseness) Log.log("JML Nature not present in " + project.getName()); //$NON-NLS-1$

        } catch (CoreException e) {
            Log.errorKey("openjml.ui.failed.to.disable.jml", e, project.getProject()); //$NON-NLS-1$
        }
    }
}
