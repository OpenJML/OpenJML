package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;
import org.jmlspecs.annotations.*;

/** This class implements the JML Nature that can be associated with Java Projects.
 *  The effects of this nature are to enable an additional decoration on Java
 *  Projects in the UI and to enable a Builder that will run JML tools as 
 *  part of the compilation cycle.
 */
public class JMLNature implements IProjectNature {

  /**
   * ID of this project nature
   */
  public static final String JML_NATURE_ID = Activator.PLUGIN_ID + ".JMLNatureID";

  /** The ID of the Java nature */
  public static final String JAVA_NATURE_ID = "org.eclipse.jdt.core.javanature";

  /** The project to which this nature applies. */
  private IProject project;

  /** Creates a JML Builder in the project.  This is automatically called by
   * Eclipse when a project becomes a JML project.
   * @see org.eclipse.core.resources.IProjectNature#configure()
   */
  public void configure() throws CoreException {
    IProjectDescription desc = project.getDescription();
    ICommand[] commands = desc.getBuildSpec();

    for (int i = 0; i < commands.length; ++i) {
      if (commands[i].getBuilderName().equals(JMLBuilder.JML_BUILDER_ID)) {
        return;
      }
    }

    ICommand[] newCommands = new ICommand[commands.length + 1];
    System.arraycopy(commands, 0, newCommands, 0, commands.length);
    ICommand command = desc.newCommand();
    command.setBuilderName(JMLBuilder.JML_BUILDER_ID);
    newCommands[newCommands.length - 1] = command;
    desc.setBuildSpec(newCommands);
    project.setDescription(desc, null);
  }

  /* Removes the JML BUilder from the project.  This is automatically called
   * by Eclipse when a project's JML Nasture is removed.
   * @see org.eclipse.core.resources.IProjectNature#deconfigure()
   */
  public void deconfigure() throws CoreException {
    IProjectDescription description = getProject().getDescription();
    ICommand[] commands = description.getBuildSpec();
    for (int i = 0; i < commands.length; ++i) {
      if (commands[i].getBuilderName().equals(JMLBuilder.JML_BUILDER_ID)) {
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
  @Query @NonNull
  public IProject getProject() {
    return project;
  }

  /* Sets the project associated with this instaqnce of the JML Nature
   * @see org.eclipse.core.resources.IProjectNature#setProject(org.eclipse.core.resources.IProject)
   */
  //@ ensures getProjecdt() == project;
  public void setProject(@NonNull IProject project) {
    this.project = project;
  }

  /**
   * Enables the JML nature on a project
   * @param project project to have nature enabled
   */
  static public void enableJMLNature(IProject project) {
    try {
      Log.log("Enabling JML nature for project " + project.getName());
      IProjectDescription description = project.getDescription();
      String[] natures = description.getNatureIds();

      boolean hasJava = false;
      for (int i = 0; i < natures.length; ++i) {
        if (JML_NATURE_ID.equals(natures[i])) {
          Log.log("JML Nature already present in " + project.getName());
          return;
        }
        if (JAVA_NATURE_ID.equals(natures[i])) hasJava = true;
      }
      if (!hasJava) Log.log("Unexpected non-Java project: " + project.getName());
      if (!hasJava) return; // Was not a Java project after all
      
      // Add the nature
      String[] newNatures = new String[natures.length + 1];
      System.arraycopy(natures, 0, newNatures, 0, natures.length);
      newNatures[natures.length] = JML_NATURE_ID;
      description.setNatureIds(newNatures);
      project.setDescription(description, null);
      Log.log("JML Nature added to " + project.getName());

    } catch (CoreException e) {
      Log.errorlog("Failed to enable JML nature for " + project.getProject(), e);
    }
  }

  /**
   * Disables the JML nature on a project
   * @param project project to have nature disabled
   */
  static public void disableJMLNature(IProject project) {
    try {
      Log.log("Disabling nature on project " + project.getName());
      IProjectDescription description = project.getDescription();
      String[] natures = description.getNatureIds();

      for (int i = 0; i < natures.length; ++i) {
        //Log.log("   Nature " + natures[i]);
        if (JML_NATURE_ID.equals(natures[i])) {
          // Remove the nature
          String[] newNatures = new String[natures.length - 1];
          System.arraycopy(natures, 0, newNatures, 0, i);
          System.arraycopy(natures, i + 1, newNatures, i,
                  natures.length - i - 1);
          description.setNatureIds(newNatures);
          project.setDescription(description, null);
          //project.deleteMarkers(Utils.JML_MARKER_ID, false, IResource.DEPTH_INFINITE);

          Log.log("JML Nature removed from " + project.getName());
          return;
        }
      }
      Log.log("JML Nature not present in " + project.getName());

    } catch (CoreException e) {
      Log.errorlog("Failed to change JML nature for " + project.getProject(), e);
    }
  }
}
