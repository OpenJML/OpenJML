package org.jmlspecs.openjml.eclipse.uitest;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable;
import org.jmlspecs.openjml.eclipse.OpenJMLResourceChangeListener;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.FixMethodOrder;
import org.junit.Test;
import org.junit.runners.MethodSorters;

/**
 * When the "OpenJML Configuration Changed" dialog opens: not for a JML project that is
 * imported, but for a JML-relevant change to an existing project.
 */
@FixMethodOrder(MethodSorters.NAME_ASCENDING)
public class ConfigChangeDialogTest extends GUITestBase {

    private static final String DIALOG_TITLE = "OpenJML Configuration Changed";
    private static final String PREF_NODE = "org.openjml.OpenJMLUI";

    @BeforeClass
    public static void alwaysAsk() {
        InstanceScope.INSTANCE.getNode(PREF_NODE).put(
                OpenJMLResourceChangeListener.PREF_CONFIG_CHANGE_ACTION, "");
    }

    @AfterClass
    public static void restorePreferenceAndDeleteProjects() throws CoreException {
        InstanceScope.INSTANCE.getNode(PREF_NODE).put(
                OpenJMLResourceChangeListener.PREF_CONFIG_CHANGE_ACTION, "Do nothing");
        for (String name : new String[] { "CfgImported", "CfgNatureAdded" }) {
            IProject p = ResourcesPlugin.getWorkspace().getRoot().getProject(name);
            if (p.exists()) p.delete(true, true, null);
        }
    }

    /** Importing an existing JML project (as File > Import does) is not a configuration change. */
    @Test
    public void t1_importedJmlProjectShowsNoDialog() throws Exception {
        IWorkspace ws = ResourcesPlugin.getWorkspace();
        Path dir = ws.getRoot().getLocation().toFile().toPath().resolve("CfgImported");
        Files.createDirectories(dir.resolve("src"));
        write(dir.resolve(".project"), """
                <?xml version="1.0" encoding="UTF-8"?>
                <projectDescription>
                  <name>CfgImported</name>
                  <comment></comment>
                  <projects></projects>
                  <buildSpec>
                    <buildCommand><name>org.eclipse.jdt.core.javabuilder</name><arguments></arguments></buildCommand>
                  </buildSpec>
                  <natures>
                    <nature>org.eclipse.jdt.core.javanature</nature>
                    <nature>org.openjml.OpenJMLUI.JMLNatureID</nature>
                  </natures>
                </projectDescription>
                """);
        write(dir.resolve(".classpath"), """
                <?xml version="1.0" encoding="UTF-8"?>
                <classpath>
                  <classpathentry kind="src" path="src"/>
                  <classpathentry kind="con" path="org.eclipse.jdt.launching.JRE_CONTAINER"/>
                  <classpathentry kind="output" path="bin"/>
                </classpath>
                """);
        IProject project = ws.getRoot().getProject("CfgImported");
        IProjectDescription desc = ws.loadProjectDescription(
                new org.eclipse.core.runtime.Path(dir.resolve(".project").toString()));
        ws.run(monitor -> {
            project.create(desc, monitor);
            project.open(monitor);
        }, null);
        waitForBuild();
        assertFalse("dialog opened for an imported JML project", dialogOpens());
    }

    /** Positive control: adding the JML nature outside OpenJML's menu asks. */
    @Test
    public void t2_natureAddedExternallyShowsDialog() throws Exception {
        IProject project = createJavaProject("CfgNatureAdded");
        waitForBuild();
        IProjectDescription desc = project.getDescription();
        desc.setNatureIds(new String[] { JavaCore.NATURE_ID, JML_NATURE_ID });
        project.setDescription(desc, null);
        assertTrue("no dialog when the JML nature was added externally", dialogOpens());
    }

    private static void write(Path p, String text) throws IOException {
        Files.writeString(p, text, StandardCharsets.UTF_8);
    }

    /**
     * Whether the dialog opens within 3 s (the listener debounces for 0.5 s); if it does,
     * presses "Do nothing" without remembering the choice.
     */
    private static boolean dialogOpens() {
        long deadline = System.currentTimeMillis() + 3_000;
        while (System.currentTimeMillis() < deadline) {
            Boolean found = UIThreadRunnable.syncExec(() -> {
                for (Shell sh : Display.getDefault().getShells()) {
                    if (sh.isVisible() && DIALOG_TITLE.equals(sh.getText())) {
                        Button b = findButton(sh, "Do nothing");
                        if (b != null) {
                            b.notifyListeners(org.eclipse.swt.SWT.Selection, new org.eclipse.swt.widgets.Event());
                        } else {
                            sh.close();
                        }
                        return true;
                    }
                }
                return false;
            });
            if (found) return true;
            bot.sleep(200);
        }
        return false;
    }

    private static Button findButton(Composite parent, String text) {
        for (Control c : parent.getChildren()) {
            if (c instanceof Button b && text.equals(b.getText().replace("&", ""))) return b;
            if (c instanceof Composite comp) {
                Button r = findButton(comp, text);
                if (r != null) return r;
            }
        }
        return null;
    }
}
