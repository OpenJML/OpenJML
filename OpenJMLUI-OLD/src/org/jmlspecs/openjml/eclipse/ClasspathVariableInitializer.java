package org.jmlspecs.openjml.eclipse;

import java.io.File;
import java.io.IOException;
import java.net.URL;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.jmlspecs.openjml.Strings;
import org.osgi.framework.Bundle;

/** Defines how a plugin-defined classpath variable is defined and initialized.
 * The name of this class is used in plugin.xml.
 * @author dcok
 *
 */
public class ClasspathVariableInitializer extends org.eclipse.jdt.core.ClasspathVariableInitializer {

    /** Name of the built-in environment variable defined to hold the location of
     * the plug-in in current use. This works for both debug operation and 
     * conventional installations. This name must agree with the name used in
     * plugin.xml. 
     */
    public static final String OPENJML_VAR = "OPENJML_PLUGIN";

    /** Name of the built-in environment variable defined to hold the location of
     * the runtime library. This works for both debug operation and 
     * conventional installations. This name must agree with the name used in
     * plugin.xml. 
     */
    public static final String OPENJML_RUNTIME_LIBRARY = "OPENJML_RUNTIME_LIBRARY";

    /** Defines and initializes the OpenJML environment variable. This method
     * is required by Eclipse.
     */
    @Override
    public void initialize(String variable) {
        try {
            Bundle bundle = Platform.getBundle(Env.PLUGIN_ID);
            if (bundle == null) {
                Log.errorKey("openjml.ui.failed.to.define.classpath.variable", null); //$NON-NLS-1$
                return;
            }
            URL url = bundle.getEntry("/"); // root of plugin  //$NON-NLS-1$
            URL local = FileLocator.toFileURL(url);
            String fullPath = new File(local.getPath()).getCanonicalPath();
            if (fullPath == null) {
                Log.errorKey("openjml.ui.failed.to.define.classpath.variable", null); //$NON-NLS-1$
                return;
            }
            JavaCore.setClasspathVariable(OPENJML_VAR, new Path(fullPath), null);

            url = bundle.getEntry(Strings.runtimeJarName); // root of plugin 
            local = FileLocator.toFileURL(url);
            fullPath = new File(local.getPath()).getCanonicalPath();
            if (fullPath == null) {
                Log.errorKey("openjml.ui.failed.to.define.classpath.variable", null); //$NON-NLS-1$
                return;
            }
            JavaCore.setClasspathVariable(OPENJML_RUNTIME_LIBRARY, new Path(fullPath), null);

        } catch (JavaModelException e) {
            Log.errorKey("openjml.ui.failed.to.set.classpath.variable",e); //$NON-NLS-1$
        } catch (IOException e) {
            Log.errorKey("openjml.ui.failed.to.define.classpath.variable", e); //$NON-NLS-1$
        }
    }

}
