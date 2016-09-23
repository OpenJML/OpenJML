package org.jmlspecs.openjml.jmldoc;

import org.jmlspecs.openjml.JmlOption;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javadoc.Start;

/**
 * This class is an alternate class to initiate the standard doclet. It simply
 * provides additional usage information for the command-line options. It 
 * also specifies an alternate doclet to use.
 * 
 * @author David R. Cok
 */
public class JmlStart extends Start {

    /** This constructor names the application; by default it uses the
     * standard doclet.
     * @param name name of application
     */
    public JmlStart(String name, Context context) {
        super(name,"org.jmlspecs.openjml.jmldoc.HtmlJmlDoclet");
        this.context = context;
    }
    
    /** Overrides the usage method to add information about jmldoc-specific options */
    protected void usage() {
        super.usage();
        JmlOption[] addedOptions = { 
                JmlOption.SPECS, 
                JmlOption.INTERNALSPECS, 
                JmlOption.INTERNALRUNTIME, 
                JmlOption.CHECKSPECSPATH, 
                JmlOption.DIRS,
                JmlOption.DIR,
//                JmlOptionName.ENDOPTIONS  // FIXME - implement this or not?
                };
        System.out.println();
        System.out.println("JMLDoc options:");
        String spaces = "                                  ";
        for (JmlOption n : addedOptions) {
            System.out.println(n.optionName() + 
                    spaces.substring(n.optionName().length()) + n.help());
        }
    }
}
