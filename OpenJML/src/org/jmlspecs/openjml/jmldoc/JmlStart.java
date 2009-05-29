package org.jmlspecs.openjml.jmldoc;

import org.jmlspecs.openjml.JmlOptionName;

import com.sun.tools.javadoc.Start;

/**
 * This class is an alternate class to initiate the standard doclet. It simply
 * provides additional usage information for the command-line options. (It could
 * also specify an alternate doclet to use.)
 * 
 * @author David R. Cok
 */
public class JmlStart extends Start {

    /** This constructor names the application; by default it uses the
     * standard doclet.
     * @param name name of application
     */
    public JmlStart(String name) {
        super(name,"org.jmlspecs.openjml.jmldoc.HtmlJmlDoclet");  // If a different doclet is to be used, name it here with another argument
    }
    
    /** Overrides the usage method to add information about jmldoc-specific options */
    protected void usage() {
        super.usage();
        JmlOptionName[] addedOptions = { 
                JmlOptionName.SPECS, 
                JmlOptionName.NOINTERNALSPECS, 
                JmlOptionName.NOINTERNALRUNTIME, 
                JmlOptionName.NOCHECKSPECSPATH 
                };
        System.out.println();
        System.out.println("JMLDoc options:");
        String spaces = "                                  ";
        for (JmlOptionName n : addedOptions) {
            System.out.println(n.optionName() + 
                    spaces.substring(n.optionName().length()) + n.help());
        }
    }
}
