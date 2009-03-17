package org.jmlspecs.openjml.jmldoc;

import com.sun.javadoc.DocErrorReporter;
import com.sun.javadoc.LanguageVersion;
import com.sun.javadoc.RootDoc;
import com.sun.tools.doclets.formats.html.HtmlDoclet;

/** This class is the doclet that is the standard Javadoc doclet enhanced to
 * write JML information
 * 
 * @author David Cok
 *
 */
public class StandardJml {

    // FIXME - not sure why we need this - we would need it if there were instance
    // methods of HtmlDoclet that we needed to call
    public static final HtmlDoclet htmlDoclet = new HtmlJmlDoclet();

    public static int optionLength(String option) {
        return HtmlJmlDoclet.optionLength(option);
    }

    public static boolean start(RootDoc root) {
        return HtmlJmlDoclet.start(root);
    }

    public static boolean validOptions(String[][] options,
                                   DocErrorReporter reporter) {
        return HtmlJmlDoclet.validOptions(options, reporter);
    }

    public static LanguageVersion languageVersion() {
        return HtmlJmlDoclet.languageVersion();
    }

}
