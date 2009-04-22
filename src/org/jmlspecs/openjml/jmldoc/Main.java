package org.jmlspecs.openjml.jmldoc;

import java.io.PrintWriter;
import java.util.LinkedList;

import org.jmlspecs.annotations.NonNull;
import org.jmlspecs.openjml.JmlOptionName;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javadoc.Start;

/** This is the class containing the entry points for the jmldoc tool. 
 * See the material in the <A HREF="package-summary.html">package description</A> for use and design discussion. */
public class Main extends org.jmlspecs.openjml.Main {
    
    // THESE ARE NOT (YET?) USED  // FIXME
    static public String JmlTableHeadingColor = "#FFCCCC";
    static public String JmlTableRowColor = "#FFFFCC";

    /** The entry point for command-line execution of the tool.  The conventional
     * array of arguments contains options and their arguments, files to be 
     * documented and any annotation processing classes.
     * 
     * @param args the command-line arguments
     */
    //@ requires \nonnullelements(args);
    public static void main(@NonNull String[] args) {
        new org.jmlspecs.openjml.jmldoc.ConfigurationJml();  // stores an instance in a static location
        System.exit(execute(args));
    }

    /** The compilation context used for JML parsing (which is different than
     * the context used for javadoc parsing - see the
     * <A HREF="package-summary.html">package documentation</A>.
     */
    public final static Context jmlContext = new Context();

    /**
     * The programmatic interface, used to execute the tool on a set of options
     * and files.  The return value is the value used as the exit code on the
     * command-line.
     * @param args   The command line parameters.
     * @return The return code.
     */
    //@ requires \nonnullelements(args);
    public static int execute(@NonNull String[] args) {
      Start jdoc = new JmlStart("jmldoc");//,"org.jmlspecs.openjml.jmldoc.StandardJml");
      registerTools(jmlContext,new PrintWriter(System.out,true));
      JavacFileManager.preRegister(jmlContext); // can't create it until Log has been set up - is it? FIXME
      args = processArgs(args,jmlContext);
      return jdoc.begin(args);
    }
    
    /** Internal method used to process and remove from the argument list any
     * jmldoc specific arguments.  This is called prior to the arguments being
     * processed by the Javadoc tool itself.
     * @param args the command-line arguments
     * @param context the compiler context in which the arguments apply
     * @return a reduced list of command-line arguments
     */
    //@ requires \nonnullelements(args);
    //@ ensures \nonnullelements(\result);
    static public @NonNull String[] processArgs(@NonNull String[] args, @NonNull Context context) {
        Options options = Options.instance(context);
        JmlOptionName n=null;
        LinkedList<String> newargs = new LinkedList<String>();
        int cpindex = -1;
        int i = 0;
        while (i < args.length) {
            String a = args[i];
            i++;
            n = JmlOptionName.find(a);
            if (n != null) {
                if (n.hasArg()) {
                    options.put(n.optionName(),args[i++]);
                } else {
                    options.put(n.optionName(),"");
                }
            } else if (a.equals("-classpath")) {
                newargs.add(a);
                options.put(a,args[i]);
                cpindex = newargs.size();
                newargs.add(args[i++]);
            } else if (a.equals("-sourcepath")) {
                newargs.add(a);
                options.put(a,args[i]);
                newargs.add(args[i++]);
            } else {
                newargs.add(a);
            }
        }
        // FIXME - some cleanup needed here
        //args = processJmlArgs(args,Options.instance(context));
        //List<File> files = super.processArgs(args);
        Utils.jmldebug = Options.instance(context).get(JmlOptionName.JMLDEBUG.optionName()) != null; 
        JmlSpecs.instance(context).initializeSpecsPath();
        if (!JmlOptionName.isOption(context,JmlOptionName.NOINTERNALRUNTIME)) {
            JmlSpecs.instance(context).appendRuntime();
        }
        String[] result = newargs.toArray(new String[newargs.size()]);
        // append annotation definitions onto result[cpindex] - what if there is none - need to append it to classpath definition
        return result;
    }


}

/* TODO
 *** Clean up all files
 *** Auto inclusion of annotations on the class path for the javadoc part
 * SHould we use the .xml to produce the JML
 * Extra space around PRE
 * Font for annotations
 * Font and color for specs

 * Toplevel Model classes 
 * Generate pages and links for model classes, interfaces - link them into package listings and next/previous links
 * model classes: inherited specs
 * nested and inherited model classes
 * Javadoc comments for model classes and interfaces

 *** CEmpty: Need jml field summary when there are no java fields
 *** CEmpty: need jml nested class summary when there are no java nested classes
 *** JML inherited fields/methods are not shown if there are no Java inherited fields/methods

 * Method: arguments and results do not have JML comments
 * Fields: JML comments do not turn into annotations
 * Classes, Nested classes: check that JML comments are listed as annotations

 * Pretty printing (as in the source) and wrapping of long expressions

 * Fix links in documentation of Represents clauses for inherited model fields
 *
 * Indentation of JML specs for methods depends on presence of javadocs (and tags?)

 *** Show specification sequence; show location of specs in spec sequence?
 * Read BML

 * Test use of -noqualifier
 * JML elements are not in index and in tree and in use and in deprecated
 
 * Extra horizontal rule after the JML class specifications
 
 * Rationalize newlines in annotations
 * 
 *** Enum bug
 *** standalone bug
 *** classpath bug
 *** class A should list methods inherited from BB - problem when using -protected
 *
 *** report bug in DocEnv with unnamed packages
 *** check and report problem with methods inherited from private super class when listing only -protected
 
 * Note: problem with javadocs applying to both Jml and Java elements
 * Note: including annotations in signatures of summaries, even though javadoc does not
 * Control visibility per command-line: JML nested classes and JML inherited nested classes
 * */
