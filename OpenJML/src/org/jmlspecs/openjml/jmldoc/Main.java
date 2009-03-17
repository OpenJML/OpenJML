package org.jmlspecs.openjml.jmldoc;

import java.io.PrintWriter;
import java.util.LinkedList;

import org.jmlspecs.openjml.JmlCompiler;
import org.jmlspecs.openjml.JmlOptionName;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;

import com.sun.javadoc.ClassDoc;
import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlFlow;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Messages;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javadoc.ClassDocImpl;
import com.sun.tools.javadoc.JavadocClassReader;
import com.sun.tools.javadoc.Start;
import org.jmlspecs.annotations.*;

/** This is the class containing the entry points for the jmldoc tool. */
public class Main extends org.jmlspecs.openjml.Main {
    
    // THESE ARE NOT (YET?) USED
    static public String JmlTableHeadingColor = "#FFCCCC";
    static public String JmlTableRowColor = "#FFFFCC";

    public static void main(String[] args) {
        new org.jmlspecs.openjml.jmldoc.ConfigurationJml();  // stores an instance in a static location
        System.exit(execute(args));
    }

    public static Context jmlContext;

    /**
     * Programmatic interface.
     * @param args   The command line parameters.
     * @return The return code.
     */
    public static int execute(String[] args) {
      Start jdoc = new JmlStart("jmldoc","org.jmlspecs.openjml.jmldoc.StandardJml");
      jmlContext = new Context();
      registerTools(jmlContext,new PrintWriter(System.out,true));
      JavacFileManager.preRegister(jmlContext); // can't create it until Log has been set up - is it? FIXME
      args = processArgs(args,jmlContext);
      return jdoc.begin(args);
    }
    
    // FIXME - fix this to actually take out any jmldoc specific arguments
    /** Internal method used to process and remove from the argument list any
     * jmldoc specific arguments.  This is called prior to the arguments being
     * processed by the Java compiler itself.
     * @param args the command-line arguments
     * @param context the compiler context in which the arguments apply
     * @returns a reduced list of command-line arguments
     */
    //@ requires \nonnullelements(args);
    //@ ensures \nonnullelements(\result);
    static public @NonNull String[] processArgs(@NonNull String[] args, @NonNull Context context) {
        LinkedList<String> newargs = new LinkedList<String>();
        int i = 0;
        while (i < args.length) {
            String a = args[i];
            i++;
            // FIXME - handle any and all jml-specific arguments; where to process the options?
            if (a.equals(JmlOptionName.NOINTERNALRUNTIME)) {
                
            } else {
                newargs.add(a);
            }
        }
        //args = processJmlArgs(args,Options.instance(context));
        //List<File> files = super.processArgs(args);
        Utils.jmldebug = Options.instance(context).get(JmlOptionName.JMLDEBUG.optionName()) != null; 
        JmlSpecs.instance(context).initializeSpecsPath();
        if (!JmlOptionName.isOption(context,JmlOptionName.NOINTERNALRUNTIME)) {
            JmlSpecs.instance(context).appendRuntime();
        }
        return newargs.toArray(new String[newargs.size()]);
    }

//    /** Called to register the JML internal tools that replace the tools used
//     * in the Java compiler.
//     * @param context the compiler context in which the tools are to be used
//     * @param out the PrintWriter used for error and informational messages
//     */
//    // MAINTENANCE - this should match 
//    static public void registerTools(/*@ non_null */ Context context, PrintWriter out) {
//
//        // This is done later, but we do it here so that the Log is
//        // available if tool registration (or argument processing) needs the
//        // Log.  However, note that if the Log is actually instantiated before
//        // Java arguments are read, then it is not set consistently with those 
//        // options.
//        context.put(Log.outKey,out);
//
//        // These have to be first in case there are error messages during 
//        // tool registration.
//        Messages.instance(context).add(Utils.messagesJML); // registering an additional source of JML-specific error messages
//
//        // These register JML versions of the various tools.  ALL OF THESE MUST
//        // REGISTER FACTORIES AND NOT CREATE ACTUAL INSTANCES.  Creating instances
//        // will trigger a cascade of tool instance generation, which can create
//        // tools (such as the Log) before the Options are processed, and can
//        // trigger some circular dependencies in the constructors of the various
//        // tools.
//        // Any initialization of these tools that needs to be done based on 
//        // options should be performed in processArgs() in this method.
//        JmlSpecs.preRegister(context); // registering the specifications repository
//        JmlParser.JmlFactory.preRegister(context); // registering a Jml-specific factory from which to generate JmlParsers
//        JmlScanner.JmlFactory.preRegister(context); // registering a Jml-specific factory from which to generate JmlScanners
//        JmlTree.Maker.preRegister(context); // registering a JML-aware factory for generating JmlTree nodes
//        JmlCompiler.preRegister(context);
//        JmlEnter.preRegister(context);
//        JmlResolve.preRegister(context);
//        JmlMemberEnter.preRegister(context);
//        JmlFlow.preRegister(context);
//        JmlAttr.preRegister(context);  // registering a JML-aware type checker
//        JmlPretty.preRegister(context);
//    }

    /** A utility function that prints out any JML annotations as '@' symbols
     * followed by simple names.
     * @param writer the writer on which to write the output
     * @param annotations the list of annotations from which to pick the JML ones
     */
    public static void printJmlAnnotations(
            @NonNull //@edu.umd.cs.findbugs.annotations.NonNull
            PrintWriter writer, 
            @NonNull //@edu.umd.cs.findbugs.annotations.NonNull
            List<JCAnnotation> annotations) {
        if (annotationPackage == null) {
            Name pn = Name.Table.instance(jmlContext).fromString("org.jmlspecs.annotations");
            annotationPackage = Symtab.instance(jmlContext).packages.get(pn);
        }
        for (List<JCAnnotation> l = annotations; l.nonEmpty(); l = l.tail) {
            JCTree t = l.head.annotationType;
            if (t instanceof JCTree.JCIdent) {
                JCTree.JCIdent id = (JCTree.JCIdent)t;
                //if (id.sym.owner == annotationPackage) {
                    writer.print("@" + t);
                //}
            }
            writer.print(" ");
        }
    }
    
    public static String jmlAnnotations(PrintWriter writer, Symbol symbol) {
        String s = "";
        if (symbol.getAnnotationMirrors() == null) return s;
        for(Attribute.Compound compound: symbol.getAnnotationMirrors()) {   // FIXME - want just JML ones
            s = s + (" @" + compound.type.tsym.name);
        }
        return s;
    }
    
    /** A utility method that returns true if the argument has content worth printing
     * @param specs the object containing method specifications
     * @return true if there are specifications worth printing
     */
    public static boolean hasSpecs(JmlMethodSpecs specs) {
        if (specs == null) return false;
        if (!specs.cases.isEmpty()) return true;
        return false;
    }

    /** An internal variable, lazily initialized, that holds the symbol for the
     * package representing 'org.jmlspecs.annotations', which holds all the 
     * JML annotation interfaces.
     */
    protected static Symbol annotationPackage = null;
    
    public static ClassSymbol findNewClassSymbol(ClassDoc classdoc) {
        if (classdoc instanceof ClassDocImpl) {
            ClassSymbol oldsym = ((ClassDocImpl)classdoc).tsym;
            Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
            Name newname = Name.Table.instance(context).fromString(oldsym.flatname);
            return Symtab.instance(context).classes.get(newname);
        }
        return null;
    }

}

/* TODO
 *** Clean up all files
 *** Use command-line args appropriately - esp specs path
 *** Report CL args with help
 *** Javadoc for JML constructs
 * SHould we use the .xml to produce the JML
 * Extra space around PRE
 * Font for annotations
 * Font and color for specs
 * Ghost and model field summary needs annotation
 * Generate pages and links for model classes, interfaces - link them into package listings and next/previous links
 *** End of file while parsing problem
 * CEmpty: Need jml field summary when there are no java fields
 * CEmpty: need jml nested class summary when there are no java nested classes
 * JML inherited fields/meethods are not shown if there are no Java inherited fields/methods
 * Method: arguments do not have annotations
 * Method: arguments and results do not have JML comments
 * Pretty printing (as in the source) and wrapping of long expressions
 * Fields: JML comments do not turn into annotations
 * Model methods, model classes: inherited specs
 * Classes: check that JML comments are listed as annotations
 * Represents clauses for inherited model fields
 *** Disambiguate methods
 * Toplevel Model classes 
 * Read BML
 * Javadoc comments for ghost, model fields, model methods, model classes
 * Javadoc comments for class specifciations???
 *** Control visibility per command-line: model methods, ghost./model fields, model classes, inherited model fields, methods
 * Try model annotations, enum types
 * */
