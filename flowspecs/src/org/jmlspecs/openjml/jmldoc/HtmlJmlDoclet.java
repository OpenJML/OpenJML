package org.jmlspecs.openjml.jmldoc;

import java.util.HashSet;
import java.util.Set;

import javax.annotation.processing.Processor;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlCompiler;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.PackageDoc;
import com.sun.javadoc.RootDoc;
import com.sun.tools.doclets.formats.html.HtmlDoclet;
import com.sun.tools.doclets.internal.toolkit.AbstractDoclet;
import com.sun.tools.doclets.internal.toolkit.util.ClassTree;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javadoc.ClassDocImpl;

/** Extends the parent class in order to add in JML functionality.  The parent
 * class does not expect to be extended, but to do otherwise would mean 
 * replicating too much code.
 * @author David R. Cok
 *
 */
public class HtmlJmlDoclet extends HtmlDoclet {

    /** Starts in the standard way, by instantiating this class and calling
     * the non-static start method.
     * @param root the root of the javadoc class document tree
     * @return true if the process executed without error
     */
    public static boolean start(RootDoc root) {
        HtmlDoclet doclet = new HtmlJmlDoclet();
        return doclet.start(doclet, root);
    }

    
    protected void startGeneration(RootDoc root) throws Exception { // DRC - changed from private to protected
        if (root.classes().length == 0) {
            configuration.message.
                error("doclet.No_Public_Classes_To_Document");
            return;
        }
        //doJmlParsing(root);
        super.startGeneration(root);
    }

    /** Overrides in order to declare this a valid doclet, since the parent class
     * only likes itself.
     */
    @Override
    protected boolean isValidDoclet(AbstractDoclet doclet) { 
        return true;
    }

    /** Overrides in order to parse all of the JML files in order to get the
     * specs, prior to generating class files.
     */
    @Override
    protected void generateClassFiles(RootDoc root, ClassTree classtree) {
        doJmlParsing(root);
        // TODO - control with a flag?
//        Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
//        if (Log.instance(context).nerrors > 0) {
//            throw new Messager.ExitJavadoc(); // Aborts Javadoc if there are any errors
//        }
        // Instead we proceed to document whatever we can despite perhaps isolated errors
        super.generateClassFiles(root,classtree);
    }
    
    /** The helper method that does all of the JML parsing, by collecting all of
     * the class symbols generated by javadoc's analysis of the input files,
     * and then initiating a compilation with a new compilation context on all
     * of the input files.
     * @param root the javadoc class tree
     */
    protected void doJmlParsing(RootDoc root) {
        Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
        ClassReader.instance(context); // Instantiates the class reader, which needs to happen before the Symbol table
        ListBuffer<JavaFileObject> list = new ListBuffer<JavaFileObject>();
        Set<JavaFileObject> set = new HashSet<JavaFileObject>();

        String[] packageNames = configuration.classDocCatalog.packageNames();
        for (int packageNameIndex = 0; packageNameIndex < packageNames.length;
                packageNameIndex++) {
            for (ClassDoc classDoc : configuration.classDocCatalog.allClasses(
                    packageNames[packageNameIndex])) {
                ClassSymbol oldsym = ((ClassDocImpl)classDoc).tsym;
                if (set.add(oldsym.sourcefile)) {  // true if not already present
                    list.append(oldsym.sourcefile);
                }
            }
        }

        PackageDoc[] packages = root.specifiedPackages();
        for (int i = 0; i < packages.length; i++) {
            for (ClassDoc classDoc : packages[i].allClasses()) {
                ClassSymbol oldsym = ((ClassDocImpl)classDoc).tsym;
                if (set.add(oldsym.sourcefile)) {  // true if not already present
                    list.append(oldsym.sourcefile);
                }
            }
        }

        // Javadoc is somewhat verbose - we'll add this message to it
        Log.instance(context).noticeWriter.println("Compiling with JML");
        JmlCompiler.instance(context).compile(list.toList(),List.<String>nil(),List.<Processor>nil());
    }
    
}
