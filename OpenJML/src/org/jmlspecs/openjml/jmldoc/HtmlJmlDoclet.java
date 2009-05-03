package org.jmlspecs.openjml.jmldoc;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import javax.annotation.processing.Processor;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlCompiler;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.PackageDoc;
import com.sun.javadoc.RootDoc;
import com.sun.tools.doclets.formats.html.ConfigurationImpl;
import com.sun.tools.doclets.formats.html.HtmlDoclet;
import com.sun.tools.doclets.internal.toolkit.AbstractDoclet;
import com.sun.tools.doclets.internal.toolkit.Configuration;
import com.sun.tools.doclets.internal.toolkit.util.ClassTree;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Enter;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javadoc.ClassDocImpl;
import com.sun.tools.javadoc.Messager;

public class HtmlJmlDoclet extends HtmlDoclet {

    public static boolean start(RootDoc root) {
        HtmlDoclet doclet = new HtmlJmlDoclet();
        return doclet.start(doclet, root);
    }

    protected boolean isValidDoclet(AbstractDoclet doclet) { 
        return true;
    }

    protected void generateClassFiles(RootDoc root, ClassTree classtree) {
        doJmlParsing(root);
        Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
//        if (Log.instance(context).nerrors > 0) {
//            throw new Messager.ExitJavadoc(); // Aborts Javadoc
//        }
        super.generateClassFiles(root,classtree);
    }
    
    protected void doJmlParsing(RootDoc root) {
        Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
        ClassReader.instance(context); // Instantiates the class reader, which needs to happen before the Symbol table
        Symtab syms = Symtab.instance(context);
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

        try {
            System.out.println("Compiling with JML");
            JmlCompiler.instance(context).compile(list.toList(),List.<String>nil(),List.<Processor>nil());
        } catch (java.io.IOException e) {
            // ??? TODO
        }

    }
    
}
