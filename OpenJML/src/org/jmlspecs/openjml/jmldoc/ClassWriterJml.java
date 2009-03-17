package org.jmlspecs.openjml.jmldoc;

import java.io.Writer;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;

import org.jmlspecs.openjml.JmlCompiler;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.MethodDoc;
import com.sun.javadoc.ProgramElementDoc;
import com.sun.javadoc.Tag;
import com.sun.javadoc.Type;
import com.sun.tools.doclets.formats.html.ClassWriterImpl;
import com.sun.tools.doclets.internal.toolkit.util.ClassTree;
import com.sun.tools.doclets.internal.toolkit.util.DocFinder;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.comp.Enter;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javadoc.ClassDocImpl;
import com.sun.tools.javadoc.MethodDocImpl;

public class ClassWriterJml extends ClassWriterImpl {
    public ClassWriterJml (ClassDoc classDoc,
            ClassDoc prevClass, ClassDoc nextClass, ClassTree classTree)
    throws Exception {
        super(classDoc,prevClass,nextClass,classTree);
    }

    public void writeClassDescription() {
        super.writeClassDescription();
        ClassSymbol newsym = null;
        if (classDoc instanceof ClassDocImpl) {
            ClassSymbol oldsym = ((ClassDocImpl)classDoc).tsym;
            Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
            ClassReader.instance(context); // Instantiates the class reader, which needs to happen before the Symbol table
            Symtab syms = Symtab.instance(context);
            Name newname = Name.Table.instance(context).fromString(oldsym.flatname);
            JmlSpecs.instance(context).initializeSpecsPath(); // FIXME - should do this just once, and needs the command-line options
            newsym = syms.classes.get(newname);
            if (newsym == null) {
                JmlResolve.instance(context).loadClass(null,newname);
                newsym = syms.classes.get(newname);
                if (newsym == null) {
                    JCTree.JCCompilationUnit jcu = ((JmlCompiler)JmlCompiler.instance(context)).parse(oldsym.sourcefile);
                    JmlCompiler.instance(context).enterTrees(List.of(jcu));
                    newsym = syms.classes.get(newname);
                    newsym.complete();
                }
            }
            TypeSpecs tspecs = JmlSpecs.instance(context).get(newsym);
            if (tspecs == null) {
                ((JmlCompiler)JmlCompiler.instance(context)).loadSpecsForBinary(null,newsym);
                tspecs = JmlSpecs.instance(context).get(newsym);
            }
            headerPrinted = false;
            if (hasSpecsToPrint(tspecs)){
                printSpecHeader("JML Specifications");
                printSpecs(newsym,tspecs);
            }
            
            java.util.List<TypeSymbol> interfaces = new LinkedList<TypeSymbol>();
            printInheritedSpecs(context,newsym,interfaces);

            // Add anything that the interfaces extend
            TypeSymbol t;
            Iterator<TypeSymbol> iter = interfaces.iterator();
            while (iter.hasNext()) { // Adding to the end while iterating
                ClassSymbol csym = (ClassSymbol)iter.next();
                addInterfaces(csym,interfaces);
            }

            // Add the specs of interfaces
            for (TypeSymbol tinterface: interfaces) {
                ClassSymbol csym = (ClassSymbol)tinterface;
                TypeSpecs ttspecs = JmlSpecs.instance(context).get(csym);
                if (hasSpecsToPrint(tspecs)){
                    printSpecHeader("JML Specifications");
                    bold("JML Specifications inherited from interface " + csym + ": ");
                    printSpecs(csym,ttspecs);
                }

            }

            if (headerPrinted) printSpecEnd();
                
        }
        p();
    }
    
    public void printSpecs(ClassSymbol newsym, TypeSpecs tspecs) {
        String s = org.jmlspecs.openjml.jmldoc.Main.jmlAnnotations(this,newsym);
        print(s);
        preNoNewLine();
        for (JmlTree.JmlTypeClause clause: tspecs.clauses) {
            if (!(clause instanceof JmlTree.JmlTypeClauseDecl)) print(clause);
        }
        preEnd();
    }
    
    public void printInheritedSpecs(Context context, ClassSymbol newsym, java.util.List<TypeSymbol> interfaces) {
        ClassSymbol csym = (ClassSymbol)newsym.getSuperclass().tsym;
        if (csym == null) return;
        TypeSpecs tspecs = JmlSpecs.instance(context).get(csym);
        if (hasSpecsToPrint(tspecs)){
            printSpecHeader("JML Specifications");
            bold("JML Specifications inherited from " + csym + ": ");
            printSpecs(csym,tspecs);
        }
        addInterfaces(csym,interfaces);
        printInheritedSpecs(context,csym,interfaces);
    }
    
    public void addInterfaces(ClassSymbol c, java.util.List<TypeSymbol> interfaces) {
        for (com.sun.tools.javac.code.Type t: c.getInterfaces()) {
            // Could use a set,but want to keep them in a sort of order
            if (!interfaces.contains(t.tsym)) interfaces.add(t.tsym);
        }
    }
    
    public boolean hasSpecsToPrint(TypeSpecs tspecs) {
        if (!tspecs.modifiers.annotations.isEmpty()) return true;
        for (JmlTree.JmlTypeClause clause: tspecs.clauses) {
            if (!(clause instanceof JmlTree.JmlTypeClauseDecl)) return true;
        }
        return false;
    }
    
    private boolean headerPrinted = false;
    
    public void printSpecHeader(String text) {
        if (headerPrinted) return;
        print("<TABLE BORDER=\"1\" WIDTH=\"100%\" CELLPADDING=\"3\" CELLSPACING=\"0\" SUMMARY=\"\">");  println();
        print("<TR BGCOLOR=\"#CCCCFF\" CLASS=\"TableHeadingColor\">"); println();
        print("<TH ALIGN=\"left\" COLSPAN=\"1\"><FONT SIZE=\"+2\">"); println();
        print("<B>" + text + "</B></FONT></TH>"); println();
        print("</TR>"); println();
        print("<TR BGCOLOR=\"white\" CLASS=\"TableRowColor\">"); println();
        print("<TD ALIGN=\"left\" VALIGN=\"top\" WIDTH=\"1%\">"); println();
        headerPrinted = true;
    }
    
    public void printSpecEnd() {
        //print("&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;</TD>"); println();
        print("</TR>"); println();
        print("</TABLE>"); println();
        print("&nbsp;"); println();

    }
    
}
