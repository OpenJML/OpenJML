package org.jmlspecs.openjml.jmldoc;

import java.io.IOException;

import org.jmlspecs.annotations.*;
import org.jmlspecs.openjml.JmlCompiler;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;

import com.sun.javadoc.ClassDoc;
import com.sun.tools.doclets.formats.html.ClassWriterImpl;
import com.sun.tools.doclets.formats.html.ConfigurationImpl;
import com.sun.tools.doclets.internal.toolkit.util.ClassTree;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.comp.Attr;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Enter;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javadoc.ClassDocImpl;

/** This class extends ClassWriterImpl in order to include in the HTML output
 * information about the JML specifications of the class whose javadoc page
 * is being written.
 * @author David R. Cok
 *
 */
public class ClassWriterJml extends ClassWriterImpl {
    
    /** Constructs an instance of the class.
     * 
     * @param classDoc the Doc element being printed
     * @param prevClass the Doc element of the class before this in the javadoc order
     * @param nextClass the Doc element of the class after this in the javadoc order
     * @param classTree the class tree for the given class
     * @throws Exception
     */
    public ClassWriterJml (ClassDoc classDoc,
            ClassDoc prevClass, ClassDoc nextClass, ClassTree classTree)
    throws Exception {
        super(classDoc,prevClass,nextClass,classTree);
    }
    
    /** This makes sure that the JML specifications are instantiated for the
     * given class, by re-parsing the class in a different context.
     * @param newname the (fully-qualified) Name of the class in the new context
     * @param oldsym the Symbol of the class in the old context
     * @return the Symbol of the class in the new context
     */
    public @NonNull ClassSymbol instantiateClass(@NonNull Name newname, @NonNull ClassSymbol oldsym) {
        Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
        ClassReader.instance(context); // Instantiates the class reader, which needs to happen before the Symbol table
        Symtab syms = Symtab.instance(context);
        ClassSymbol newsym = syms.classes.get(newname);
        if (newsym == null) {
            if (oldsym.sourcefile != null) {
                try {
                    JmlCompiler.instance(context).compile(List.of(oldsym.sourcefile));
                    newsym = syms.classes.get(newname);
                } catch (Throwable e) {
                    // FIXME - ???
                }
            }
            if (newsym == null) {
                Env<AttrContext> env = Enter.instance(context).getEnv(newsym);
                JmlResolve.instance(context).loadClass(env,newname);
                newsym = syms.classes.get(newname);
                if (newsym == null) {
                    JCTree.JCCompilationUnit jcu = ((JmlCompiler)JmlCompiler.instance(context)).parse(oldsym.sourcefile);
                    JmlCompiler.instance(context).enterTrees(List.of(jcu));
                    newsym = syms.classes.get(newname);
                    newsym.complete();
                }
            }
        }
        instantiateSpecs(context, newsym);
        return newsym;
    }
    
    /** This method makes sure that the specs for a given class are parsed
     * and read and loaded into the JmlSpecs database.
     * @param context the compilation context to use
     * @param newsym the class in that compilation context whose specs are wanted
     */
    public void instantiateSpecs(@NonNull Context context, @NonNull ClassSymbol newsym) {
        // Make sure that superclasses are instantiated
        com.sun.tools.javac.code.Type t = newsym.getSuperclass();
        if (t.tsym != null) instantiateSpecs(context,(ClassSymbol)t.tsym);
        // Make sure that superinterfaces are instantiated
        List<com.sun.tools.javac.code.Type> interfaces = newsym.getInterfaces();
        while (interfaces.tail != null) {
            instantiateSpecs(context,(ClassSymbol)interfaces.head.tsym);
            interfaces = interfaces.tail;
        }
        
        TypeSpecs tspecs = JmlSpecs.instance(context).get(newsym);
        if (tspecs == null) {
            ((JmlCompiler)JmlCompiler.instance(context)).loadSpecsForBinary(null,newsym);
        }
    }

    /** This overrides the parent class method in order to append the JML specs
     * of a class (e.g. invariants) after the class description near the beginning
     * of the javadoc output.
     */
    @Override
    public void writeClassDescription() {
        super.writeClassDescription();
        ClassSymbol newsym = null;
        if (classDoc instanceof ClassDocImpl) {
            ClassSymbol oldsym = ((ClassDocImpl)classDoc).tsym;
            Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
            Name newname = Names.instance(context).fromString(oldsym.flatname.toString());
            newsym = Symtab.instance(context).classes.get(newname);
            //newsym = instantiateClass(newname,oldsym);
            TypeSpecs tspecs = JmlSpecs.instance(context).get(newsym);
            String ss = Utils.jmlAnnotations(newsym);
            headerPrinted = false;
            boolean hsp = hasSpecsToPrint(tspecs);
            if (hsp || ss.length()!=0){
                printSpecHeader("JML Specifications");
//                bold("Specification sequence:");
//                JmlClassDecl list = tspecs.decl;
//                br();
                if (ss.length()!=0) {
                    strong("Annotations:");
                    print(ss);
                    br();
                }
                if (hsp) printSpecs(tspecs);
            }
            
            for (ClassSymbol ssym: Utils.getSupers(newsym)) {
                printInheritedSpecs(context,ssym);
            }

            if (headerPrinted) printSpecEnd();
                
        }
        p();
    }
    
    /** Prints the given specs (any clauses that are not declarations, e.g.
     * not field or method declarations).
     * 
     * @param tspecs the specs to print
     */
    public void printSpecs(TypeSpecs tspecs) {
        preNoNewLine();
        for (JmlTree.JmlTypeClause clause: tspecs.clauses) {
            if (clause instanceof JmlTree.JmlTypeClauseDecl) continue;
            if (clause instanceof JmlTree.JmlTypeClauseRepresents) continue;
            print("    ");
            print(JmlPretty.write(clause,false));
            println();
        }
        preEnd();
    }
    
    /** Prints specs with a header that these are inherited from a super class
     * 
     * @param context the compilation context in use
     * @param csym the super class or interface whose specs are to be printed
     */
    public void printInheritedSpecs(Context context, ClassSymbol csym) {
        TypeSpecs tspecs = JmlSpecs.instance(context).get(csym);
        if (hasSpecsToPrint(tspecs)){
//            printSpecHeader("JML Specifications");
            strong("JML Specifications inherited from " + csym + ": ");
            printSpecs(tspecs);
        }
    }
    
    /** Returns true if the argument contains specs worth printing.
     * @param tspecs the specs of a class or interface
     * @return true if the argument contains stuff to print
     */
    public boolean hasSpecsToPrint(TypeSpecs tspecs) {
        if (!tspecs.modifiers.annotations.isEmpty()) return true;
        for (JmlTree.JmlTypeClause clause: tspecs.clauses) {
            if (!(clause instanceof JmlTree.JmlTypeClauseDecl)) return true;
        }
        return false;
    }
    
    /** Set to true once the 'JML Specifications' header has been printed; this
     * happens the first time a class or superclass is found with something
     * to print. */
    private boolean headerPrinted = false;
    
    /** Prints a header containing the given text.  This is written to match
     * the other header blocks produced in various places in the javadoc code
     * (e.g. SubHolderWriterHolder.printTableHeadingBackground).
     * 
     * @param text the title to put in the header block
     */
    public void printSpecHeader(@NonNull String text) {
        if (headerPrinted) return;
        Utils.writeHeader(this,null,null,text,1);
        headerPrinted = true;
        // Write the beginning of a row
        println("<TR BGCOLOR=\"white\" CLASS=\"TableRowColor\">");
        println("<TD ALIGN=\"left\" VALIGN=\"top\" WIDTH=\"1%\">");
    }
    
    /** Prints the HTML that ends a table begun by printSpecHeader */
    public void printSpecEnd() {
        println("</TD></TR>");
        tableEnd();
        space();
    }

    /** This overrides the method in HtmlDocletWriter in order to issue a
     *  comment saying that the file was generated by jmldoc.  Note that
     *  the comment is not in the same place as the javadoc comment would
     *  be, but that is too intrusive to do.  Also note that we generate a
     *  date-less jmldoc comment (rather than no comment) even if notimestamp
     *  is specified.
     */
    @Override
    public void printHtmlHeader(String title, String[] metakeywords,
            boolean includeScript) {
        boolean notimestamp = configuration.notimestamp;
        configuration.notimestamp = true;
        try {
            if (!notimestamp) {
                print("<!-- Generated by jmldoc (build " + ConfigurationImpl.BUILD_DATE + ":" + JavaCompiler.version() + ") on ");
                print(today());
                println(" -->");
            } else {
                println("<!-- Generated by jmldoc -->");                
            }
            super.printHtmlHeader(title,metakeywords,includeScript);
        } finally {
            configuration.notimestamp = notimestamp;
        }
    }

}
