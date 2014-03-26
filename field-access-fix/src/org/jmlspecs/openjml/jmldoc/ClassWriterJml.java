package org.jmlspecs.openjml.jmldoc;

import org.jmlspecs.annotation.NonNull;
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
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javadoc.ClassDocImpl;

/**
 * This class extends ClassWriterImpl in order to include in the HTML output
 * information about the JML specifications of the class whose javadoc page is
 * being written.
 * 
 * @author David R. Cok
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
    

    // FIXME - major change in b144
//    /** This overrides the parent class method in order to append the JML specs
//     * of a class (e.g. invariants) after the class description near the beginning
//     * of the javadoc output.
//     */
//    @Override
//    public void writeClassDescription() {
//        super.writeClassDescription();
//        ClassSymbol newsym = null;
//        if (classDoc instanceof ClassDocImpl) {
//            ClassSymbol oldsym = ((ClassDocImpl)classDoc).tsym;
//            Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
//            Name newname = Names.instance(context).fromString(oldsym.flatname.toString());
//            newsym = Symtab.instance(context).classes.get(newname);
//            TypeSpecs tspecs = JmlSpecs.instance(context).get(newsym);
//            String ss = Utils.jmlAnnotations(newsym);
//            headerPrinted = false;
//            boolean hsp = hasSpecsToPrint(tspecs);
//            if (hsp || ss.length()!=0){
//                printSpecHeader("JML Specifications");
//                if (ss.length()!=0) {
//                    strong("Annotations:");
//                    print(ss);
//                    br();
//                }
//                if (hsp) printSpecs(tspecs);
//            }
//            
//            for (ClassSymbol ssym: Utils.getSupers(newsym)) {
//                printInheritedSpecs(context,ssym);
//            }
//
//            if (headerPrinted) printSpecEnd();
//                
//        }
//        p();
//    }
    
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
            strong("JML Specifications inherited from " + csym + ": ");
            printSpecs(tspecs);
        }
    }
    
    /** Returns true if the argument contains specs worth printing (this does not
     * include model or ghost declarations).
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
