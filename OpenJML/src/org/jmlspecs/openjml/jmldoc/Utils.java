package org.jmlspecs.openjml.jmldoc;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlSpecs;

import com.sun.javadoc.ClassDoc;
import com.sun.tools.doclets.formats.html.AbstractMemberWriter;
import com.sun.tools.doclets.formats.html.SubWriterHolderWriter;
import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javadoc.ClassDocImpl;

/** This class contains utility functions used by the rest of the package. */
public class Utils {
    
    //FIXME _ is there a way to discover this?
    /** The fully-qualified name of the package the annotations are defined in. */
    @NonNull
    private final static String packageString = "org.jmlspecs.annotation";

    // FIXME - this is not thread/context safe
    
    /** An internal variable, lazily initialized, that holds the symbol for the
     * package representing 'org.jmlspecs.annotation', which holds all the 
     * JML annotation interfaces.
     */
    private static Symbol annotationPackage = null;
    
    /** Returns the Symbol (in the JML context) of the package that all of
     * the annotations are in.
     * @return the Package Symbol for the annotation package
     */
    public static Symbol annotationPackage() {
        Symbol s = annotationPackage;
        if (s == null) {
            Name pn = Names.instance(Main.jmlContext).fromString(packageString);
            annotationPackage = Symtab.instance(Main.jmlContext).packages.get(pn);
        }
        return s;
    }
    
    /** A utility function that returns a String containing text version of the
     * JML annotations belonging to the given symbol.
     * @param symbol the symbol whose annotations are to be printed
     * @return a String with a text representation of the JML annotations
     *    (with no end-of-line characters)
     */
    public static @NonNull String jmlAnnotations(@NonNull Symbol symbol) {
        String s = "";
        Symbol ap = annotationPackage();
        if (symbol.getAnnotationMirrors() == null) return s;
        for(Attribute.Compound compound: symbol.getAnnotationMirrors()) {
            if (compound.type.tsym.owner == ap) s = s + (" @" + compound.type.tsym.name);
        }
        return s;
    }
    
    /** A utility method that returns true if the argument has content worth printing
     * @param specs the object containing method specifications
     * @return true if there are specifications worth printing
     */
    public static boolean hasSpecs(JmlSpecs.MethodSpecs specs) {
        if (specs == null) return false;
        if (!specs.cases.cases.isEmpty()) return true;
        return false;
    }

    /** A utility function that returns the class symbol in the JML compilation
     * context corresponding to the class represented by the classdoc argument.
     * @param classdoc the class whose symbol is wanted
     * @return the Symbol in the new context for the class
     */
    public static ClassSymbol findNewClassSymbol(ClassDoc classdoc) {
        if (classdoc instanceof ClassDocImpl) {
            ClassSymbol oldsym = ((ClassDocImpl)classdoc).tsym;
            Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
            Name newname = Names.instance(context).fromString(oldsym.flatname.toString());
            return Symtab.instance(context).classes.get(newname);
        }
        return null;
    }
    
    /** A utility function that returns a list of the classes and interfaces that
     * the argument directly or indirectly extends or implements.  Interfaces are
     * listed at most once; classes are listed before interfaces; the argument
     * itself is not in the list.
     * @param csym the class or interface whose supers are wanted
     * @return a list of super classes and interfaces
     */
    // FIXME - check this works for interfaces
    public static @NonNull java.util.List<ClassSymbol> getSupers(@NonNull ClassSymbol csym) {
        java.util.List<ClassSymbol> list = new java.util.ArrayList<ClassSymbol>();
        ClassSymbol c = csym;
        while (true) {
            c = (ClassSymbol)c.getSuperclass().tsym;
            if (c == null) break;
            list.add(c);
        }
        
        c = csym;
        for (com.sun.tools.javac.code.Type t: c.getInterfaces()) {
            if (!list.contains(t.tsym)) list.add((ClassSymbol)t.tsym);
        }
        for (int i=0; i<list.size(); i++) { 
            c = list.get(i);
            for (com.sun.tools.javac.code.Type t: c.getInterfaces()) {
                if (!list.contains(t.tsym)) list.add((ClassSymbol)t.tsym);
            }
        }
        return list;
    }

    /** This writes a colored header.   Note that the color specified here
     * is generally overridden by a hard-coded property.
     * 
     * @param classDoc the class whose ghost and model fields are to be described
     */
    public static void writeHeader(
            @NonNull SubWriterHolderWriter writer, 
            @NonNull AbstractMemberWriter mw, 
            @NonNull ClassDoc classDoc, 
            @NonNull String title, 
            int tableColumns) {
        
        //printSummaryAnchor(cd);
        
        //mw.printTableSummary();
        writer.tableIndexSummary();
        writer.tableHeaderStart("#CCCCFF",tableColumns);

        writer.tableCaptionStart();

        //mw.printSummaryLabel();
        writer.strong(title);
        writer.tableHeaderEnd();

        writer.tableCaptionEnd();
        
       // if (mw != null) mw.printSummaryTableHeader(classDoc); // DRCok - does not compiler with b144, but what should it be?
}
    
    /** Returns true if Symbol msym should be in the inherited list for the given
     * class.  msym must be an element of a super class or interface.
     * @param msym the element being tested
     * @param currentClassSym the class being documented
     * @return true if msym is visible in currentClassSym
     */
    public static boolean isInherited(Symbol msym, ClassSymbol currentClassSym) {
        long m = msym.flags();
        if ((m & Flags.PRIVATE) != 0) return false;
        if (msym.owner == currentClassSym) return false;
        if ((m & Flags.AccessFlags) == 0 &&
                (currentClassSym.packge() != msym.packge())) return false;
        return true;
    }

}
