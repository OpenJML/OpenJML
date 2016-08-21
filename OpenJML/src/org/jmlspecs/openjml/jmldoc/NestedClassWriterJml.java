package org.jmlspecs.openjml.jmldoc;

import java.util.ArrayList;
import java.util.Collections;

import org.jmlspecs.annotation.*;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.ProgramElementDoc;
import com.sun.javadoc.Tag;
import com.sun.tools.doclets.formats.html.NestedClassWriterImpl;
import com.sun.tools.doclets.formats.html.SubWriterHolderWriter;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javadoc.ClassDocImpl;
import com.sun.tools.javadoc.DocEnv;

/**
 * This class extends its parent class in order to add to the list of Java
 * nested classes printed out by Javadoc any nested model classes or interfaces
 * supplied by JML.
 * 
 * @author David R. Cok
 */
public class NestedClassWriterJml extends NestedClassWriterImpl {

    /** The ClassSymbol (in the JML compilation context) of the class
     * whose nested classes are being described.
     */
    protected @NonNull ClassSymbol currentClassSym;

//    protected @NonNull ClassDoc currentClassDoc;
    
    /** The env corresponding to the input classdoc */
    protected @NonNull DocEnv currentDocEnv;
    
    /** The constructor for this kind of writer.
     * 
     * @param writer the actual writer to which calls are delegated
     * @param classdoc the class whoise nested classes this writer describes
     */
    public NestedClassWriterJml(@NonNull SubWriterHolderWriter writer,
            @NonNull ClassDoc classdoc) {
        super(writer, classdoc);
//        currentClassDoc = classdoc;
        currentClassSym = Utils.findNewClassSymbol(classdoc);
        currentDocEnv = ((ClassDocImpl)classdoc).docenv();
    }
    
    // FIXME - major change in b144
//    /** This is overridden to tack onto the end of the nested class information
//     * any information about nested JML classes.
//     * @param classDoc the classDoc whose nested members are being described
//     */
//    public void writeMemberSummaryFooter(@NonNull ClassDoc classDoc) {
//        super.writeMemberSummaryFooter(classDoc);
//        writeJmlNestedClassSummary(classDoc);
//    }

    // FIXME - major change in b144
//    /** This is overridden to tack onto the end of the inherited 
//     * nested class information
//     * any information about inherited nested JML classes.
//     * @param classDoc the classDoc whose nested members are being described
//     */
//    @Override
//    public void writeInheritedMemberSummaryFooter(@NonNull ClassDoc classDoc) {
//        writeJmlInheritedNestedClassSummaryFooter(classDoc);
//        writer.writeInheritedMemberSummaryFooter(classDoc);
//    }
    
    /** This is used in place of DocEnv.shouldDocument because model methods are
     * marked as synthetic and thus not allowed by DocEnv.
     * @param currentDocEnv TODO
     * @param sym TODO
     * @return TODO
     */
    public boolean shouldDocumentModel(DocEnv currentDocEnv, ClassSymbol sym) {
        return 
            // FIXME - do we need the line below - what does it guard against?
            //(currentDocEnv.docClasses || currentDocEnv.getClassDoc(sym).tree != null) &&
            currentDocEnv.isVisible(sym);
    }
    
    /** This writes out information about JML inherited nested classes,
     * including writing the header and footer.
     * @param classDoc the super class whose members are being described as inherited from currentClassSym
     */
    public void writeJmlInheritedNestedClassSummaryFooter(@NonNull ClassDoc classDoc) {
        ClassSymbol nsym = Utils.findNewClassSymbol(classDoc);
        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(nsym);
        ArrayList<ClassDoc> list = new ArrayList<ClassDoc>();
        // Find all the JML inherited nested classes to describe
        for (JmlClassDecl mdecl : tspecs.modelTypes) {
            ClassSymbol msym = mdecl.sym;
            if (!shouldDocumentModel(currentDocEnv,msym)) continue;
            if (!Utils.isInherited(msym,currentClassSym)) continue;
            ClassDoc modelClass = new ClassDocJml(((ClassDocImpl)classDoc).docenv(),msym,mdecl.docComment,mdecl,null);
            list.add(modelClass);
        } 
        
        if (!list.isEmpty()) {
            writer.br();
            writer.strong("Inherited JML model classes and interfaces: ");
            Collections.sort(list);
            boolean isFirst = true;
            // FIXME - major change in b144
//            for (ClassDoc nestedClass: list) {
//                writer.printInheritedSummaryMember(this, classDoc, nestedClass, isFirst);
//                isFirst = false;
//            }
        }
    }

    // FIXME - do we need this?
    /** check whether this class should be documented. */
    public boolean shouldDocument(ClassSymbol sym) {
        // special version of currentDocEnv.shouldDocument(msym)
        return
            (sym.flags_field&Flags.SYNTHETIC) == 0;// && // no synthetics
            //(docClasses || getClassDoc(sym).tree != null) &&
            //isVisible(sym);
    }


    /** This writes out information about JML directly nested classes,
     * including writing the header and footer.
     * @param classDoc the class whose inherited members are being described
     */
    public void writeJmlNestedClassSummary(@NonNull ClassDoc classDoc) {
        ArrayList<ClassDoc> list = new ArrayList<ClassDoc>();
        DocEnv denv = ((ClassDocImpl)classDoc).docenv();
        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(currentClassSym);
        for (JmlClassDecl cdecl : tspecs.modelTypes) {
            ClassSymbol msym = cdecl.sym;
            //if (!denv.shouldDocument(msym)) continue; // FIXME - explain why the line below instead of this one
            if (!denv.isVisible(msym)) continue;
            ClassDoc modelClass = new ClassDocJml(((ClassDocImpl)classDoc).docenv(),msym,cdecl.docComment,cdecl,null);
            list.add(modelClass);
        }
        if (list.isEmpty()) return;
        Collections.sort(list);
        writeJmlNestedClassSummaryHeader(classDoc);
        // The following loop is copied with modifications from MemberSummaryBuilder.buildSummary
        // FIXME - major change in b144
//        for (int i = 0; i<list.size(); i++) {
//            ClassDoc member = list.get(i);
//            Tag[] firstSentenceTags = member.firstSentenceTags();
//            writeMemberSummary(classDoc, member, firstSentenceTags,
//                i == 0, i == list.size() - 1);
//        }
        // FIXME - major change in b144
//        super.writeMemberSummaryFooter(classDoc);
    }
    
    /** This writes out the header for the block of information about
     * nested JML classes.
     * @param classDoc the class whose JML nested classes are to be described
     */
    public void writeJmlNestedClassSummaryHeader(@NonNull ClassDoc classDoc) {
        //printSummaryAnchor(cd);
        Utils.writeHeader(writer,this,classDoc,"JML Nested Model Class Summary",2);
    }

    /** This is overridden in order to include annotation information in the
     * nested class summary entry.  Immediately after this, the modifiers are written.
     * @param member the (class) Doc element whose annotation is to be printed
     */
    @Override
    protected void printModifier(@NonNull ProgramElementDoc member) {
        writer.writeAnnotationInfo(member);
        super.printModifier(member);
    }

}
