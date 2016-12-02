package org.jmlspecs.openjml.jmldoc;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.FieldDoc;
import com.sun.javadoc.ProgramElementDoc;
import com.sun.javadoc.Tag;
import com.sun.tools.doclets.formats.html.FieldWriterImpl;
import com.sun.tools.doclets.formats.html.SubWriterHolderWriter;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javadoc.ClassDocImpl;
import com.sun.tools.javadoc.DocEnv;
import com.sun.tools.javadoc.FieldDocImpl;

/**
 * This class extends its Javadoc parent class in order to write out any JML
 * specifications associated with fields.
 * 
 * @author David R. Cok
 */
public class FieldWriterJml extends FieldWriterImpl {

    /** Constructor for this JML-enabled writer of field documentation.
     * 
     * @param writer the writer to which writing is delegated
     * @param classdoc the class that owns the fields being described
     */
    //@ ensures this.classdoc == classdoc;
    public FieldWriterJml(@NonNull SubWriterHolderWriter writer, @NonNull ClassDoc classdoc) {
        super(writer, classdoc);
        currentClassSym = Utils.findNewClassSymbol(classdoc);
    }

    /** Constructor for this JML-enabled writer of field documentation.
     * 
     * @param writer the writer to which writing is delegated
     */
    public FieldWriterJml(@NonNull SubWriterHolderWriter writer) {
        super(writer);
        currentClassSym = Utils.findNewClassSymbol(classdoc);
    }
    
    /** The ClassSymbol (in the JML compilation context) of the class
     * whose nested classes are being described.
     */
    protected @NonNull ClassSymbol currentClassSym;
    
    /** Set to true if the JML field is a model field, false if it is ghost or Java field. */
    boolean isModel = false;

    // FIXME - major change in b144
//    /** Overrides the parent class method in order to write out any JML specs
//     * after writing out the comments about the field.
//     */
//    public void writeComments(@NonNull FieldDoc field) {
//        super.writeComments(field);
//        writeJmlSpecs(field);
//    }
    
    /** Writes out the JML specs about the field. 
     * @param field the field to describe
     */
    public void writeJmlSpecs(@NonNull FieldDoc field) {
        Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
        Name newFieldName = Names.instance(context).fromString(field.name());
        VarSymbol newField = (VarSymbol)currentClassSym.members().lookup(newFieldName).sym;
        //System.out.println("Sym " + newField + " for " + newFieldName + " in " + currentClassSym);
        if (newField == null) return; // Inherited Java fxields?
        
        JmlSpecs.FieldSpecs fspecs = JmlSpecs.instance(context).getSpecs(newField);
        // FIXME - if the only specs are represent clauses, this won't print them
        String s = Utils.jmlAnnotations(newField);
        if (fspecs != null && (!fspecs.list.isEmpty() || s.length()!=0) ){  // FIXME - what if there are JML annotations but no clauses
            strong("JML Specifications: ");
            writer.print(s);
            writer.dl();
            writer.preNoNewLine();
            for (JmlTree.JmlTypeClause clause: fspecs.list) {
                writer.print("    ");
                writer.print(clause);
                writer.println();
            }
            if (isModel) {
                TypeSpecs tspecs = JmlSpecs.instance(context).get(currentClassSym);
                for (JmlTypeClause t : tspecs.clauses) {
                    if (!(t instanceof JmlTypeClauseRepresents)) continue;
                    JmlTypeClauseRepresents tr = (JmlTypeClauseRepresents)t;
                    if (!(tr.ident instanceof JCTree.JCIdent)) continue;
                    Name n = ((JCTree.JCIdent)(tr.ident)).name;
                    if (n == newFieldName) {
                        writer.print("    ");
                        writer.print(JmlPretty.write(t,false));
                        writer.println();
                    }
                }

            }

            writer.preEnd();
            writer.dlEnd();
        }
    }

    // FIXME - major change in b144
//    /**
//     * Write the footer for the field documentation, and then add any
//     * field detail information about ghost and model fields.
//     *
//     * @param classDoc the class that the fields belong to.
//     */
//    public void writeFooter(@NonNull ClassDoc classDoc) {
//        super.writeFooter(classDoc);
//        writeJmlGhostModelFieldDetail(classDoc,JmlToken.GHOST,"Ghost");
//        writeJmlGhostModelFieldDetail(classDoc,JmlToken.MODEL,"Model");
//        writeJmlRepresentsDetail(classDoc);
//    }
    
    public void writeJmlGhostModelFieldDetail(@NonNull ClassDoc classDoc,
            @NonNull JmlTokenKind token,String showString) {
// Hard coding this
//        <Header/>
//        <FieldDoc>
//            <FieldHeader/>
//            <Signature/>
//            <DeprecationInfo/>
//            <FieldComments/>
//            <TagInfo/>
//            <FieldFooter/>
//        </FieldDoc>
//        <Footer/>

        DocEnv denv = ((ClassDocImpl)classDoc).docenv();

        // Find ghost fields to see if we need to do anything at all
        LinkedList<JmlVariableDecl> list = new LinkedList<JmlVariableDecl>();
        TypeSpecs tspecs = JmlSpecs.instance(org.jmlspecs.openjml.jmldoc.Main.jmlContext).get(currentClassSym);
        for (JmlTypeClause tc: tspecs.decls) {
            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JmlVariableDecl) {
                JmlVariableDecl d = (JmlVariableDecl)((JmlTypeClauseDecl)tc).decl;
                boolean use = JmlAttr.instance(org.jmlspecs.openjml.jmldoc.Main.jmlContext).findMod(d.mods,token) != null;
                if (use && denv.shouldDocument(d.sym)) {
                    list.add(d);
                }
            }
        }
        if (list.isEmpty()) return;
        
        // Header
        writer.printTableHeadingBackground("JML " + showString + " Field Detail");
        writer.println();
        
        //Field Header
        boolean isFirst = true;
        // FIXME - major change in b144
//        for (JmlVariableDecl tc: list) {
//            FieldDoc fd = new FieldDocImpl(((ClassDocImpl)classDoc).docenv(),tc.sym,tc.docComment,tc,null);
//            // field header
//            writeFieldHeader(fd,isFirst); isFirst = false;
//            
//            // signature
//            writeSignature(fd);
//            
//            // deprecation
//            writeDeprecated(fd);
//            
//            // field comments
//            isModel = token == JmlToken.MODEL;
//            try {
//                //writeComments(fd);
//                // Extract some of the contents of writeComments to avoid some
//                // problems with the dual contexts - in particular, a field looks
//                // like it is inherited from a class or interface
//                writer.dd();
//                writer.printInlineComment(fd);
//                writeJmlSpecs(fd);
//                writer.ddEnd();
//            } finally {
//                isModel = false;
//            }
//            
//            // tag info
//            writeTags(fd);
//
//            // Field footer
//            writeFieldFooter();
//        }
//        
//        
//        //Footer
//        super.writeFooter(classDoc);
        
    }
    
    public java.util.List<JmlTypeClauseRepresents> makeRepresentsList(ClassDoc classDoc) {
        java.util.List<JmlTypeClauseRepresents> list = new java.util.LinkedList<JmlTypeClauseRepresents>();
        TypeSpecs tspecs = JmlSpecs.instance(org.jmlspecs.openjml.jmldoc.Main.jmlContext).get(currentClassSym);
        for (JmlTypeClause t : tspecs.clauses) {
            if (!(t instanceof JmlTypeClauseRepresents)) continue;
            JmlTypeClauseRepresents tr = (JmlTypeClauseRepresents)t;
            if (!(tr.ident instanceof JCTree.JCIdent)) continue;
            boolean found = false;
            for (JmlTypeClause tc: tspecs.decls) {
                // FIXME - only model fields
                // FIXME - only only fields that are in classDoc if it is not null
                if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JmlVariableDecl) {
                    JmlVariableDecl d = (JmlVariableDecl)((JmlTypeClauseDecl)tc).decl;
                    if (d.name.equals(((JCTree.JCIdent)tr.ident).name)) {
                        found = true;
                        break;
                    }
                }
            }
            if (!found) list.add(tr);
        }
        return list;
    }
    
    /** This writes out a documentation block containing detail on any represents
     * clauses for model fields in parent classes
     * @param classDoc the class in which the represents clauses appear
     */
    public void writeJmlRepresentsDetail(ClassDoc classDoc) {
        java.util.List<JmlTypeClauseRepresents> list = makeRepresentsList(null);
        
        if (list.isEmpty()) return;
        
        // FIXME - do this as a two-column table to align the columns
        writer.anchor("JmlRepresentsClauses");
        writer.printTableHeadingBackground("Represents clauses for parent class model fields");
        writer.println();
        writer.code();
        writer.br();
        for (JmlTypeClauseRepresents tr : list) {
            writer.print("&nbsp;&nbsp;&nbsp;&nbsp;");
            writer.print(linkedName((JCTree.JCIdent)tr.ident));
            writer.print(": ");
            writer.println(JmlPretty.write(tr,false));
            writer.br();
        }
        writer.br();
        writer.codeEnd();
        // FIXME - major change in b144
//        super.writeFooter(classDoc);
       
    }
    
    // FIXME - fix this link - problem is that the stuff in the represents clause
    // is not attributed, so we don't know which class it comes from.
    // We could do a lookup I suppose???
    /** Returns the HTML that links this id to its own HTML page
     * @param id the id to link
     * @return the String giving the link in HTML
     */
    public String linkedName(JCTree.JCIdent id) {
        return "<A HREF=\"   \">" +
                JmlPretty.write(id,false) +
                "</A>";
    }
    
    /** Writes out a block of HTML that documents any represents clauses for
     * model fields that are not in this class
     * @param classDoc the base class - ignore represents for fields in this class
     */
    public void writeJmlRepresentsSummary(ClassDoc classDoc) {
        java.util.List<JmlTypeClauseRepresents> list = makeRepresentsList(classDoc);
        
        if (list.isEmpty()) return;
        
        writer.br();
        writer.strong("<A HREF=\"#JmlRepresentsClauses\">Represents specification of super class fields</A>: ");
        //Collections.sort(list);
        // FIXME - major change in b144
//        boolean isFirst = true;
//        for (JmlTypeClauseRepresents tr: list) {
//            FieldDoc field = new FieldDocImpl(((ClassDocImpl)classDoc).docenv(),(VarSymbol)((JCTree.JCIdent)tr.ident).sym);
//            writer.printInheritedSummaryMember(this, classDoc, field, isFirst);
//            isFirst = false;
//        }
//        super.writeInheritedMemberSummaryFooter(classDoc);
    }
    
    /** This is overridden in order to include annotation information in the
     * field summary entry.  Immediately after this, the modifiers are written.
     * @param member the (field) Doc element whose annotation is to be printed
     */
    @Override
    protected void printModifier(@NonNull ProgramElementDoc member) {
        writer.writeAnnotationInfo(member);
        super.printModifier(member);
    }

    // FIXME - major change in b144
//    /** This is overridden in order to write out the summary footer and to 
//     * follow it by the summary of JML fields.
//     * @param classDoc the class that owns the fields
//     */
//    @Override
//    public void writeMemberSummaryFooter(@NonNull ClassDoc classDoc) {
//        super.writeMemberSummaryFooter(classDoc);
//        writeJmlFieldSummary(classDoc);
//    }
    
    public void checkJmlSummary(@NonNull ClassDoc classDoc) {
        if (summaryHeaderWritten) return;
        writeJmlFieldSummary(classDoc);
    }
    


    // FIXME - major change in b144
//    /** This is overridden in order to write out the summary footer for
//     * inherited fields and to 
//     * follow it by the summary of JML inherited fields.
//     * @param classDoc the class whose inherited fields are to be described
//     */
//    public void writeInheritedMemberSummaryFooter(@NonNull ClassDoc classDoc) {
//        writeJmlInheritedMemberSummary(classDoc);
//        writeJmlRepresentsSummary(classDoc);
//        super.writeInheritedMemberSummaryFooter(classDoc);
//    }
//    
//    public void checkJmlInheritedSummary(@NonNull ClassDoc classDoc, java.util.List inhmembers) {
//        if (summaryHeaderWritten) return;
//        super.writeInheritedMemberSummaryHeader(classDoc);
//        writeInheritedMemberSummaryFooter(classDoc);
//    }
    

    
    /** This writes out summary information about JML fields. 
     * @param classDoc the class whose inherited fields are to be described. 
     * */
    public void writeJmlInheritedMemberSummary(@NonNull ClassDoc classDoc) {
        ClassSymbol csym = Utils.findNewClassSymbol(classDoc);
        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(csym);
        DocEnv denv = ((ClassDocImpl)classDoc).docenv();
        ArrayList<FieldDoc> list = new ArrayList<FieldDoc>();
        for (JmlTypeClause tc : tspecs.decls) {
            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JCTree.JCVariableDecl) {
                JmlVariableDecl vdecl = ((JmlVariableDecl)((JmlTypeClauseDecl)tc).decl);
                VarSymbol msym = vdecl.sym;
                if (!denv.shouldDocument(msym)) continue;
                if (!Utils.isInherited(msym,currentClassSym)) continue;
                FieldDoc field = new FieldDocImpl(((ClassDocImpl)classDoc).docenv(),msym,vdecl.docComment,vdecl,null);
                list.add(field);
            }
        }
        
        // FIXME - major change in b144
//        if (!list.isEmpty()) {
//            writer.br();
//            writer.strong("Inherited JML ghost and model fields: ");
//            Collections.sort(list);
//            boolean isFirst = true;
//            for (FieldDoc field: list) {
//                writer.printInheritedSummaryMember(this, classDoc, field, isFirst);
//                isFirst = false;
//            }
//        }
    }
    
    /** Write out a summary of JML fields for the given class 
     * 
     * @param classDoc the class whose JML fields are to be written
     */
    public void writeJmlFieldSummary(@NonNull ClassDoc classDoc) {
        ArrayList<FieldDoc> list = new ArrayList<FieldDoc>();
        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(currentClassSym);
        DocEnv denv = ((ClassDocImpl)classDoc).docenv();
        for (JmlTypeClause tc : tspecs.decls) {
            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JCTree.JCVariableDecl) {
                JmlVariableDecl vdecl = ((JmlVariableDecl)((JmlTypeClauseDecl)tc).decl);
                VarSymbol msym = vdecl.sym;
                if (!denv.shouldDocument(msym)) continue;
                FieldDoc field = new FieldDocImpl(denv,msym,vdecl.docComment,vdecl,null);
                list.add(field);
            }
        }
        if (list.isEmpty()) return;
        Collections.sort(list);
        writeJmlFieldSummaryHeader(classDoc);
        // The following loop is copied with modifications from MemberSummaryBuilder.buildSummary ??? FIXME
        // FIXME - major change in b144
//        for (int i = 0; i<list.size(); i++) {
//            FieldDoc member = list.get(i);
//            Tag[] firstSentenceTags = member.firstSentenceTags();
//            writeMemberSummary(classDoc, member, firstSentenceTags,
//                i == 0, i == list.size() - 1);
//        }
//        super.writeMemberSummaryFooter(classDoc);
    }
    
    /** This writes the header for the summary of JML ghost and model fields
     * 
     * @param classDoc the class whose ghost and model fields are to be described
     */
    public void writeJmlFieldSummaryHeader(@NonNull ClassDoc classDoc) {
        //printSummaryAnchor(cd);
        Utils.writeHeader(writer,this,classDoc,"JML Ghost and Model Field Summary",2);
        summaryHeaderWritten = true;
    }
    
    protected boolean summaryHeaderWritten = false;
}
