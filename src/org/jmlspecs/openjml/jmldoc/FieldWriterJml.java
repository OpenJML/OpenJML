package org.jmlspecs.openjml.jmldoc;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.FieldDoc;
import com.sun.javadoc.Tag;
import com.sun.tools.doclets.formats.html.FieldWriterImpl;
import com.sun.tools.doclets.formats.html.SubWriterHolderWriter;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javadoc.ClassDocImpl;
import com.sun.tools.javadoc.FieldDocImpl;

public class FieldWriterJml extends FieldWriterImpl {

    public FieldWriterJml(SubWriterHolderWriter writer, ClassDoc classdoc) {
        super(writer, classdoc);
        currentClassSym = org.jmlspecs.openjml.jmldoc.Main.findNewClassSymbol(classdoc);
    }

    public FieldWriterJml(SubWriterHolderWriter writer) {
        super(writer);
        currentClassSym = org.jmlspecs.openjml.jmldoc.Main.findNewClassSymbol(classdoc);
    }
    
    protected ClassSymbol currentClassSym;
    boolean isModel = false;
    
    public void writeComments(FieldDoc field) {
        super.writeComments(field);
        writeJmlSpecs(field);
    }
    
    public void writeJmlSpecs(FieldDoc field) {
        //if (field instanceof FieldDocImpl) {
            Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
            Name newFieldName = Name.Table.instance(context).fromString(field.name());
            VarSymbol newField = (VarSymbol)currentClassSym.members().lookup(newFieldName).sym;
            JmlSpecs.FieldSpecs fspecs = JmlSpecs.instance(context).getSpecs(newField);
            // FIXME - if the only specs are represent clauses, this won't print them
            String s = org.jmlspecs.openjml.jmldoc.Main.jmlAnnotations(writer,newField);
            if (fspecs != null && (!fspecs.list.isEmpty() || !s.isEmpty()) ){  // FIXME - what if there are JML annotations but no clauses
                bold("JML Specifications: ");
                writer.print(s);
                writer.dl();
                writer.preNoNewLine();
                for (JmlTree.JmlTypeClause clause: fspecs.list) {
                    writer.print(clause);
                }
                if (isModel) {
                    TypeSpecs tspecs = JmlSpecs.instance(context).get(currentClassSym);
                    for (JmlTypeClause t : tspecs.clauses) {
                        if (!(t instanceof JmlTypeClauseRepresents)) continue;
                        JmlTypeClauseRepresents tr = (JmlTypeClauseRepresents)t;
                        if (!(tr.ident instanceof JCTree.JCIdent)) continue;
                            Name n = ((JCTree.JCIdent)(tr.ident)).name;
                            if (n == newFieldName) {
                                writer.print(t);
                            }
                    }
                    
                }

                writer.preEnd();
                writer.dlEnd();
            }
        //}
    }

    /**
     * Write the footer for the field documentation.
     *
     * @param classDoc the class that the fields belong to.
     */
    public void writeFooter(ClassDoc classDoc) {
        super.writeFooter(classDoc);
        writeJmlGhostModelFieldDetail(classDoc,JmlToken.GHOST,"Ghost");
        writeJmlGhostModelFieldDetail(classDoc,JmlToken.MODEL,"Model");
    }
    
    public void writeJmlGhostModelFieldDetail(ClassDoc classDoc,JmlToken token,String showString) {
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
        
        // Find ghost fields to see if we need to do anything at all
        LinkedList<JmlVariableDecl> list = new LinkedList<JmlVariableDecl>();
        TypeSpecs tspecs = JmlSpecs.instance(org.jmlspecs.openjml.jmldoc.Main.jmlContext).get(currentClassSym);
        for (JmlTypeClause tc: tspecs.clauses) {
            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JmlVariableDecl) {
                JmlVariableDecl d = (JmlVariableDecl)((JmlTypeClauseDecl)tc).decl;
                boolean use = JmlAttr.instance(org.jmlspecs.openjml.jmldoc.Main.jmlContext).findMod(d.mods,token) != null;
                if (use) {
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
        for (JmlVariableDecl tc: list) {
            FieldDoc fd = new FieldDocImpl(((ClassDocImpl)classDoc).docenv(),tc.sym,"RAWDOCS",tc,null);
            // field header
            writeFieldHeader(fd,isFirst); isFirst = false;
            
            // signature
            writeSignature(fd);
            
            // deprecation
            writeDeprecated(fd);
            
            // field comments
            isModel = token == JmlToken.MODEL;
            try {
                //writeComments(fd);
                // Extract some of the contents of writeComments to avoid some
                // problems with the dual contexts - in particular, a field looks
                // like it is inherited from a class or interface
                writer.dd();
                writer.printInlineComment(fd);
                writeJmlSpecs(fd);
            } finally {
                isModel = false;
            }
            
            // tag info
            writeTags(fd);

            // Field footer
            writeFieldFooter();
        }
        
        
        //Footer
        super.writeFooter(classDoc);
        
    }

    public void writeMemberSummaryFooter(ClassDoc classDoc) {
        super.writeMemberSummaryFooter(classDoc);
        writeJmlFieldSummary(classDoc);
    }

    public void writeInheritedMemberSummaryFooter(ClassDoc classDoc) {
        ClassSymbol csym = Main.findNewClassSymbol(classDoc);
        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(csym);
        ArrayList<FieldDoc> list = new ArrayList<FieldDoc>();
        for (JmlTypeClause tc : tspecs.clauses) {
            // FIXME - check package and not in the same package
            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JCTree.JCVariableDecl) {
                VarSymbol msym = ((JCTree.JCVariableDecl)((JmlTypeClauseDecl)tc).decl).sym;
                if ((msym.flags() & Flags.PRIVATE) != 0) continue;
                FieldDoc field = new FieldDocImpl(((ClassDocImpl)classDoc).docenv(),msym,"DOCCOMMENT",(JCTree.JCVariableDecl)((JmlTypeClauseDecl)tc).decl,null);
                list.add(field);
            }
        }
        
        if (!list.isEmpty()) {
            writer.br();
            writer.bold("Inherited JML ghost and model fields: ");
            Collections.sort(list);
            boolean isFirst = true;
            for (FieldDoc field: list) {
                writer.printInheritedSummaryMember(this, classDoc, field, isFirst);
                isFirst = false;
            }
        }
        super.writeInheritedMemberSummaryFooter(classDoc);
    }
    
    public void writeJmlFieldSummary(ClassDoc classDoc) {
        ArrayList<FieldDoc> list = new ArrayList<FieldDoc>();
        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(currentClassSym);
        for (JmlTypeClause tc : tspecs.clauses) {
            // FIXME - control visibility
            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JCTree.JCVariableDecl) {
                VarSymbol msym = ((JCTree.JCVariableDecl)((JmlTypeClauseDecl)tc).decl).sym;
                FieldDoc field = new FieldDocImpl(((ClassDocImpl)classDoc).docenv(),msym,"DOCCOMMENT",(JCTree.JCVariableDecl)((JmlTypeClauseDecl)tc).decl,null);
                list.add(field);
            }
        }
        if (list.isEmpty()) return;
        Collections.sort(list);
        writeJmlFieldSummaryHeader(classDoc);
        // The following loop is copied with modifications from MemberSummaryBuilder.buildSummary ??? FIXME
        for (int i = 0; i<list.size(); i++) {
            FieldDoc member = list.get(i);
            Tag[] firstSentenceTags = member.firstSentenceTags();
//            if (firstSentenceTags.length == 0) {
//                //Inherit comments from overridden or implemented method if
//                //necessary.
//                DocFinder.Output inheritedDoc =
//                    DocFinder.search(new DocFinder.Input((MethodDoc) member));
//                if (inheritedDoc.holder != null &&
//                        inheritedDoc.holder.firstSentenceTags().length > 0) {
//                    firstSentenceTags = inheritedDoc.holder.firstSentenceTags();
//                }
//            }
            writeMemberSummary(classDoc, member, firstSentenceTags,
                i == 0, i == list.size() - 1);
        }
        super.writeMemberSummaryFooter(classDoc);
    }
    
    public void writeJmlFieldSummaryHeader(ClassDoc classDoc) {
        //printSummaryAnchor(cd);
        writer.tableIndexSummary();
        writer.tableHeaderStart("#CCCCFF");
        writer.bold("JML Ghost and Model Field Summary");
        writer.tableHeaderEnd();
    }


}
