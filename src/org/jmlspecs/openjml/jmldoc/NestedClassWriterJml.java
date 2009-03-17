package org.jmlspecs.openjml.jmldoc;

import java.util.ArrayList;
import java.util.Collections;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.MethodDoc;
import com.sun.javadoc.Tag;
import com.sun.tools.doclets.formats.html.NestedClassWriterImpl;
import com.sun.tools.doclets.formats.html.SubWriterHolderWriter;
import com.sun.tools.doclets.internal.toolkit.util.DocFinder;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javadoc.ClassDocImpl;
import com.sun.tools.javadoc.MethodDocImpl;

public class NestedClassWriterJml extends NestedClassWriterImpl {

    protected ClassSymbol currentClassSym;

    public NestedClassWriterJml(SubWriterHolderWriter writer,
            ClassDoc classdoc) {
        super(writer, classdoc);
        currentClassSym = org.jmlspecs.openjml.jmldoc.Main.findNewClassSymbol(classdoc);
    }
    
    public void writeMemberSummaryFooter(ClassDoc classDoc) {
        super.writeMemberSummaryFooter(classDoc);
        writeJmlNestedClassSummary(classDoc);
    }

    public void writeInheritedMemberSummaryFooter(ClassDoc classDoc) {
        writeJmlInheritedNestedClassSummaryFooter(classDoc);
        super.writeInheritedMemberSummaryFooter(classDoc);
    }
    
    public void writeJmlInheritedNestedClassSummaryFooter(ClassDoc classDoc) {
        ClassSymbol csym = Main.findNewClassSymbol(classDoc);
        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(csym);
        ArrayList<MethodDoc> list = new ArrayList<MethodDoc>();
        for (JmlTypeClause tc : tspecs.clauses) {
            // FIXME - check package and not in the same package
            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JCTree.JCMethodDecl) {
                MethodSymbol msym = ((JCTree.JCMethodDecl)((JmlTypeClauseDecl)tc).decl).sym;
                if ((msym.flags() & Flags.PRIVATE) != 0) continue;
                MethodDoc modelMethod = new MethodDocImpl(((ClassDocImpl)classDoc).docenv(),msym,"DOCCOMMENT",(JCTree.JCMethodDecl)((JmlTypeClauseDecl)tc).decl,null);
                list.add(modelMethod);
            }
        }
        
        if (!list.isEmpty()) {
            writer.br();
            writer.bold("Inherited JML model methods: ");
            Collections.sort(list);
            boolean isFirst = true;
            for (MethodDoc method: list) {
                writer.printInheritedSummaryMember(this, classDoc, method, isFirst);
                isFirst = false;
            }
        }
    }
    
    public void writeJmlNestedClassSummary(ClassDoc classDoc) {
        ArrayList<ClassDoc> list = new ArrayList<ClassDoc>();
        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(currentClassSym);
        for (JmlTypeClause tc : tspecs.clauses) {
            // FIXME - control visibility
            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JCTree.JCClassDecl) {
                ClassSymbol msym = ((JCTree.JCClassDecl)((JmlTypeClauseDecl)tc).decl).sym;
                ClassDoc modelClass = new ClassDocImpl(((ClassDocImpl)classDoc).docenv(),msym,"DOCCOMMENT",(JCTree.JCClassDecl)((JmlTypeClauseDecl)tc).decl,null);
                list.add(modelClass);
            }
        }
        if (list.isEmpty()) return;
        Collections.sort(list);
        writeJmlNestedClassSummaryHeader(classDoc);
        // The following loop is copied with modifications from MemberSummaryBuilder.buildSummary
        for (int i = 0; i<list.size(); i++) {
            ClassDoc member = list.get(i);
            Tag[] firstSentenceTags = member.firstSentenceTags();
//            if (firstSentenceTags.length == 0) {
//                //Inherit comments from overridden or implemented method if
//                //necessary.
//                DocFinder.Output inheritedDoc =
//                    DocFinder.search(new DocFinder.Input(member));
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
    
    public void writeJmlNestedClassSummaryHeader(ClassDoc classDoc) {
        //printSummaryAnchor(cd);
        writer.tableIndexSummary();
        writer.tableHeaderStart("#CCCCFF");
        bold("JML Nested Model Class Summary");
        writer.tableHeaderEnd();
    }


}
