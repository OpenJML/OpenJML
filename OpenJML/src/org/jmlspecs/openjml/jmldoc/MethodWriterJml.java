package org.jmlspecs.openjml.jmldoc;

import java.io.Writer;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;

import org.jmlspecs.openjml.JmlCompiler;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.FieldDoc;
import com.sun.javadoc.MethodDoc;
import com.sun.javadoc.ProgramElementDoc;
import com.sun.javadoc.Tag;
import com.sun.javadoc.Type;
import com.sun.tools.doclets.formats.html.MethodWriterImpl;
import com.sun.tools.doclets.formats.html.SubWriterHolderWriter;
import com.sun.tools.doclets.internal.toolkit.util.DocFinder;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javadoc.ClassDocImpl;
import com.sun.tools.javadoc.FieldDocImpl;
import com.sun.tools.javadoc.MethodDocImpl;

public class MethodWriterJml extends MethodWriterImpl {

    protected ClassSymbol currentClassSym = null;

    /**
     * Construct a new MethodWriterImpl.
     *
     * @param writer the writer for the class that the methods belong to.
     * @param classDoc the class being documented.
     */
    public MethodWriterJml(SubWriterHolderWriter writer, ClassDoc classDoc) {
        super(writer, classDoc);
        currentClassSym = org.jmlspecs.openjml.jmldoc.Main.findNewClassSymbol(classdoc);
    }
    
    /**
     * Write the comments for the given method.
     *
     * @param method the method being documented.
     */

    public void writeTags(MethodDoc method) {
        super.writeTags(method);
        writeJmlSpecs(method);
    }
    
    public void writeJmlSpecs(MethodDoc method) {
        if (method instanceof MethodDocImpl) {
            MethodSymbol oldMethodSym = ((MethodDocImpl)method).sym;
            Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
            Name newMethodName = Name.Table.instance(context).fromString(oldMethodSym.name.toString());
            Scope.Entry e = currentClassSym.members().lookup(newMethodName);
            while (!(e.sym instanceof MethodSymbol) || !match((MethodSymbol)e.sym,oldMethodSym)) {
                e = e.sibling;
            }
            MethodSymbol newMethodSym = (MethodSymbol)e.sym;
            JmlMethodSpecs mspecs = JmlSpecs.instance(context).getSpecs(newMethodSym);
            if (mspecs != null) {
                writer.ddEnd(); // Only needed if there were actually inline comments // FIXME?
                writer.br(); // Need this if there is tag info, otherwise not // FIXME
                String s = Main.jmlAnnotations(writer,newMethodSym);
                if (Main.hasSpecs(mspecs) || !s.isEmpty()) {
                    bold("JML Method Specifications: "); 
                    writer.print(s);
                    writer.preNoNewLine();
                    for (JmlTree.JmlSpecificationCase cs: mspecs.cases) {
                        writer.print(cs);
                    }
                    writer.preEnd();
                }
                
                ClassSymbol c = currentClassSym;
                while (true) {
                    c = (ClassSymbol)c.getSuperclass().tsym;
                    if (c == null) break;
                    MethodSymbol m = findSameContext(newMethodSym,c);
                    if (m != null) {
                        mspecs = JmlSpecs.instance(context).getSpecs(m);
                        String ss = Main.jmlAnnotations(writer,newMethodSym);
                        if (Main.hasSpecs(mspecs) || !ss.isEmpty()) {
                            bold("JML Specifications inherited from " + c + ": "); 
                            writer.print(ss);
                            writer.preNoNewLine();
                            for (JmlTree.JmlSpecificationCase cs: mspecs.cases) {
                                writer.print(cs);
                            }
                            writer.preEnd();
                        }
                    }
                }
                // FIXME - find any inherited specs from interfaces
            }
        }
    }
    
    // CAUTION: The symbols are in different contexts
    public boolean match(MethodSymbol m, MethodSymbol mm) {
        if (!m.name.toString().equals(mm.name.toString())) return false;
        List<VarSymbol> mp = m.params();
        List<VarSymbol> mmp = mm.params();
        if (mp.size() != mmp.size()) return false;
        // Types are in different contexts FIXME
//        while (mp.tail != null) {
//            if (!mp.head.type.equals(mmp.head.type)) return false; // FIXME - is this how to compare types?
//            mp = mp.tail;
//            mmp = mmp.tail;
//        }
        return true;
    }
    
    public MethodSymbol findSameContext(MethodSymbol m, ClassSymbol c) {
        Scope.Entry e = c.members().lookup(m.name);
        while (e.sym != null) {
            Symbol s = e.sym;
            e = e.sibling;
            if (!(s instanceof MethodSymbol)) continue;
            MethodSymbol mm = (MethodSymbol)s;
            if (m.name != mm.name) continue;
            List<VarSymbol> mp = m.params();
            List<VarSymbol> mmp = mm.params();
            if (mp.size() != mmp.size()) continue;
            while (mp.tail != null) {
                if (!mp.head.type.equals(mmp.head.type)) continue; // FIXME - how to compare types?
                mp = mp.tail;
                mmp = mmp.tail;
            }
            return mm;
        }
        return null;
    }
    
    public void writeFooter(ClassDoc classDoc) {
        super.writeFooter(classDoc);
        writeJmlModelMethods(classDoc);
    }
    
    public void writeJmlModelMethods(ClassDoc classDoc) {
     // Hard coding this
//        <Header/>
//        <MethodDoc>
//            <MethodHeader/>
//            <Signature/>
//            <DeprecationInfo/>
//            <MethodComments/>
//            <TagInfo/>
//            <MethodFooter/>
//        </MethodDoc>
//        <Footer/>
      
      // Find model methods to see if we need to do anything at all
      LinkedList<JmlMethodDecl> list = new LinkedList<JmlMethodDecl>();
      TypeSpecs tspecs = JmlSpecs.instance(org.jmlspecs.openjml.jmldoc.Main.jmlContext).get(currentClassSym);
      for (JmlTypeClause tc: tspecs.clauses) {
          if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JmlMethodDecl) {
              JmlMethodDecl d = (JmlMethodDecl)((JmlTypeClauseDecl)tc).decl;
              //boolean use = JmlAttr.instance(org.jmlspecs.openjml.jmldoc.Main.jmlContext).findMod(d.mods,JmlToken.MODEL) != null;
              if (!d.sym.isConstructor()) {
                  list.add(d);
              }
          }
      }
      if (list.isEmpty()) return;
      
      // Header
      writer.printTableHeadingBackground("JML Model Method Detail");
      writer.println();
      
      //Field Header
      boolean isFirst = true;
      for (JmlMethodDecl tc: list) {
          MethodDoc md = new MethodDocImpl(((ClassDocImpl)classDoc).docenv(),tc.sym,"RAWDOCS",tc,null);
          // Method header
          writeMethodHeader(md,isFirst); isFirst = false;
          
          // signature
          writeSignature(md);
          
          // deprecation
          writeDeprecated(md);
          
          // field comments
          writeComments(classDoc,md);
          
          // tag info
          // FIXME writeTags(md);
          // instead for now
          writer.dl(); writer.dlEnd(); writeJmlSpecs(md);

          // Method footer
          writeMethodFooter();
      }
      
      
      //Footer
      super.writeFooter(classDoc);
      
        
    }

    public void writeMemberSummaryFooter(ClassDoc classDoc) {
        super.writeMemberSummaryFooter(classDoc);
        writeJmlMethodSummary(classDoc);
    }

    public void writeInheritedMemberSummaryFooter(ClassDoc classDoc) {
        writeJmlInheritedMemberSummaryFooter(classDoc);
        super.writeInheritedMemberSummaryFooter(classDoc);
    }
    
    public void writeJmlInheritedMemberSummaryFooter(ClassDoc classDoc) {
        ClassSymbol csym = Main.findNewClassSymbol(classDoc);
        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(csym);
        ArrayList<MethodDoc> list = new ArrayList<MethodDoc>();
        for (JmlTypeClause tc : tspecs.clauses) {
            // FIXME - check package and not in the same package
            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JCTree.JCMethodDecl) {
                MethodSymbol msym = ((JCTree.JCMethodDecl)((JmlTypeClauseDecl)tc).decl).sym;
                if (msym.isConstructor() || (msym.flags() & Flags.PRIVATE) != 0) continue;
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
    
    public void writeJmlMethodSummary(ClassDoc classDoc) {
        ArrayList<MethodDoc> list = new ArrayList<MethodDoc>();
        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(currentClassSym);
        for (JmlTypeClause tc : tspecs.clauses) {
            // FIXME - control visibility
            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JCTree.JCMethodDecl) {
                MethodSymbol msym = ((JCTree.JCMethodDecl)((JmlTypeClauseDecl)tc).decl).sym;
                if (!msym.isConstructor()) {
                    MethodDoc modelMethod = new MethodDocImpl(((ClassDocImpl)classDoc).docenv(),msym,"DOCCOMMENT",(JCTree.JCMethodDecl)((JmlTypeClauseDecl)tc).decl,null);
                    list.add(modelMethod);
                }
            }
        }
        if (list.isEmpty()) return;
        Collections.sort(list);
        writeJmlMethodSummaryHeader(classDoc);
        // The following loop is copied with modifications from MemberSummaryBuilder.buildSummary
        for (int i = 0; i<list.size(); i++) {
            MethodDoc member = list.get(i);
            Tag[] firstSentenceTags = member.firstSentenceTags();
            if (firstSentenceTags.length == 0) {
                //Inherit comments from overridden or implemented method if
                //necessary.
                DocFinder.Output inheritedDoc =
                    DocFinder.search(new DocFinder.Input((MethodDoc) member));
                if (inheritedDoc.holder != null &&
                        inheritedDoc.holder.firstSentenceTags().length > 0) {
                    firstSentenceTags = inheritedDoc.holder.firstSentenceTags();
                }
            }
            writeMemberSummary(classDoc, member, firstSentenceTags,
                i == 0, i == list.size() - 1);
        }
        super.writeMemberSummaryFooter(classDoc);
    }
    
    public void writeJmlMethodSummaryHeader(ClassDoc classDoc) {
        //printSummaryAnchor(cd);
        writer.tableIndexSummary();
        writer.tableHeaderStart("#CCCCFF");
        writer.bold("JML Model Method Summary");
        writer.tableHeaderEnd();
    }
}
