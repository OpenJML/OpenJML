package org.jmlspecs.openjml.jmldoc;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.ConstructorDoc;
import com.sun.javadoc.MethodDoc;
import com.sun.javadoc.Tag;
import com.sun.tools.doclets.formats.html.ConstructorWriterImpl;
import com.sun.tools.doclets.formats.html.SubWriterHolderWriter;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javadoc.ClassDocImpl;
import com.sun.tools.javadoc.ConstructorDocImpl;
import com.sun.tools.javadoc.MethodDocImpl;

public class ConstructorWriterJml extends ConstructorWriterImpl {

    protected ClassSymbol currentClassSym;

    public ConstructorWriterJml(SubWriterHolderWriter writer,
            ClassDoc classdoc) {
        super(writer, classdoc);
        currentClassSym = org.jmlspecs.openjml.jmldoc.Main.findNewClassSymbol(classdoc);
    }

    /** Overrides the super class method in order to write out any specs after the tags */
    public void writeTags(ConstructorDoc method) {
        super.writeTags(method);
        writeJmlSpecs(method);
    }
    
    public void writeJmlSpecs(ConstructorDoc method) {
        if (method instanceof ConstructorDocImpl) {
            MethodSymbol oldMethodSym = ((ConstructorDocImpl)method).sym;
            Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
            Name newMethodName = Name.Table.instance(context).fromString(oldMethodSym.name.toString());
            Scope.Entry e = currentClassSym.members().lookup(newMethodName);
            while (!(e.sym instanceof MethodSymbol) || !match((MethodSymbol)e.sym,oldMethodSym)) {
                e = e.sibling;
            }
            MethodSymbol newMethodSym = (MethodSymbol)e.sym;
            JmlMethodSpecs mspecs = JmlSpecs.instance(context).getSpecs(newMethodSym);
            if (mspecs != null) {
                writer.ddEnd(); // Only needed if there were actually inline comments
                writer.br(); // Need this if there is tag info, otherwise not // FIXME
                String s = Main.jmlAnnotations(writer,newMethodSym);
                if (Main.hasSpecs(mspecs) || !s.isEmpty()) {
                    bold("JML Constructor Specifications: "); 
                    writer.print(s);
                    writer.preNoNewLine();
                    for (JmlTree.JmlSpecificationCase cs: mspecs.cases) {
                        writer.print(cs);
                    }
                    writer.preEnd();
                }
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
        writeJmlModelConstructors(classDoc);
    }
    
    public void writeJmlModelConstructors(ClassDoc classDoc) {
     // Hard coding this
//        <ConstructorDetails>
//        <Header/>
//        <ConstructorDoc>
//            <ConstructorHeader/>
//            <Signature/>
//            <DeprecationInfo/>
//            <ConstructorComments/>
//            <TagInfo/>
//            <ConstructorFooter/>
//        </ConstructorDoc>
//        <Footer/>
//    </ConstructorDetails>
//      
      // Find model methods to see if we need to do anything at all
      LinkedList<JmlMethodDecl> list = new LinkedList<JmlMethodDecl>();
      TypeSpecs tspecs = JmlSpecs.instance(org.jmlspecs.openjml.jmldoc.Main.jmlContext).get(currentClassSym);
      for (JmlTypeClause tc: tspecs.clauses) {
          if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JmlMethodDecl) {
              JmlMethodDecl d = (JmlMethodDecl)((JmlTypeClauseDecl)tc).decl;
              //boolean use = JmlAttr.instance(org.jmlspecs.openjml.jmldoc.Main.jmlContext).findMod(d.mods,JmlToken.MODEL) != null;
              if (d.sym.isConstructor()) {
                  list.add(d);
              }
          }
      }
      if (list.isEmpty()) return;
      
      // Header
      writer.printTableHeadingBackground("JML Model Constructor Detail");
      writer.println();
      
      boolean isFirst = true;
      for (JmlMethodDecl tc: list) {
          ConstructorDoc md = new ConstructorDocImpl(((ClassDocImpl)classDoc).docenv(),tc.sym,"RAWDOCS",tc,null);
          // Method header
          writeConstructorHeader(md,isFirst); isFirst = false;
          
          // signature
          writeSignature(md);
          
          // deprecation
          writeDeprecated(md);
          
          // field comments
          writeComments(md);
          
          // tag info
          // FIXME super.writeTags(md);
          writeJmlSpecs(md);
          
          // Method footer
          writeConstructorFooter();
      }
      
      
      //Footer
      super.writeFooter(classDoc);
      
        
    }

    public void writeMemberSummaryFooter(ClassDoc classDoc) {
        super.writeMemberSummaryFooter(classDoc);
        writeJmlConstructorSummary(classDoc);
    }

    // There are no inherited constructors
    
//    public void writeInheritedMemberSummaryFooter(ClassDoc classDoc) {
//        //writeJmlInheritedNestedClassSummaryFooter(classDoc);
//        super.writeInheritedMemberSummaryFooter(classDoc);
//    }
    
//    public void writeJmlInheritedNestedClassSummaryFooter(ClassDoc classDoc) {
//        ClassSymbol csym = Main.findNewClassSymbol(classDoc);
//        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(csym);
//        ArrayList<MethodDoc> list = new ArrayList<MethodDoc>();
//        for (JmlTypeClause tc : tspecs.clauses) {
//            // FIXME - check package and not in the same package
//            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JCTree.JCMethodDecl) {
//                MethodSymbol msym = ((JCTree.JCMethodDecl)((JmlTypeClauseDecl)tc).decl).sym;
//                if ((msym.flags() & Flags.PRIVATE) != 0) continue;
//                MethodDoc modelMethod = new MethodDocImpl(((ClassDocImpl)classDoc).docenv(),msym,"DOCCOMMENT",(JCTree.JCMethodDecl)((JmlTypeClauseDecl)tc).decl,null);
//                list.add(modelMethod);
//            }
//        }
//        
//        if (!list.isEmpty()) {
//            writer.br();
//            writer.bold("Inherited JML model methods: ");
//            Collections.sort(list);
//            boolean isFirst = true;
//            for (MethodDoc method: list) {
//                writer.printInheritedSummaryMember(this, classDoc, method, isFirst);
//                isFirst = false;
//            }
//        }
//    }
    
    public void writeJmlConstructorSummary(ClassDoc classDoc) {
        ArrayList<ConstructorDoc> list = new ArrayList<ConstructorDoc>();
        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(currentClassSym);
        for (JmlTypeClause tc : tspecs.clauses) {
            // FIXME - control visibility
            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JCTree.JCMethodDecl) {
                MethodSymbol msym = ((JCTree.JCMethodDecl)((JmlTypeClauseDecl)tc).decl).sym;
                if (msym.isConstructor()) {
                    ConstructorDoc constructor = new ConstructorDocImpl(((ClassDocImpl)classDoc).docenv(),msym,"DOCCOMMENT",(JCTree.JCMethodDecl)((JmlTypeClauseDecl)tc).decl,null);
                    list.add(constructor);
                }
            }
        }
        if (list.isEmpty()) return;
        Collections.sort(list);
        writeJmlConstructorSummaryHeader(classDoc);
        // The following loop is copied with modifications from MemberSummaryBuilder.buildSummary
        for (int i = 0; i<list.size(); i++) {
            ConstructorDoc member = list.get(i);
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
    
    public void writeJmlConstructorSummaryHeader(ClassDoc classDoc) {
        //printSummaryAnchor(cd);
        writer.tableIndexSummary();
        writer.tableHeaderStart("#CCCCFF");
        bold("JML Model Constructor Summary");
        writer.tableHeaderEnd();
    }


}
