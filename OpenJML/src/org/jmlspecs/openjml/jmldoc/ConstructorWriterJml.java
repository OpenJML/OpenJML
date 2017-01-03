package org.jmlspecs.openjml.jmldoc;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;

import org.jmlspecs.annotation.*;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.ConstructorDoc;
import com.sun.javadoc.ExecutableMemberDoc;
import com.sun.javadoc.ProgramElementDoc;
import com.sun.javadoc.Tag;
import com.sun.tools.doclets.formats.html.ConstructorWriterImpl;
import com.sun.tools.doclets.formats.html.SubWriterHolderWriter;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javadoc.ClassDocImpl;
import com.sun.tools.javadoc.ConstructorDocImpl;
import com.sun.tools.javadoc.DocEnv;

/**
 * This class extends its parent in order to write out documentation about (a)
 * model constructors and (b) the JML specifications of constructors and model
 * constructors.
 * 
 * @author David R. Cok
 */
public class ConstructorWriterJml extends ConstructorWriterImpl {

    /** The Symbol of the class (in the JML compilation context) that owns
     * these constructors.
     */
    protected @NonNull ClassSymbol currentClassSym;

    /** Constructs a writer for constructors, given a delegating writer and an owning class.
     * 
     * @param writer the delegating writer (typically the corresponding ClassWriter)
     * @param classdoc the Doc of the class whose constructors are being documented
     */
    public ConstructorWriterJml(@NonNull SubWriterHolderWriter writer,
            @NonNull ClassDoc classdoc) {
        super(writer, classdoc);
        currentClassSym = Utils.findNewClassSymbol(classdoc);
    }

    // FIXME - major change in b144
//    /** Overrides the super class method in order to write out any specs after the tags.
//     * @param method the constructor begin documented
//     */
//    public void writeTags(@NonNull ConstructorDoc method) {
//        super.writeTags(method);
//        writeJmlSpecs(method);
//    }
    
    /** Writes out the JML specifications for the constructor.
     * 
     * @param method the Doc element of the constructor being documented
     */
    public void writeJmlSpecs(@NonNull ConstructorDoc method) {
        if (method instanceof ConstructorDocImpl) {
            MethodSymbol oldMethodSym = ((ConstructorDocImpl)method).sym;
            Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
            Name newMethodName = Names.instance(context).fromString(oldMethodSym.name.toString());
            // FIXME - improve this method of finding matches
            Scope.Entry e = currentClassSym.members().lookup(newMethodName);
            while (!(e.sym instanceof MethodSymbol) || !match((MethodSymbol)e.sym,oldMethodSym)) {
                e = e.sibling;
            }
            MethodSymbol newMethodSym = (MethodSymbol)e.sym;
            JmlSpecs.MethodSpecs mspecs = JmlSpecs.instance(context).getSpecs(newMethodSym);
            if (mspecs != null) {
                writer.br(); // Need this if there is tag info, otherwise not // FIXME
                String s = Utils.jmlAnnotations(newMethodSym);
                if (Utils.hasSpecs(mspecs) || s.length()!=0) {
                    strong("JML Constructor Specifications: "); 
                    writer.print(s);
                    writer.preNoNewLine();
                    //writer.print(JmlPretty.write(mspecs.mods,false));
                    writer.print(JmlPretty.write(mspecs.cases,false));
                    writer.preEnd();
                }
            }
        }
    }
    
    /** Returns true if the two method symbols refer to the same constructor - 
     * same name, same parameter names, same parameter types, same type arguments.
     * The first argument is a method symbol in the JML compilation context;
     * the second argument is a method symbol in the Javadoc compilation context.
     * @param m constructor symbol in JML compilation context
     * @param mm method symbol in the Javadoc compilation context
     * @return true if the two symbols refer to the same method
     */ // FIXME
    public boolean match(MethodSymbol m, MethodSymbol mm) {
        if (!m.isConstructor()) return false;
        List<VarSymbol> mp = m.params();
        List<VarSymbol> mmp = mm.params();
        if (mp.size() != mmp.size()) return false;
        while (mp.tail != null) {
            if (!mp.head.name.toString().equals(mmp.head.name.toString())) return false;
            if (!mp.head.type.toString().equals(mmp.head.type.toString())) return false; // FIXME - is this how to compare types?
            mp = mp.tail;
            mmp = mmp.tail;
        }
        return true;
    }
    
    // FIXME - major change in b144
//    /** Overrides the parent method in order to write out details about
//     * JML model constructors after the footer for the Java constructors
//     * is written.
//     * @param classDoc the class whose constructors are being documented
//     */
//    public void writeFooter(@NonNull ClassDoc classDoc) {
//        super.writeFooter(classDoc);
//        writeJmlModelConstructors(classDoc);
//    }
    
    public void writeJmlModelConstructors(@NonNull ClassDoc classDoc) {
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
      DocEnv denv = ((ClassDocImpl)classDoc).docenv();
      // Find model methods to see if we need to do anything at all
      LinkedList<JmlMethodDecl> list = new LinkedList<JmlMethodDecl>();
      TypeSpecs tspecs = JmlSpecs.instance(org.jmlspecs.openjml.jmldoc.Main.jmlContext).get(currentClassSym);
      for (JmlTypeClause tc: tspecs.decls) {
          if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JmlMethodDecl) {
              JmlMethodDecl d = (JmlMethodDecl)((JmlTypeClauseDecl)tc).decl;
              //boolean use = JmlAttr.instance(org.jmlspecs.openjml.jmldoc.Main.jmlContext).findMod(d.mods,JmlToken.MODEL) != null;
              if (d.sym.isConstructor() && denv.shouldDocument(d.sym)) {
                  list.add(d);
              }
          }
      }
      if (list.isEmpty()) return;
      
      // Header
      writer.printTableHeadingBackground("JML Model Constructor Detail");
      writer.println();
      
      // FIXME - major change in b144
//      boolean isFirst = true;
//      for (JmlMethodDecl tc: list) {
//          ConstructorDoc md = new ConstructorDocImpl(((ClassDocImpl)classDoc).docenv(),tc.sym,tc.docComment,tc,null);
//          // Method header
//          writeConstructorHeader(md,isFirst); isFirst = false;
//          
//          // signature
//          writeSignature(md);
//          
//          // deprecation
//          writeDeprecated(md);
//          
//          // field comments
//          writeComments(md);
//          
//          // tag info
//          // FIXME super.writeTags(md);
//          writeJmlSpecs(md);
//          
//          // Method footer
//          writeConstructorFooter();
//      }
//      
//      
//      //Footer
//      super.writeFooter(classDoc);
      
        
    }

    // FIXME - major change in b144
//    public void writeMemberSummaryFooter(ClassDoc classDoc) {
//        super.writeMemberSummaryFooter(classDoc);
//        writeJmlConstructorSummary(classDoc);
//    }

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
        DocEnv denv = ((ClassDocImpl)classDoc).docenv();
        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(currentClassSym);
        for (JmlTypeClause tc : tspecs.decls) {
            // FIXME - control visibility
            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JCTree.JCMethodDecl) {
                JmlMethodDecl mdecl = ((JmlMethodDecl)((JmlTypeClauseDecl)tc).decl);
                MethodSymbol msym = mdecl.sym;
                if (msym.isConstructor() && denv.shouldDocument(msym)) {
                    ConstructorDoc constructor = new ConstructorDocImpl(((ClassDocImpl)classDoc).docenv(),msym,mdecl.docComment,mdecl,null);
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
            // FIXME - major change in b144
//            writeMemberSummary(classDoc, member, firstSentenceTags,
//                i == 0, i == list.size() - 1);
        }
//        super.writeMemberSummaryFooter(classDoc);
    }
    
    public void writeJmlConstructorSummaryHeader(ClassDoc classDoc) {
        //printSummaryAnchor(cd);
        Utils.writeHeader(writer,this,classDoc,"JML Model Constructor Summary",1);
    }

    /** This is overridden in order to include annotation information in the
     * method summary entry.  Immediately after this, the modifiers are written.
     * @param member the (method) Doc element whose annotation is to be printed
     */
    @Override
    protected void printModifier(ProgramElementDoc member) {
        writer.writeAnnotationInfo(member);
        super.printModifier(member);
    }

    // FIXME - major change in b144
//    /** This override has the effect of always printing out annotation information
//     * when a method signature is written; in particular, in javadoc it is not
//     * written out in the parameters within the constructor summary section.
//     * @param member the Doc element whose information is being printed
//     * @param includeAnnotations boolean switch now being ignored
//     */
//    @Override
//    protected void writeParameters(ExecutableMemberDoc member,
//            boolean includeAnnotations) {
//        super.writeParameters(member,true);
//    }

}
