package org.jmlspecs.openjml.jmldoc;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.ExecutableMemberDoc;
import com.sun.javadoc.MethodDoc;
import com.sun.javadoc.ProgramElementDoc;
import com.sun.javadoc.Tag;
import com.sun.tools.doclets.formats.html.MethodWriterImpl;
import com.sun.tools.doclets.formats.html.SubWriterHolderWriter;
import com.sun.tools.doclets.internal.toolkit.util.DocFinder;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javadoc.ClassDocImpl;
import com.sun.tools.javadoc.DocEnv;
import com.sun.tools.javadoc.MethodDocImpl;

/**
 * This class extends its parent in order (a) to add JML specification
 * information to the documentation of Java methods and (b) to document model
 * methods.
 * 
 * @author David R. Cok
 */
public class MethodWriterJml extends MethodWriterImpl {

    /** The class symbol of the class owning the method being documented,
     * in the JML compilation context.
     */
    protected @NonNull ClassSymbol currentClassSym;

    /**
     * Construct a new MethodWriterImpl.
     *
     * @param writer the writer for the class that the methods belong to.
     * @param classDoc the class being documented.
     */
    public MethodWriterJml(@NonNull SubWriterHolderWriter writer, @NonNull ClassDoc classDoc) {
        super(writer, classDoc);
        currentClassSym = Utils.findNewClassSymbol(classdoc);
    }
    
    /**
     * Write the javadoc tags (e.g. param and return tags) for the given method
     * and then write any JML specifications.
     *
     * @param method the method being documented.
     */
    // FIXME - major change in b144
//    @Override
//    public void writeTags(@NonNull MethodDoc method) {
//        super.writeTags(method);
//        writeJmlSpecs(method);
//    }
//    
    /** Write the JML specifications for the given method.
     * 
     * @param method the method whose specs are to be written
     */
    public void writeJmlSpecs(MethodDoc method) {
        if (method instanceof MethodDocImpl) {
            MethodSymbol oldMethodSym = ((MethodDocImpl)method).sym;
            Context context = org.jmlspecs.openjml.jmldoc.Main.jmlContext;
            Name newMethodName = Names.instance(context).fromString(oldMethodSym.name.toString());
            Scope.Entry e = currentClassSym.members().lookup(newMethodName);
            while (!(e.sym instanceof MethodSymbol) || !match((MethodSymbol)e.sym,oldMethodSym)) {
                //Scope.Entry ee = e;
                e = e.sibling;
                if (e == null) {
                    //if (ee.scope == null) {
                    // FIXME - this happens when public fields are inherited from package super classes
                    //    System.out.println("NOT FOUND " + newMethodName + " IN " + currentClassSym);
                        return;   // FIXME - not found?
                    //}
                    //e = ee.scope.lookup(newMethodName);
                }
            }
            MethodSymbol newMethodSym = (MethodSymbol)e.sym;
            JmlSpecs.MethodSpecs mspecs = JmlSpecs.instance(context).getSpecs(newMethodSym);
            if (mspecs != null) {
                writer.br(); // Need this if there is tag info, otherwise not // FIXME
                String s = Utils.jmlAnnotations(newMethodSym);
                if (Utils.hasSpecs(mspecs) || s.length()!=0) {
                    strong("JML Method Specifications: "); 
                    writer.print(s);
                    writer.preNoNewLine();
                    writer.print(JmlPretty.write(mspecs.cases,false));
                    writer.preEnd();
                }
                
                for (ClassSymbol c: Utils.getSupers(currentClassSym)) {
                    MethodSymbol m = findSameContext(newMethodSym,c);
                    if (m != null) {
                        mspecs = JmlSpecs.instance(context).getSpecs(m);
                        String ss = Utils.jmlAnnotations(m);
                        if (Utils.hasSpecs(mspecs) || ss.length()!=0) {
                            strong("JML Specifications inherited from " + c + ": "); 
                            writer.print(ss);
                            writer.preNoNewLine();
                            writer.print(JmlPretty.write(mspecs.cases,false));
                            writer.preEnd();
                        }
                    }
                }
            }
        }
    }
    
    /** Returns true if the two method symbols refer to the same method - 
     * same name, same parameter names, same parameter types, same type arguments.
     * The first argument is a method symbol in the JML compilation context;
     * the second argument is a method symbol in the Javadoc compilation context.
     * @param m method symbol in JML compilation context
     * @param mm method symbol in the Javadoc compilation context
     * @return true if the two symbols refer to the same method
     */
    public boolean match(MethodSymbol m, MethodSymbol mm) {
        if (!m.name.toString().equals(mm.name.toString())) return false;
        List<VarSymbol> mp = m.params();
        List<VarSymbol> mmp = mm.params();
        if (mp.size() != mmp.size()) return false;
        while (mp.tail != null) {
            if (!mp.head.name.toString().equals(mmp.head.name.toString())) return false;
            if (!mp.head.type.toString().equals(mmp.head.type.toString())) return false; 
            mp = mp.tail;
            mmp = mmp.tail;
        }
        return true;
    }
    
    /** This method finds a method, if any, in the given class with the same
     * signature as the given method - same name, same parameter types, same
     * type arguments (the parameter names may be different).  
     * The class and method are both in the JML compilation 
     * context, but the class may be a superclass or superinterface of the
     * method's owner.
     * @param m a method
     * @param c a super-class or interface of m's owner in which to find an overridden method
     * @return the overridden method, or null if none present
     */  // FIXME - need a better way to find overridden methods - can't be doing signature matching by hand - complications if there are type arguments with different names
    public MethodSymbol findSameContext(MethodSymbol m, ClassSymbol c) {
        Scope.Entry e = c.members().lookup(m.name);
loop:   while (e != null && e.sym != null) {
            Symbol s = e.sym;
            e = e.sibling; // We use sibling instead of next() so that we stay 
                // within the scope and do not look in enclosing scopes.  But then
                // we do have to check that names match
            if (!(s instanceof MethodSymbol)) continue;
            MethodSymbol mm = (MethodSymbol)s;
            if (m.name != mm.name) continue;
            List<VarSymbol> mp = m.params();
            List<VarSymbol> mmp = mm.params();
            if (mp.size() != mmp.size()) continue;
            while (mp.tail != null) {
                if (!Types.instance(Main.jmlContext).isSameType(mp.head.type,mmp.head.type)) continue loop;
                mp = mp.tail;
                mmp = mmp.tail;
            }
            return mm;
        }
        return null;
    }
    
    /** Overrides the parent class method in order to follow writing the
     * footer with writing out the detail information on all the JML model 
     * methods.
     * @param classDoc the class whose model methods are to be documented
     */
    // FIXME - major change in b144
//    public void writeFooter(@NonNull ClassDoc classDoc) {
//        super.writeFooter(classDoc);
//        writeJmlModelMethods(classDoc);
//    }
    
    /** Write out HTML documentation on JML model methods.
     * 
     * @param classDoc the class whose model methods are to be documented
     */
    public void writeJmlModelMethods(@NonNull ClassDoc classDoc) {
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
      DocEnv denv = ((ClassDocImpl)classDoc).docenv();
      LinkedList<JmlMethodDecl> list = new LinkedList<JmlMethodDecl>();
      TypeSpecs tspecs = JmlSpecs.instance(org.jmlspecs.openjml.jmldoc.Main.jmlContext).get(currentClassSym);
      for (JmlTypeClause tc: tspecs.clauses) {
          if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JmlMethodDecl) {
              JmlMethodDecl d = (JmlMethodDecl)((JmlTypeClauseDecl)tc).decl;
              if (!d.sym.isConstructor() && denv.shouldDocument(d.sym)) {
                  list.add(d);
              }
          }
      }
      if (list.isEmpty()) return;
      
      // Header
      writer.printTableHeadingBackground("JML Model Method Detail");
      writer.println();
      
      boolean isFirst = true;
      // FIXME - major change in b144
//      for (JmlMethodDecl tc: list) {
//          MethodDoc md = new MethodDocImpl(((ClassDocImpl)classDoc).docenv(),tc.sym,tc.docComment,tc,null);
//          // Method header
//          writeMethodHeader(md,isFirst); isFirst = false;
//          
//          // signature
//          writeSignature(md);
//          
//          // deprecation
//          writeDeprecated(md);
//          
//          // field comments
//          writeComments(classDoc,md);
//          
//          // tag info
//          writeTags(md); // includes writeJmlSpecs(md);
//
//          // Method footer
//          writeMethodFooter();
//      }
//      
//      
//      //Footer
//      super.writeFooter(classDoc);
      
        
    }

    // FIXME - major change in b144
//    /** Overridden to follow the member summary footer with the summary of
//     * JML model methods.
//     * @param classDoc the class that owns the methods and model methods
//     */
//    public void writeMemberSummaryFooter(@NonNull ClassDoc classDoc) {
//        super.writeMemberSummaryFooter(classDoc);
//        writeJmlMethodSummary(classDoc);
//    }

    // FIXME - major change in b144
//    /** Overridden to follow the summary footer for inherited methods
//     * with the summary of inherited
//     * JML model methods.
//     * @param classDoc the class whose inherited methods are being documented
//     */
//    public void writeInheritedMemberSummaryFooter(ClassDoc classDoc) {
//        writeJmlInheritedMemberSummaryFooter(classDoc);
//        super.writeInheritedMemberSummaryFooter(classDoc);
//    }
    
    /** Writes out information about the inherited model methods for the given
     * class.
     * @param classDoc the class whose inherited model methods are begin listed
     */
    public void writeJmlInheritedMemberSummaryFooter(ClassDoc classDoc) {
        ClassSymbol csym = Utils.findNewClassSymbol(classDoc);
        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(csym);
        ArrayList<MethodDoc> list = new ArrayList<MethodDoc>();
        DocEnv denv = ((ClassDocImpl)classDoc).docenv();
        
        // collect the methods to be documented
        for (JmlTypeClause tc : tspecs.clauses) {
            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JCTree.JCMethodDecl) {
                JmlMethodDecl mdecl = (JmlMethodDecl)((JmlTypeClauseDecl)tc).decl;
                MethodSymbol msym = mdecl.sym;
                if (msym.isConstructor()) continue;
                if (!denv.shouldDocument(msym)) continue;
                if (!Utils.isInherited(msym,currentClassSym)) continue;
                MethodDoc modelMethod = new MethodDocImpl(((ClassDocImpl)classDoc).docenv(),msym,mdecl.docComment,mdecl,null);
                list.add(modelMethod);
            }
        }
        
        // FIXME - major change in b144
//        // If there are any, emit documentation
//        if (!list.isEmpty()) {
//            writer.br();
//            writer.strong("Inherited JML model methods: ");
//            Collections.sort(list);
//            boolean isFirst = true;
//            for (MethodDoc method: list) {
//                writer.printInheritedSummaryMember(this, classDoc, method, isFirst);
//                isFirst = false;
//            }
//        }
    }
    
    /** Writes out documentation for JML model methods.
     * 
     * @param classDoc the class whose model methods are being documented
     */
    public void writeJmlMethodSummary(@NonNull ClassDoc classDoc) {
        ArrayList<MethodDoc> list = new ArrayList<MethodDoc>();
        DocEnv denv = ((ClassDocImpl)classDoc).docenv();
        TypeSpecs tspecs = JmlSpecs.instance(Main.jmlContext).get(currentClassSym);
        for (JmlTypeClause tc : tspecs.clauses) {
            if (tc instanceof JmlTypeClauseDecl && ((JmlTypeClauseDecl)tc).decl instanceof JCTree.JCMethodDecl) {
                JmlMethodDecl mdecl = ((JmlMethodDecl)((JmlTypeClauseDecl)tc).decl);
                MethodSymbol msym = mdecl.sym;
                if (!msym.isConstructor() && denv.shouldDocument(msym)) {
                    MethodDoc modelMethod = new MethodDocImpl(((ClassDocImpl)classDoc).docenv(),msym,mdecl.docComment,mdecl,null);
                    list.add(modelMethod);
                }
            }
        }
        if (list.isEmpty()) return;
        Collections.sort(list);
        writeJmlMethodSummaryHeader(classDoc);
        // The following loop is copied with modifications from MemberSummaryBuilder.buildSummary
        // FIXME - major change in b144
//        for (int i = 0; i<list.size(); i++) {
//            MethodDoc member = list.get(i);
//            Tag[] firstSentenceTags = member.firstSentenceTags();
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
//            writeMemberSummary(classDoc, member, firstSentenceTags,
//                i == 0, i == list.size() - 1);
//        }
//        super.writeMemberSummaryFooter(classDoc);
    }
    
    /** Writes the beginning of the HTML for a (model) method summary.
     * 
     * @param classDoc the class whose methods are being documented
     */
    public void writeJmlMethodSummaryHeader(@NonNull ClassDoc classDoc) {
        Utils.writeHeader(writer,this,classDoc,"JML Model Method Summary",2);
    }
    
    /** This is overridden in order to include annotation information in the
     * method summary entry.  Immediately after this, the modifiers are written.
     * @param member the (method) Doc element whose annotation is to be printed
     */
    @Override
    protected void printModifier(@NonNull ProgramElementDoc member) {
        writer.writeAnnotationInfo(member);
        super.printModifier(member);
    }

    // FIXME - major change in b144
//    /** This override has the effect of always printing out annotation information
//     * when a method signature is written; in particular, in javadoc it is not
//     * written out in the parameters within the member summary section.
//     * @param member the Doc element whose information is being printed
//     * @param includeAnnotations boolean switch now being ignored
//     */
//    @Override
//    protected void writeParameters(ExecutableMemberDoc member,
//            boolean includeAnnotations) {
//        super.writeParameters(member,true);
//    }
}
