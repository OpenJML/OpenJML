package org.jmlspecs.openjml.esc;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;

class ClassCollector extends JmlTreeScanner {
    
    public static ClassCollector collect(JmlClassDecl cd, JmlMethodDecl md) {
        ClassCollector collector = new ClassCollector();
        collector.doMethods = false;
        //System.out.println("COLLECTING FOR CLASS " + cd.sym);
        collector.scan(cd);
        //System.out.println("COLLECTING FOR METHOD " + md.sym);
        if (md != null) {
            collector.doMethods = true;
            collector.scan(md);
        }
        return collector;
    }
    
    boolean doMethods;
    Set<ClassSymbol> classes = new HashSet<ClassSymbol>();
    Collection<JCTree> literals = new ArrayList<JCTree>();
    
    public ClassCollector() {
        scanMode = AST_SPEC_MODE;
    }
    
    @Override
    public void visitClassDef(JCClassDecl tree) {
        //System.out.println("ADDING-CD " + tree.sym);
        classes.add(tree.sym);
        super.visitClassDef(tree);
    }
    
    @Override
    public void visitMethodDef(JCMethodDecl tree) {
        if (!doMethods) return;
        super.visitMethodDef(tree);
    }
    
    @Override
    public void visitIdent(JCIdent tree) {
        save(tree.type);
        super.visitIdent(tree);
    }
    
    @Override
    public void visitSelect(JCFieldAccess tree) {
        save(tree.type);
        super.visitSelect(tree);
    }
    
    @Override
    public void visitIndexed(JCArrayAccess tree) {
        save(tree.indexed.type);
        super.visitIndexed(tree);
    }
    
    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation tree) {
        // FIXME - return types ?
        super.visitJmlMethodInvocation(tree);
    }
    
    @Override
    public void visitApply(JCMethodInvocation tree) {
        com.sun.tools.javac.code.Type tt = tree.type;
        save(tt);
        super.visitApply(tree);
    }
    
    protected void save(Type tt) {
        if (tt != null && tt.tag != TypeTags.VOID && !tt.isPrimitive() && tt.tsym instanceof ClassSymbol) {
            ClassSymbol c = (ClassSymbol)tt.tsym;
            classes.add(c);
        }
    }
    
    protected void save(Symbol sym) {
        if (sym instanceof ClassSymbol) save(sym.type);
    }
    
//    static public class JmlDiagnostic extends JCDiagnostic {
//        public JmlDiagnostic(DiagnosticFormatter<JCDiagnostic> formatter,
//                       DiagnosticType dt,
//                       boolean mandatory,
//                       DiagnosticSource source,
//                       DiagnosticPosition pos,
//                       String key,
//                       Object ... args) {
//            super(formatter,dt,mandatory,source,pos,key,args);
//        }
//        
//        static JmlDiagnostic warning(int pos, String key, Object ... args) {
//            return new JmlDiagnostic(formatter, WARNING, false, source, pos, qualify(WARNING, key), args);
//            
//        }
//    }
}