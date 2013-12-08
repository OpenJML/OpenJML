package org.jmlspecs.openjml.esc;

import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTreeScanner;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCInstanceOf;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCTypeCast;

/** This class collects all mentions of classes within the ASTs scanned. */
class ClassCollector extends JmlTreeScanner {
    
    /** Static method that is the entry point to the functionality the collector */
    public static /*@ non_null pure */ ClassCollector collect(/*@ non_null */JmlClassDecl cd, /*@ nullable */JmlMethodDecl md) {
        ClassCollector collector = new ClassCollector();
        collector.doMethods = false;
        collector.scan(cd);
        if (md != null) {
            collector.doMethods = true;
            collector.scan(md);
        }
        return collector;
    }
    
    boolean doMethods;
    public final Set<ClassSymbol> classes = new HashSet<ClassSymbol>();
    
    public ClassCollector() {
        // scan all the specifications as well
        scanMode = AST_SPEC_MODE;
    }
    
    // FIXME - what about generic type variables
    protected void save(Type tt) {
        if (tt != null && tt.tag != TypeTags.VOID && !tt.isPrimitive() && tt.tsym instanceof ClassSymbol) {
            ClassSymbol c = (ClassSymbol)tt.tsym;
            classes.add(c);
        }
    }
    
    protected void save(Symbol sym) {
        if (sym instanceof ClassSymbol) save(sym.type);
    }
    
    // Note - we do not include parent classes and interfaces
    @Override
    public void visitClassDef(JCClassDecl tree) {
        classes.add(tree.sym);
        super.visitClassDef(tree);
    }
    
    @Override
    public void visitMethodDef(JCMethodDecl tree) {
        if (!doMethods) return;
        super.visitMethodDef(tree);
    }
    
    @Override
    public void visitJmlVariableDecl(JmlVariableDecl tree) {
        save(tree.sym.type);
        super.visitJmlVariableDecl(tree);
    }
    
    @Override
    public void visitIdent(JCIdent tree) {
        save(tree.type);
        super.visitIdent(tree);
    }
    
    @Override
    public void visitLiteral(JCLiteral tree) {
        save(tree.type);
        super.visitLiteral(tree);
    }
    
    @Override
    public void visitSelect(JCFieldAccess tree) {
        save(tree.type);
        super.visitSelect(tree);
    }
    
    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation tree) {
        save(tree.type);
        super.visitJmlMethodInvocation(tree);
    }
    
    @Override
    public void visitApply(JCMethodInvocation tree) {
        save(tree.type);
        super.visitApply(tree);
    }

    @Override
    public void visitTypeCast(JCTypeCast tree) {
        save(tree.type);
        super.visitTypeCast(tree);
    }

    @Override
    public void visitTypeTest(JCInstanceOf tree) {
        save(tree.clazz.type);
        super.visitTypeTest(tree);
    }
    
    // FIXME - generic visitType... methods

}