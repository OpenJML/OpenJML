package org.jmlspecs.openjml.esc;

import java.lang.reflect.Method;
import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.ext.SetStatement;
import org.jmlspecs.openjml.ext.StatementExprExtensions;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;

/** This class collects all mentions of classes within the ASTs scanned. */
class ClassCollector extends JmlTreeScanner {
    
    /** Static method that is the entry point to the functionality the collector */
    public static /*@ non_null pure */ ClassCollector collect(/*@ non_null */JmlClassDecl cd, /*@ nullable */JmlMethodDecl md, Context context) {
        ClassCollector collector = new ClassCollector();
        collector.context = context;
        collector.useBV = false;
        collector.doMethods = false;
        collector.scan(cd);
        if (md != null) {
            collector.doMethods = true;
            collector.scan(md);
        }
        return collector;
    }
    // FIXME - change to collecting TypeSymbol
    
    Context context;
    boolean doMethods;
    boolean useBV = false;
    public final Set<ClassSymbol> classes = new HashSet<ClassSymbol>();
    
    public ClassCollector() {
        // scan all the specifications as well
        scanMode = AST_SPEC_MODE;
    }
    
    // FIXME - what about generic type variables
    protected void save(Type tt) {
        if (tt != null && tt.getTag() != TypeTag.VOID && tt.getTag() != TypeTag.BOT && !tt.isPrimitive() && tt.tsym instanceof ClassSymbol && !(tt instanceof MethodType)) {
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
        save(tree.sym);
        super.visitClassDef(tree);
//        scan(tree.mods);
//        scan(tree.typarams);
//        scan(tree.extending);
//        scan(tree.implementing);
//        if (doMethods) scan(tree.defs);
        Symbol encl = tree.sym.owner;
        while (encl instanceof Symbol.MethodSymbol){
            encl = encl.owner;
        }
        if (encl instanceof ClassSymbol) {
            save(encl);
        }
    }
    
    public void visitAnnotation(JCAnnotation tree) {
        // Don't record the annotation or things it depends on, since we do not reason about them
    }

    
    @Override
    public void visitMethodDef(JCMethodDecl tree) {
        if (!doMethods) return;
        super.visitMethodDef(tree);
    }
    
    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
    	if (!doMethods) return;
    	JmlSpecs.MethodSpecs ms = JmlSpecs.instance(context).getAttrSpecs(that.sym);
    	// ms might be null if the method has no explicit specs and has not been given default or inferred
    	// specs -- constructors for anonymous methods, for example
    	if (ms != null) scan(ms.mods);
        visitMethodDef(that);
        if (ms != null) scan(ms.cases);
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
    public void visitBinary(JCTree.JCBinary tree) {
        JCTree.Tag op = tree.getTag();
        boolean was = useBV;
        // FIXME - the tree may not always be typed, but this is likely not the correct behavior
        if (tree.type != null && tree.type.getTag() != TypeTag.BOOLEAN) {
            if (op == JCTree.Tag.BITAND || op == JCTree.Tag.BITAND_ASG) {
                if (!useBV && tree.rhs instanceof JCLiteral) {
                    Object o = ((JCLiteral)tree.rhs).getValue();
                    if (o instanceof Number) {
                        long v = ((Number)o).longValue();
                        if (v > 0 && Long.bitCount(v+1) == 1) {
                            // OK
                        } else {
                            useBV = true;
                        }
                    } else {
                        useBV = true;
                    }
                } else {
                    useBV = true;
                }
            } else if (op == JCTree.Tag.BITOR || op == JCTree.Tag.BITOR_ASG || op == JCTree.Tag.BITXOR || op == JCTree.Tag.BITXOR_ASG) {
                useBV = true;
            }
        }
        if (op == JCTree.Tag.SL || op == JCTree.Tag.SL_ASG || op == JCTree.Tag.SR || op == JCTree.Tag.SR_ASG || op == JCTree.Tag.USR || op == JCTree.Tag.USR_ASG    ) {
            if (!(tree.rhs instanceof JCLiteral)) {
                useBV = true;
            }
        }
        if (!was && useBV && Utils.debug("bv")) { System.out.println("Using bit-vector because of " + tree); }
        super.visitBinary(tree);
    }
    
    @Override
    public void visitAssignop(JCTree.JCAssignOp tree) {
        JCTree.Tag op = tree.getTag();
        if (useBV) {
            // skip
        } else if (op == JCTree.Tag.BITAND_ASG ||  op == JCTree.Tag.BITOR_ASG  || op == JCTree.Tag.BITXOR_ASG) {  
            if (tree.type.getTag() != TypeTag.BOOLEAN && Types.instance(context).unboxedTypeOrType(tree.type).getTag() != TypeTag.BOOLEAN) {
                useBV = true;
                if (Utils.debug("bv")) System.out.println("Using bit-vector because of " + tree);
            }
        } else if (op == JCTree.Tag.SL_ASG || op == JCTree.Tag.SR_ASG || op == JCTree.Tag.USR_ASG    ) {
            useBV = true;
            if (Utils.debug("bv")) { System.out.println("Using bit-vector because of " + tree); }
        }
        super.visitAssignop(tree);
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
    public void visitJmlStatementExpr(JmlStatementExpr tree) {
        boolean was = useBV;
        if (tree.clauseType == StatementExprExtensions.useClause) {
            // skip
        } else {
            super.visitJmlStatementExpr(tree);
        }
        if (!was && useBV && Utils.debug("bv")) { System.out.println("Using bit-vector because of " + tree);  }
    }
    
    @Override
    public void visitJmlStatement(JmlStatement tree) {
        boolean was = useBV;
        if (tree.clauseType == SetStatement.setClause) {
            if (tree.statement instanceof JCTree.JCExpressionStatement exec) {
                JCExpression expr = exec.expr;
                if (expr.type.getTag() == TypeTag.VOID
                    && expr instanceof JCTree.JCMethodInvocation apply
                    && JmlSpecs.instance(context).isSpecOKMethod((Symbol.MethodSymbol)TreeInfo.symbolFor(apply.meth))) {
                    // skip
                    return;
                }
            }
        }
        super.visitJmlStatement(tree);
        if (!was && useBV && Utils.debug("bv")) { System.out.println("Using bit-vector because of " + tree);  }
    }
    
    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {
        boolean was = useBV;
        super.visitJmlMethodClauseExpr(tree);
        if (!was && useBV && Utils.debug("bv")) { System.out.println("Using bit-vector because of " + tree); }
    }
    
    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation tree) {
        save(tree.type);
        super.visitJmlMethodInvocation(tree);
    }
    
    Set<Symbol.MethodSymbol> methodsVisited = new HashSet<>();
    
    @Override
    public void visitApply(JCMethodInvocation tree) {
        save(tree.type);
        super.visitApply(tree);
        Symbol sym = (tree.meth instanceof JCIdent) ? ((JCIdent)tree.meth).sym
                            : (tree.meth instanceof JCFieldAccess) ? ((JCFieldAccess)tree.meth).sym : null;
        if (sym instanceof Symbol.MethodSymbol) {
            Symbol.MethodSymbol msym = (Symbol.MethodSymbol)sym;
            if (methodsVisited.add(msym)) {
                JmlSpecs.MethodSpecs mspecs = JmlSpecs.instance(context).getAttrSpecs(msym);
                if (mspecs != null) scan(mspecs.cases);
            }
        }
    }

    @Override
    public void visitTypeCast(JCTypeCast tree) {
        save(tree.type);
        super.visitTypeCast(tree);
    }

    @Override
    public void visitTypeTest(JCInstanceOf tree) {
        save(tree.pattern.type); // FIXME - is this correct?
        super.visitTypeTest(tree);
    }
    
    // FIXME - generic visitType... methods

}