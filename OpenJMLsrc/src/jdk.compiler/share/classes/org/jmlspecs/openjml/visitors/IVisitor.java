/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.visitors;

import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlLambda;
import org.jmlspecs.openjml.JmlTree.JmlNewClass;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

/**
 * This class is an interface to the JDK Visitor class. Too bad OpenJDK does not
 * use it (or something like it)---they should. However, we use it as a base for
 * extensions.
 * 
 * @author David Cok
 */
public interface IVisitor {
	default public void scan(JCTree tree) {
	}
	
	default public void scan(List<? extends JCTree> trees) {
		for (var tree: trees) scan(tree);
	}

    default public void scan(Iterable<? extends JCTree> list) { 
        if (list != null)
          for (JCTree t: list) scan(t);
    }

    default public void visitTopLevel(JCCompilationUnit that) {
    	for (var d: that.defs) scan(d);
    }

    default public void visitImport(JCImport that) {
        scan(that.qualid);
    }
        public void visitClassDef(JCClassDecl that)          ;
        public void visitMethodDef(JCMethodDecl that)        ;
        public void visitVarDef(JCVariableDecl that)         ;
        
	default public void visitSkip(JCSkip that) {
	}
	
    default public void visitBlock(JCBlock that) {
    	for (var s: that.stats) scan(s);
    }
    
    default public void visitLabelled(JCLabeledStatement tree) {
        scan(tree.body);
    }

        public void visitDoLoop(JCDoWhileLoop that)          ;
        public void visitWhileLoop(JCWhileLoop that)         ;
        public void visitForLoop(JCForLoop that)             ;
        public void visitForeachLoop(JCEnhancedForLoop that) ;
        public void visitSwitch(JCSwitch that)               ;
        public void visitCase(JCCase that)                   ;
        public void visitSynchronized(JCSynchronized that)   ;
        public void visitTry(JCTry that)                     ;
        public void visitCatch(JCCatch that)                 ;
        public void visitConditional(JCConditional that)     ;
        public void visitIf(JCIf that)                       ;
        public void visitExec(JCExpressionStatement that)    ;
        public void visitBreak(JCBreak that)                 ;
        public void visitContinue(JCContinue that)           ;
        public void visitReturn(JCReturn that)               ;
        public void visitThrow(JCThrow that)                 ;
        public void visitAssert(JCAssert that)               ;
        public void visitApply(JCMethodInvocation that)      ;
        public void visitNewArray(JCNewArray that)           ;
        public void visitParens(JCParens that)               ;
        public void visitAssign(JCAssign that)               ;
        public void visitAssignop(JCAssignOp that)           ;
        public void visitUnary(JCUnary that)                 ;
        public void visitBinary(JCBinary that)               ;
        public void visitTypeCast(JCTypeCast that)           ;
        public void visitTypeTest(JCInstanceOf that)         ;
        public void visitIndexed(JCArrayAccess that)         ;
        public void visitSelect(JCFieldAccess that)          ;
        public void visitIdent(JCIdent that)                 ;
        public void visitLiteral(JCLiteral that)             ;
        public void visitTypeIdent(JCPrimitiveTypeTree that) ;
        public void visitTypeArray(JCArrayTypeTree that)     ;
        public void visitTypeApply(JCTypeApply that)         ;
        public void visitTypeParameter(JCTypeParameter that) ;
        public void visitWildcard(JCWildcard that)           ;
        public void visitTypeBoundKind(TypeBoundKind that)   ;
        public void visitAnnotation(JCAnnotation that)       ;
        default public void visitModifiers(JCModifiers that)         {}
        public void visitErroneous(JCErroneous that)         ;
        public void visitLetExpr(LetExpr that)               ;
        public void visitReference(JCMemberReference that)   ;
        
        default public void visitLambda(JCLambda that) {
            visitLambda(that);
            scan(((JmlLambda)that).jmlType);
        }

        default public void visitNewClass(JCNewClass that) {
            scan(that.encl);
            scan(that.typeargs);
            scan(that.clazz);
            scan(that.args);
            scan(that.def);
        }


}
