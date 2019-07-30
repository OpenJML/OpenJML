/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.vistors;

import org.jmlspecs.openjml.JmlTree.JmlNewClass;

import com.sun.tools.javac.tree.JCTree.*;

/**
 * This class is an interface to the JDK Visitor class. Too bad OpenJDK does not
 * use it (or something like it)---they should. However, we use it as a base for
 * extensions.
 * 
 * @author David Cok
 */
public interface IVisitor {
        public void visitTopLevel(JCCompilationUnit that)    ;
        public void visitImport(JCImport that)               ;
        public void visitClassDef(JCClassDecl that)          ;
        public void visitMethodDef(JCMethodDecl that)        ;
        public void visitVarDef(JCVariableDecl that)         ;
        public void visitSkip(JCSkip that)                   ;
        public void visitBlock(JCBlock that)                 ;
        public void visitDoLoop(JCDoWhileLoop that)          ;
        public void visitWhileLoop(JCWhileLoop that)         ;
        public void visitForLoop(JCForLoop that)             ;
        public void visitForeachLoop(JCEnhancedForLoop that) ;
        public void visitLabelled(JCLabeledStatement that)   ;
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
        public void visitNewClass(JCNewClass that)           ;
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
        public void visitModifiers(JCModifiers that)         ;
        public void visitErroneous(JCErroneous that)         ;
        public void visitLetExpr(LetExpr that)               ;
        public void visitReference(JCMemberReference that)   ;
        public void visitLambda(JCLambda that)               ;
}
