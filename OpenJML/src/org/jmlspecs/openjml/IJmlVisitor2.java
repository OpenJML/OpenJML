/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCArrayTypeTree;
import com.sun.tools.javac.tree.JCTree.JCAssert;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCAssignOp;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCBreak;
import com.sun.tools.javac.tree.JCTree.JCCase;
import com.sun.tools.javac.tree.JCTree.JCCatch;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCConditional;
import com.sun.tools.javac.tree.JCTree.JCContinue;
import com.sun.tools.javac.tree.JCTree.JCDoWhileLoop;
import com.sun.tools.javac.tree.JCTree.JCEnhancedForLoop;
import com.sun.tools.javac.tree.JCTree.JCErroneous;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCForLoop;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCIf;
import com.sun.tools.javac.tree.JCTree.JCImport;
import com.sun.tools.javac.tree.JCTree.JCInstanceOf;
import com.sun.tools.javac.tree.JCTree.JCLabeledStatement;
import com.sun.tools.javac.tree.JCTree.JCLambda;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCMemberReference;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCNewArray;
import com.sun.tools.javac.tree.JCTree.JCNewClass;
import com.sun.tools.javac.tree.JCTree.JCParens;
import com.sun.tools.javac.tree.JCTree.JCPrimitiveTypeTree;
import com.sun.tools.javac.tree.JCTree.JCReturn;
import com.sun.tools.javac.tree.JCTree.JCSkip;
import com.sun.tools.javac.tree.JCTree.JCSwitch;
import com.sun.tools.javac.tree.JCTree.JCSynchronized;
import com.sun.tools.javac.tree.JCTree.JCThrow;
import com.sun.tools.javac.tree.JCTree.JCTry;
import com.sun.tools.javac.tree.JCTree.JCTypeApply;
import com.sun.tools.javac.tree.JCTree.JCTypeCast;
import com.sun.tools.javac.tree.JCTree.JCTypeParameter;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.JCWhileLoop;
import com.sun.tools.javac.tree.JCTree.JCWildcard;
import com.sun.tools.javac.tree.JCTree.LetExpr;
import com.sun.tools.javac.tree.JCTree.TypeBoundKind;

/**
 * This is an interface for Visitors to JML and Java nodes; it extends IVisitor
 * for Java nodes. Any JML tree visitor should implement this interface; it
 * provides a check for missing visit methods and enables the visitor to be
 * handled as an IJmlVisitor if needed. There should be a method here for each
 * kind of AST node that JML adds to the syntax tree.
 * 
 * @author David Cok
 */
public interface IJmlVisitor2<T> extends IVisitor {

    public void visitTopLevel(JCCompilationUnit that, T arg)    ;
    public void visitImport(JCImport that, T arg)               ;
    public void visitClassDef(JCClassDecl that, T arg)          ;
    public void visitMethodDef(JCMethodDecl that, T arg)        ;
    public void visitVarDef(JCVariableDecl that, T arg)         ;
    public void visitSkip(JCSkip that, T arg)                   ;
    public void visitBlock(JCBlock that, T arg)                 ;
    public void visitDoLoop(JCDoWhileLoop that, T arg)          ;
    public void visitWhileLoop(JCWhileLoop that, T arg)         ;
    public void visitForLoop(JCForLoop that, T arg)             ;
    public void visitForeachLoop(JCEnhancedForLoop that, T arg) ;
    public void visitLabelled(JCLabeledStatement that, T arg)   ;
    public void visitSwitch(JCSwitch that, T arg)               ;
    public void visitCase(JCCase that, T arg)                   ;
    public void visitSynchronized(JCSynchronized that, T arg)   ;
    public void visitTry(JCTry that, T arg)                     ;
    public void visitCatch(JCCatch that, T arg)                 ;
    public void visitConditional(JCConditional that, T arg)     ;
    public void visitIf(JCIf that, T arg)                       ;
    public void visitExec(JCExpressionStatement that, T arg)    ;
    public void visitBreak(JCBreak that, T arg)                 ;
    public void visitContinue(JCContinue that, T arg)           ;
    public void visitReturn(JCReturn that, T arg)               ;
    public void visitThrow(JCThrow that, T arg)                 ;
    public void visitAssert(JCAssert that, T arg)               ;
    public void visitApply(JCMethodInvocation that, T arg)      ;
    public void visitNewClass(JCNewClass that, T arg)           ;
    public void visitNewArray(JCNewArray that, T arg)           ;
    public void visitParens(JCParens that, T arg)               ;
    public void visitAssign(JCAssign that, T arg)               ;
    public void visitAssignop(JCAssignOp that, T arg)           ;
    public void visitUnary(JCUnary that, T arg)                 ;
    public void visitBinary(JCBinary that, T arg)               ;
    public void visitTypeCast(JCTypeCast that, T arg)           ;
    public void visitTypeTest(JCInstanceOf that, T arg)         ;
    public void visitIndexed(JCArrayAccess that, T arg)         ;
    public void visitSelect(JCFieldAccess that, T arg)          ;
    public void visitIdent(JCIdent that, T arg)                 ;
    public void visitLiteral(JCLiteral that, T arg)             ;
    public void visitTypeIdent(JCPrimitiveTypeTree that, T arg) ;
    public void visitTypeArray(JCArrayTypeTree that, T arg)     ;
    public void visitTypeApply(JCTypeApply that, T arg)         ;
    public void visitTypeParameter(JCTypeParameter that, T arg) ;
    public void visitWildcard(JCWildcard that, T arg)           ;
    public void visitTypeBoundKind(TypeBoundKind that, T arg)   ;
    public void visitAnnotation(JCAnnotation that, T arg)       ;
    public void visitModifiers(JCModifiers that, T arg)         ;
    public void visitErroneous(JCErroneous that, T arg)         ;
    public void visitLetExpr(LetExpr that, T arg)               ;
    public void visitReference(JCMemberReference that, T arg)   ;
    public void visitLambda(JCLambda that, T arg)               ;

    public void visitJmlBinary(JmlBinary that, T arg)                     ;
    public void visitJmlBlock(JmlBlock that, T arg)                       ;
    public void visitJmlChoose(JmlChoose that, T arg)                     ;
    public void visitJmlClassDecl(JmlClassDecl that, T arg)               ;
    public void visitJmlCompilationUnit(JmlCompilationUnit that, T arg)   ;
    public void visitJmlMethodSig(JmlMethodSig that, T arg)               ;
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that, T arg)           ;
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that, T arg)   ;
    public void visitJmlForLoop(JmlForLoop that, T arg)                   ;
    public void visitJmlGroupName(JmlGroupName that, T arg)               ;
    public void visitJmlImport(JmlImport that, T arg)                     ;
    public void visitJmlInlinedLoop(JmlInlinedLoop that, T arg)           ;
    public void visitJmlLabeledStatement(JmlLabeledStatement that, T arg) ;
    public void visitJmlLblExpression(JmlLblExpression that, T arg)       ;
    public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that, T arg) ;
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that, T arg) ;
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that, T arg) ;
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that, T arg) ;
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that, T arg) ;
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that, T arg) ;
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that, T arg) ;
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that, T arg) ;
    public void visitJmlMethodDecl(JmlMethodDecl that, T arg)             ;
    public void visitJmlMethodInvocation(JmlMethodInvocation that, T arg) ;
    public void visitJmlMethodSpecs(JmlMethodSpecs that, T arg)           ;
    public void visitJmlModelProgramStatement(JmlModelProgramStatement that, T arg);
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that, T arg);
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that, T arg)     ;
    public void visitJmlSetComprehension(JmlSetComprehension that, T arg) ;
    public void visitJmlSingleton(JmlSingleton that, T arg)               ;
    public void visitJmlSpecificationCase(JmlSpecificationCase that, T arg);
    public void visitJmlStatement(JmlStatement that, T arg)               ;
    public void visitJmlStatementShow(JmlStatementShow that, T arg)       ;
    public void visitJmlStatementDecls(JmlStatementDecls that, T arg)     ;
    public void visitJmlStatementExpr(JmlStatementExpr that, T arg)       ;
    public void visitJmlStatementHavoc(JmlStatementHavoc that, T arg)       ;
    public void visitJmlStatementLoopExpr(JmlStatementLoopExpr that, T arg)       ;
    public void visitJmlStatementLoopModifies(JmlStatementLoopModifies that, T arg)       ;
    public void visitJmlStatementSpec(JmlStatementSpec that, T arg)       ;
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that, T arg);
    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that, T arg)   ;
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that, T arg);
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that, T arg) ;
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that, T arg) ;
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that, T arg)     ;
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that, T arg)     ;
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that, T arg)         ;
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that, T arg) ;
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that, T arg)     ;
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that, T arg) ;
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that, T arg) ;
    public void visitJmlVariableDecl(JmlVariableDecl that, T arg)         ;
    public void visitJmlWhileLoop(JmlWhileLoop that, T arg)               ;

}
