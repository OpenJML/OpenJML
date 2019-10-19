/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.vistors;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.source.tree.TreeVisitor;
import com.sun.tools.javac.tree.JCTree.LetExpr;

/**
 * This is an interface for visitors for JML ASTs, with parameters and return 
 * types, as described in TreeVisitor.
 * 
 * @author David Cok
 * 
 * @param <R>
 *            the return type from the visitor methods
 * @param <P>
 *            the type of additional parameters (or Void)
 */
// TODO - TreeVisitor takes arguments that are interfaces, not specific node
// classes.  JmlTreeVisitor should be modified to that model as well.
public interface JmlTreeVisitor<R,P> extends TreeVisitor<R,P> {
    
    // TODO - the following ought to be in TreeVisitor, but JDK did 
    // not include it.
    R visitLetExpr(LetExpr that, P p)                         ;

    R visitJmlBinary(JmlBinary that, P p)                     ;
    R visitJmlBlock(JmlBlock that, P p)                       ;
    R visitJmlChained(JmlChained that, P p)                   ;
    R visitJmlChoose(JmlChoose that, P p)                     ;
    R visitJmlClassDecl(JmlClassDecl that, P p)               ;
    R visitJmlCompilationUnit(JmlCompilationUnit that, P p)   ;
    R visitJmlConstraintMethodSig(JmlMethodSig that, P p);
    R visitJmlDoWhileLoop(JmlDoWhileLoop that, P p)           ;
    R visitJmlEnhancedForLoop(JmlEnhancedForLoop that, P p)   ;
    R visitJmlForLoop(JmlForLoop that, P p)                   ;
    R visitJmlGroupName(JmlGroupName that, P p)               ;
    R visitJmlImport(JmlImport that, P p)                     ;
    R visitJmlInlinedLoop(JmlInlinedLoop that, P p)           ;
    R visitJmlLabeledStatement(JmlLabeledStatement that, P p) ;
    R visitJmlLblExpression(JmlLblExpression that, P p)       ;
    R visitJmlMatchExpression(JmlMatchExpression that, P p)   ;
    R visitJmlMethodClauseCallable(JmlMethodClauseCallable that, P p) ;
    R visitJmlMethodClauseConditional(JmlMethodClauseConditional that, P p) ;
    R visitJmlMethodClauseDecl(JmlMethodClauseDecl that, P p) ;
    R visitJmlMethodClauseExpr(JmlMethodClauseExpr that, P p) ;
    R visitJmlMethodClauseGroup(JmlMethodClauseGroup that, P p) ;
    R visitJmlMethodClauseSignals(JmlMethodClauseSignals that, P p) ;
    R visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that, P p) ;
    R visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that, P p) ;
    R visitJmlMethodDecl(JmlMethodDecl that, P p)             ;
    R visitJmlMethodInvocation(JmlMethodInvocation that, P p) ;
    R visitJmlMethodSpecs(JmlMethodSpecs that, P p)           ;
    R visitJmlNewClass(JmlNewClass that, P p)                 ;
    R visitJmlModelProgramStatement(JmlModelProgramStatement that, P p);
    R visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that, P p);
    R visitJmlQuantifiedExpr(JmlQuantifiedExpr that, P p)     ;
    R visitJmlSetComprehension(JmlSetComprehension that, P p) ;
    R visitJmlSingleton(JmlSingleton that, P p)               ;
    R visitJmlSpecificationCase(JmlSpecificationCase that, P p);
    R visitJmlStatement(JmlStatement that, P p)               ;
    R visitJmlStatementShow(JmlStatementShow that, P p)       ;
    R visitJmlStatementDecls(JmlStatementDecls that, P p)     ;
    R visitJmlStatementExpr(JmlStatementExpr that, P p)       ;
    R visitJmlStatementHavoc(JmlStatementHavoc that, P p)       ;
    R visitJmlStatementLoopExpr(JmlStatementLoopExpr that, P p)       ;
    R visitJmlStatementLoopModifies(JmlStatementLoopModifies that, P p)       ;
    R visitJmlStatementSpec(JmlStatementSpec that, P p)       ;
    R visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that, P p);
    R visitJmlStoreRefKeyword(JmlStoreRefKeyword that, P p)   ;
    R visitJmlStoreRefListExpression(JmlStoreRefListExpression that, P p);
    R visitJmlTuple(JmlTuple that, P p)                       ;
    R visitJmlTypeClauseConditional(JmlTypeClauseConditional that, P p) ;
    R visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that, P p) ;
    R visitJmlTypeClauseDecl(JmlTypeClauseDecl that, P p)     ;
    R visitJmlTypeClauseExpr(JmlTypeClauseExpr that, P p)     ;
    R visitJmlTypeClauseIn(JmlTypeClauseIn that, P p)         ;
    R visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that, P p) ;
    R visitJmlTypeClauseMaps(JmlTypeClauseMaps that, P p)     ;
    R visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that, P p) ;
    R visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that, P p) ;
    R visitJmlVariableDecl(JmlVariableDecl that, P p)         ;
    R visitJmlWhileLoop(JmlWhileLoop that, P p)               ;
}
