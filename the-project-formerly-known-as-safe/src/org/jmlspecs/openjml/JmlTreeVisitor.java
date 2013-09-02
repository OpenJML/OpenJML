/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import org.jmlspecs.openjml.JmlTree.*;

import com.sun.source.tree.TreeVisitor;

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

    R visitJmlBinary(JmlBinary that, P p)                     ;
    R visitJmlChoose(JmlChoose that, P p)                     ;
    R visitJmlClassDecl(JmlClassDecl that, P p)               ;
    R visitJmlCompilationUnit(JmlCompilationUnit that, P p)   ;
    R visitJmlConstraintMethodSig(JmlConstraintMethodSig that, P p);
    R visitJmlDoWhileLoop(JmlDoWhileLoop that, P p)           ;
    R visitJmlEnhancedForLoop(JmlEnhancedForLoop that, P p)   ;
    R visitJmlForLoop(JmlForLoop that, P p)                   ;
    R visitJmlGroupName(JmlGroupName that, P p)               ;
    R visitJmlImport(JmlImport that, P p)                     ;
    R visitJmlLblExpression(JmlLblExpression that, P p)       ;
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
    R visitJmlModelProgramStatement(JmlModelProgramStatement that, P p);
    R visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that, P p);
    R visitJmlQuantifiedExpr(JmlQuantifiedExpr that, P p)     ;
    R visitJmlSetComprehension(JmlSetComprehension that, P p) ;
    R visitJmlSingleton(JmlSingleton that, P p)               ;
    R visitJmlSpecificationCase(JmlSpecificationCase that, P p);
    R visitJmlStatement(JmlStatement that, P p)               ;
    R visitJmlStatementDecls(JmlStatementDecls that, P p)     ;
    R visitJmlStatementExpr(JmlStatementExpr that, P p)       ;
    R visitJmlStatementHavoc(JmlStatementHavoc that, P p)       ;
    R visitJmlStatementLoop(JmlStatementLoop that, P p)       ;
    R visitJmlStatementSpec(JmlStatementSpec that, P p)       ;
    R visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that, P p);
    R visitJmlStoreRefKeyword(JmlStoreRefKeyword that, P p)   ;
    R visitJmlStoreRefListExpression(JmlStoreRefListExpression that, P p);
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
    R visitJmlDeclassifyClause(JmlDeclassifyClause that, P p)               ;
    R visitJmlLevelStatement(JmlLevelStatement that, P p)               ;
    R visitJmlChannelStatement(JmlChannelStatement that, P p)               ;

}
