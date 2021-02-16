/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.vistors;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.*;

/**
 * This is an interface for Visitors to JML and Java nodes; it extends IVisitor
 * for Java nodes. Any JML tree visitor should implement this interface; it
 * provides a check for missing visit methods and enables the visitor to be
 * handled as an IJmlVisitor if needed. There should be a method here for each
 * kind of AST node that JML adds to the syntax tree.
 * 
 * @author David Cok
 */
public interface IJmlVisitor extends IVisitor {

    public void visitJmlBinary(JmlBinary that)                     ;
    public void visitJmlBlock(JmlBlock that)                       ;
    public void visitJmlChained(JmlChained that)                   ;
    public void visitJmlChoose(JmlChoose that)                     ;
    public void visitJmlClassDecl(JmlClassDecl that)               ;
    public void visitJmlCompilationUnit(JmlCompilationUnit that)   ;
    public void visitJmlMethodSig(JmlMethodSig that)               ;
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that)           ;
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that)   ;
    public void visitJmlForLoop(JmlForLoop that)                   ;
    public void visitJmlGroupName(JmlGroupName that)               ;
    public void visitJmlImport(JmlImport that)                     ;
    public void visitJmlInlinedLoop(JmlInlinedLoop that)           ;
    public void visitJmlLabeledStatement(JmlLabeledStatement that) ;
    public void visitJmlLblExpression(JmlLblExpression that)       ;
    public void visitJmlMatchExpression(JmlMatchExpression that)   ;
    public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that) ;
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) ;
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) ;
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) ;
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) ;
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) ;
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) ;
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) ;
    public void visitJmlMethodDecl(JmlMethodDecl that)             ;
    public void visitJmlMethodInvocation(JmlMethodInvocation that) ;
    public void visitJmlMethodSpecs(JmlMethodSpecs that)           ;
    public void visitJmlModelProgramStatement(JmlModelProgramStatement that);
    public void visitJmlNewClass(JmlNewClass that)                 ;
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that);
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that)     ;
    public void visitJmlSetComprehension(JmlSetComprehension that) ;
    public void visitJmlSingleton(JmlSingleton that)               ;
    public void visitJmlSpecificationCase(JmlSpecificationCase that);
    public void visitJmlStatement(JmlStatement that)               ;
    public void visitJmlStatementShow(JmlStatementShow that)       ;
    public void visitJmlStatementDecls(JmlStatementDecls that)     ;
    public void visitJmlStatementExpr(JmlStatementExpr that)       ;
    public void visitJmlStatementHavoc(JmlStatementHavoc that)       ;
    public void visitJmlStatementLoopExpr(JmlStatementLoopExpr that)       ;
    public void visitJmlStatementLoopModifies(JmlStatementLoopModifies that)       ;
    public void visitJmlStatementSpec(JmlStatementSpec that)       ;
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that);
    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that)   ;
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that);
    public void visitJmlTuple(JmlTuple that)                       ;
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) ;
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) ;
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that)     ;
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that)     ;
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that)         ;
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) ;
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that)     ;
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) ;
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) ;
    public void visitJmlVariableDecl(JmlVariableDecl that)         ;
    public void visitJmlWhileLoop(JmlWhileLoop that)               ;

}
