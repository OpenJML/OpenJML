package org.jmlspecs.openjml;

import org.jmlspecs.openjml.JmlTree.*;

/** This is an interface for Visitors to JML and Java nodes; it extends 
 * IVisitor for Java nodes.  Any JML tree visitor should implement this
 * interface, if only to provide a check for missing visit methods.
 * 
 * @author David Cok
 *
 */
public interface IJmlVisitor extends IVisitor {

    public void visitJmlCompilationUnit(JmlCompilationUnit that)   ;
    public void visitJmlRefines(JmlRefines that)                   ;
    public void visitJmlImport(JmlImport that)                     ;
    public void visitJmlClassDecl(JmlClassDecl that)               ;
    public void visitJmlMethodDecl(JmlMethodDecl that)             ;
    public void visitJmlVariableDecl(JmlVariableDecl that)         ;
    public void visitJmlSingleton(JmlSingleton that)               ;
    public void visitJmlFunction(JmlFunction that)                 ;
    public void visitJmlBinary(JmlBinary that)                     ;
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that)     ;
    public void visitJmlSetComprehension(JmlSetComprehension that) ;
    public void visitJmlLblExpression(JmlLblExpression that)       ;
    public void visitJmlForLoop(JmlForLoop that)                   ;
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that)   ;
    public void visitJmlWhileLoop(JmlWhileLoop that)               ;
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that)           ;
    public void visitJmlStatement(JmlStatement that)               ;
    public void visitJmlStatementLoop(JmlStatementLoop that)       ;
    public void visitJmlStatementSpec(JmlStatementSpec that)       ;
    public void visitJmlStatementExpr(JmlStatementExpr that)       ;
    public void visitJmlStatementDecls(JmlStatementDecls that)     ;
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that);
    public void visitJmlGroupName(JmlGroupName that)               ;
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that)         ;
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that)     ;
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that)     ;
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that)     ;
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) ;
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) ;
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) ;
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) ;
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) ;
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) ;
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) ;
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) ;
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) ;
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) ;
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly that) ;
    public void visitJmlMethodClauseAssignable(JmlMethodClauseAssignable that) ;
    public void visitJmlSpecificationCase(JmlSpecificationCase that);
    public void visitJmlMethodSpecs(JmlMethodSpecs that)           ;
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that);
    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that)   ;
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that);

}
