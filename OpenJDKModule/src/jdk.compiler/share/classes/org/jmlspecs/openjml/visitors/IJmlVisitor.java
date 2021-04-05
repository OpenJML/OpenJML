/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.visitors;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.visitors.JmlTreeScanner.Continuation;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.List;

/**
 * This is an interface for Visitors to JML and Java nodes; it extends IVisitor
 * for Java nodes. Any JML tree visitor should implement this interface; it
 * provides a check for missing visit methods and enables the visitor to be
 * handled as an IJmlVisitor if needed. There should be a method here for each
 * kind of AST node tree JML adds to the syntax tree.
 * 
 * @author David Cok
 */
public interface IJmlVisitor extends IVisitor {
	
	default public void scan(JCTree tree) {}
	
	default public void scan(List<? extends JCTree> trees) {
		for (var tree: trees) scan(tree);
	}

    default public void scan(Iterable<? extends JCTree> list) { 
        if (list != null)
          for (JCTree t: list) scan(t);
    }
    
    default public void visitJmlBinary(JmlBinary tree) {
    	scan(tree.lhs);
    	scan(tree.rhs);
    }
    default public void visitJmlBlock(JmlBlock tree) {
    	visitBlock(tree);
    }
    
    default public void visitJmlChained(JmlChained tree) {
        for (JCTree.JCBinary b: tree.conjuncts) scan(b);
    }
    
    default public void visitJmlChoose(JmlChoose tree) {
        scan(tree.orBlocks);
        scan(tree.elseBlock);
    }

    default public void visitJmlClassDecl(JmlClassDecl tree)               {}

    default public void visitJmlMethodSig(JmlMethodSig tree)               {}

    default public void visitJmlDoWhileLoop(JmlDoWhileLoop tree) {
        scan(tree.loopSpecs);
        visitDoLoop(tree);
    }
    
    default public void visitJmlEnhancedForLoop(JmlEnhancedForLoop tree)   {}
    default public void visitJmlForLoop(JmlForLoop tree)                   {}
    default public void visitJmlGroupName(JmlGroupName tree)               {}
    default public void visitJmlImport(JmlImport tree)                     {}
    default public void visitJmlInlinedLoop(JmlInlinedLoop tree)           {}
    default public void visitJmlLabeledStatement(JmlLabeledStatement tree) {}
    default public void visitJmlLblExpression(JmlLblExpression tree)       {}
    default public void visitJmlMatchExpression(JmlMatchExpression tree)   {}
    default public void visitJmlMethodClauseCallable(JmlMethodClauseCallable tree) {}
    default public void visitJmlMethodClauseConditional(JmlMethodClauseConditional tree) {}
    default public void visitJmlMethodClauseDecl(JmlMethodClauseDecl tree) {}
    default public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {}
    default public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {}
    default public void visitJmlMethodClauseSignals(JmlMethodClauseSignals tree) {}
    default public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly tree) {}
    default public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef tree) {}
    default public void visitJmlMethodDecl(JmlMethodDecl tree)             {}
    default public void visitJmlMethodInvocation(JmlMethodInvocation tree) {}
    default public void visitJmlMethodSpecs(JmlMethodSpecs tree)           {}
    default public void visitJmlModelProgramStatement(JmlModelProgramStatement tree){}
    default public void visitJmlNewClass(JmlNewClass tree)                 {}
    default public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree tree){}
    default public void visitJmlQuantifiedExpr(JmlQuantifiedExpr tree)     {}
    default public void visitJmlSetComprehension(JmlSetComprehension tree) {}
    default public void visitJmlSingleton(JmlSingleton tree) {
    	// do nothing - no children to scan
    }
    default public void visitJmlSpecificationCase(JmlSpecificationCase tree){}

    default public void visitJmlStatement(JmlStatement tree) {
        scan(tree.statement);
    }
    default public void visitJmlStatementShow(JmlStatementShow tree) {
        for (JCExpression e: tree.expressions) scan(e);
    }
    
    default public void visitJmlStatementDecls(JmlStatementDecls tree)     {}
    default public void visitJmlStatementExpr(JmlStatementExpr tree) {
        scan(tree.expression);
        scan(tree.optionalExpression);
    }
    
    default public void visitJmlStatementHavoc(JmlStatementHavoc tree)       {}
    default public void visitJmlStatementLoopExpr(JmlStatementLoopExpr tree)       {}
    default public void visitJmlStatementLoopModifies(JmlStatementLoopModifies tree)       {}
    default public void visitJmlStatementSpec(JmlStatementSpec tree)       {}
    default public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange tree){}
    default public void visitJmlStoreRefKeyword(JmlStoreRefKeyword tree)   {}
    default public void visitJmlStoreRefListExpression(JmlStoreRefListExpression tree){}
    default public void visitJmlTuple(JmlTuple tree)                       {}
    default public void visitJmlTypeClauseConditional(JmlTypeClauseConditional tree) {}
    default public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint tree) {}
    default public void visitJmlTypeClauseDecl(JmlTypeClauseDecl tree)     {}
    default public void visitJmlTypeClauseExpr(JmlTypeClauseExpr tree)     {}
    default public void visitJmlTypeClauseIn(JmlTypeClauseIn tree)         {}
    default public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer tree) {}
    default public void visitJmlTypeClauseMaps(JmlTypeClauseMaps tree)     {}
    default public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor tree) {}
    default public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents tree) {}
    default public void visitJmlVariableDecl(JmlVariableDecl tree)         {}
    default public void visitJmlWhileLoop(JmlWhileLoop tree)               {}

}
