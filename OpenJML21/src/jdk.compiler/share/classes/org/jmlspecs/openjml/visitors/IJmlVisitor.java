/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.visitors;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.ext.RecommendsClause;
import org.jmlspecs.openjml.visitors.JmlTreeScanner.Continuation;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCLambda;
import com.sun.tools.javac.tree.JCTree.JCNewClass;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

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
		if (trees != null) for (var tree: trees) scan(tree);
	}

    default public void scan(Iterable<? extends JCTree> list) { 
        if (list != null)
          for (JCTree t: list) scan(t);
    }
    
    default public void visitJmlBinary(JmlBinary tree) {
    	scan(tree.lhs);
    	scan(tree.rhs);
    }

//    default public void visitBlock(JmlBlock tree) {
//    	super.visitBlock(tree);
//    }
    
    default public void visitJmlChained(JmlChained tree) {
        for (JCTree.JCBinary b: tree.conjuncts) scan(b);
    }
    
    default public void visitJmlChoose(JmlChoose tree) {
        scan(tree.orBlocks);
        scan(tree.elseBlock);
    }

    default public void visitJmlClassDecl(JmlClassDecl tree)               {}

    default public void visitJmlMethodSig(JmlMethodSig tree) {
        scan(tree.expression);
        scan(tree.argtypes);
    }

    default public void visitJmlDoWhileLoop(JmlDoWhileLoop tree) {
        scan(tree.loopSpecs);
        visitDoLoop(tree);
    }

    default public void visitJmlEnhancedForLoop(JmlEnhancedForLoop tree) {
        scan(tree.loopSpecs);
        visitForeachLoop(tree);
    }

    default public void visitJmlForLoop(JmlForLoop tree) {
        scan(tree.loopSpecs);
        visitForLoop(tree);
    }


    default public void visitJmlGroupName(JmlGroupName tree) {
        scan(tree.selection);
    }

    default public void visitImport(JCTree.JCImport tree) {
        IVisitor.super.visitImport(tree);
    }
    
    default public void visitJmlInlinedLoop(JmlInlinedLoop tree)           {
    	// do nothing
    }

    default public void visitLabelled(JCTree.JCLabeledStatement tree) {
//        scan(tree.extraStatements.toList());
        scan(tree.body);
    }
    
    default public void visitJmlLblExpression(JmlLblExpression tree) {
        scan(tree.expression);
    }

    default public void visitJmlMatchExpression(JmlMatchExpression tree) {
        scan(tree.expression);
        for (JmlMatchExpression.MatchCase c: tree.cases) {
            scan(c.caseExpression);
            scan(c.value);
        }
    }

    default public void visitJmlMethodClauseBehaviors(JmlMethodClauseBehaviors tree) {
    }

    default public void visitJmlMethodClauseCallable(JmlMethodClauseCallable tree) {
        scan(tree.keyword);
        scan(tree.methodSignatures);
    }

    default public void visitJmlMethodClauseConditional(JmlMethodClauseConditional tree) {
        scan(tree.expression);
        scan(tree.predicate);
    }

    default public void visitJmlMethodClauseDecl(JmlMethodClauseDecl tree) {
        for (JCTree.JCVariableDecl s: tree.decls) {
            scan(s);
        }
    }

    default public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {
        scan(tree.expression);
        if (tree instanceof RecommendsClause.Node) {
            RecommendsClause.Node n = (RecommendsClause.Node)tree;
            scan(n.exceptionType);
        }
    }

    default public void visitJmlMethodClauseInvariants(JmlMethodClauseInvariants tree) {
        for (var e: tree.expressions) scan(e);
    }

    default public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {
        if(tree.cases==null){
            return;
        }
        for (JCTree t: tree.cases) {
            scan(t);
        }
    }

    default public void visitJmlMethodClauseSignals(JmlMethodClauseSignals tree) {
        scan(tree.expression);
    }

    default public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly tree) {
        scan(tree.list);
    }

    default public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef tree) {
        scan(tree.list);
    }

    default public void visitJmlMethodDecl(JmlMethodDecl tree)             {}
    default public void visitJmlMethodInvocation(JmlMethodInvocation tree) {
        scan(tree.args);
    }

    default public void visitJmlMethodSpecs(JmlMethodSpecs tree)           {
        scan(tree.cases);
        scan(tree.impliesThatCases);
        scan(tree.forExampleCases);
        scan(tree.feasible);
    }

    default public void visitJmlModelProgramStatement(JmlModelProgramStatement tree){
        scan(tree.item);
    }

//    default public void visitNewClass(JCNewClass tree)                 {
//        IVisitor.super.visitClass(tree);
//    }
    
    default public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree tree){
        // no children to scan
    }

    default public void visitJmlQuantifiedExpr(JmlQuantifiedExpr tree)     {
        scan(tree.decls);
        scan(tree.range);
        scan(tree.value);
        scan(tree.racexpr);
        scan(tree.triggers);
    }

    default public void visitJmlSetComprehension(JmlSetComprehension tree) {
        scan(tree.newtype);
        scan(tree.variable);
        scan(tree.predicate);
    }
    default public void visitJmlRange(JmlRange tree) {
    	scan(tree.lo);
    	scan(tree.hi);
    }
    default public void visitJmlSingleton(JmlSingleton tree) {
    	// do nothing - no children to scan
    }

    default public void visitJmlSpecificationCase(JmlSpecificationCase tree) {
//		var prev = context == null ? null : Log.instance(context).useSource(tree.sourcefile);
//		try {
	        scan(tree.modifiers);
	        scan(tree.clauses);
	        scan(tree.block);
//		} finally {
//			if (context != null) Log.instance(context).useSource(prev);
//		}
//   	
    }

    default public void visitJmlStatement(JmlStatement tree) {
        scan(tree.statement);
    }
    default public void visitJmlStatementShow(JmlStatementShow tree) {
        for (JCExpression e: tree.expressions) scan(e);
    }
    
    default public void visitJmlStatementDecls(JmlStatementDecls tree) {
        for (JCTree.JCStatement s : tree.list) {
            scan(s);
        }
    }

    default public void visitJmlStatementExpr(JmlStatementExpr tree) {
        scan(tree.expression);
        scan(tree.optionalExpression);
    }
    
    default public void visitJmlStatementHavoc(JmlStatementHavoc tree) {
        scan(tree.storerefs);
    }

    default public void visitJmlStatementLoopExpr(JmlStatementLoopExpr tree) {
        scan(tree.expression);
    }

    default public void visitJmlStatementLoopModifies(JmlStatementLoopModifies tree) {
        scan(tree.storerefs);
    }

    default public void visitJmlStatementSpec(JmlStatementSpec tree) {
        scan(tree.statementSpecs);
        scan(tree.statements);
    }
    
    default public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange tree) {
        scan(tree.expression);
        scan(tree.lo);
        scan(tree.hi);
    }

    default public void visitJmlStoreRefKeyword(JmlStoreRefKeyword tree) {
        // nothing to scan
    }

    default public void visitJmlStoreRefListExpression(JmlStoreRefListExpression tree) {
        for (JCTree t: tree.list) {
            scan(t);
        }
    }
    
    default public void visitJmlStoreRef(JmlStoreRef tree) {
    	scan(tree.expression);
    	scan(tree.receiver);
    	scan(tree.range);
    }
    
    default public void visitJmlTuple(JmlTuple tree) {
        for (JCExpression e: tree.values) 
            scan(e);
    }
    
    default public void visitJmlTypeClauseConditional(JmlTypeClauseConditional tree) {
        scan(tree.modifiers);
        scan(tree.identifier);
        scan(tree.expression);
    }

    default public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint tree) {
        scan(tree.modifiers);
        scan(tree.expression);
        scan(tree.sigs);
    }

    default public void visitJmlTypeClauseDecl(JmlTypeClauseDecl tree) {
        scan(tree.modifiers);
        scan(tree.decl);
    }

    default public void visitJmlTypeClauseExpr(JmlTypeClauseExpr tree) {
        scan(tree.modifiers);
        scan(tree.expression);
    }

    default public void visitJmlTypeClauseIn(JmlTypeClauseIn tree) {
        scan(tree.modifiers);
        for (JmlGroupName g: tree.list) {
            scan(g);
        }
    }

    default public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer tree) {
        scan(tree.modifiers);
        scan(tree.specs);
    }

    default public void visitJmlTypeClauseMaps(JmlTypeClauseMaps tree) {
        scan(tree.modifiers);
        scan(tree.expressions);
        for (JmlGroupName g: tree.list) {
            scan(g);
        }
    }

    default public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor tree) {
        scan(tree.modifiers);
        scan(tree.identifier);
        for (JCTree.JCExpression e: tree.list) {
            scan(e);
        }
    }

    default public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents tree) {
        scan(tree.modifiers);
        scan(tree.ident);
        scan(tree.expression);
    }

    default public void visitJmlVariableDecl(JmlVariableDecl tree)         {} // FIXME or comment

    default public void visitJmlWhileLoop(JmlWhileLoop tree) {
        scan(tree.loopSpecs);
        visitWhileLoop(tree);
    }

}
