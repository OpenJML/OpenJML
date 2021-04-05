package com.sun.tools.javac.comp;

import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlBlock;
import org.jmlspecs.openjml.JmlTree.JmlChained;
import org.jmlspecs.openjml.JmlTree.JmlChoose;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import org.jmlspecs.openjml.JmlTree.JmlEnhancedForLoop;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlImport;
import org.jmlspecs.openjml.JmlTree.JmlInlinedLoop;
import org.jmlspecs.openjml.JmlTree.JmlLabeledStatement;
import org.jmlspecs.openjml.JmlTree.JmlLblExpression;
import org.jmlspecs.openjml.JmlTree.JmlMatchExpression;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseCallable;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignals;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignalsOnly;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlMethodSig;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlModelProgramStatement;
import org.jmlspecs.openjml.JmlTree.JmlNewClass;
import org.jmlspecs.openjml.JmlTree.JmlPrimitiveTypeTree;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlSetComprehension;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlStatement;
import org.jmlspecs.openjml.JmlTree.JmlStatementDecls;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlStatementHavoc;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoopExpr;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoopModifies;
import org.jmlspecs.openjml.JmlTree.JmlStatementShow;
import org.jmlspecs.openjml.JmlTree.JmlStatementSpec;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefListExpression;
import org.jmlspecs.openjml.JmlTree.JmlTuple;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConstraint;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseIn;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMaps;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMonitorsFor;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTree.JmlWhileLoop;
import org.jmlspecs.openjml.visitors.IJmlVisitor;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.comp.Annotate;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

public class JmlTypeAnnotate extends Annotate.TypeAnnotate implements IJmlVisitor {

	public JmlTypeAnnotate(Annotate annotate, Env<AttrContext> env, Symbol sym, DiagnosticPosition deferPos) {
		annotate.super(env, sym, deferPos);
	}

	@Override
	public void visitJmlBinary(JmlBinary that) {
		scan(that.lhs);
		scan(that.rhs);
	}

	@Override
	public void visitJmlBlock(JmlBlock that) {
		scan(that.stats);
	}

	@Override
	public void visitJmlChained(JmlChained that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlChoose(JmlChoose that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlClassDecl(JmlClassDecl that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlMethodSig(JmlMethodSig that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlForLoop(JmlForLoop that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlGroupName(JmlGroupName that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlImport(JmlImport that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlInlinedLoop(JmlInlinedLoop that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlLabeledStatement(JmlLabeledStatement that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlLblExpression(JmlLblExpression that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlMatchExpression(JmlMatchExpression that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlMethodDecl(JmlMethodDecl that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlMethodInvocation(JmlMethodInvocation that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlMethodSpecs(JmlMethodSpecs that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlNewClass(JmlNewClass that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlSetComprehension(JmlSetComprehension that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlSingleton(JmlSingleton that) {
		// do nothing
	}

	@Override
	public void visitJmlSpecificationCase(JmlSpecificationCase that) {
		scan(that.clauses);
	}

	@Override
	public void visitJmlStatement(JmlStatement that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlStatementShow(JmlStatementShow that) {
		scan(that.expressions);
	}

	@Override
	public void visitJmlStatementDecls(JmlStatementDecls that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlStatementExpr(JmlStatementExpr that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlStatementHavoc(JmlStatementHavoc that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlStatementLoopExpr(JmlStatementLoopExpr that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlStatementLoopModifies(JmlStatementLoopModifies that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlStatementSpec(JmlStatementSpec that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlTuple(JmlTuple that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
		scan(that.decl);
		
	}

	@Override
	public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void visitJmlVariableDecl(JmlVariableDecl that) {
		visitVarDef(that);
	}

	@Override
	public void visitJmlWhileLoop(JmlWhileLoop that) {
		// TODO Auto-generated method stub
		
	}
	
	

}
