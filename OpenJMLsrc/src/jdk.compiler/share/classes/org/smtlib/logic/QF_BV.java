package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.ISymbol;

public class QF_BV extends Logic {

	public QF_BV(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}

	public void validExpression(IExpr expression) throws IVisitor.VisitorException {
	}
	

	public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
		// May declare constants, but not functions without definitions
		noFunctions(id,argSorts,resultSort,definition);
	}

	public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
		noSorts(id,params,expr);
	}

	// All sorts are bitvector sorts; no new functions
	// FIXME : what does this mean : Formulas in ite terms must satisfy the same
	//  restriction as well, with the exception that they need not be closed 
	//  (because they may be in the scope of a let binder

}
