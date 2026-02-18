package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.ISymbol;

public class QF_AUFLIA extends Logic {

	public QF_AUFLIA(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}

	public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
	}

	public void validExpression(IExpr expression) throws IVisitor.VisitorException {
		noQuantifiers(expression);
		if (!isLinearInteger(expression)) throw new IVisitor.VisitorException("Integer expressions must be linear in this logic",expression.pos());
	}
	
	public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
	}

	// FIXME - needs restriction on array sort parameters - only Int
}
