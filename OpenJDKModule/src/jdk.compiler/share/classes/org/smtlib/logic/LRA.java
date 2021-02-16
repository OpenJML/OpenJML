package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.ILanguage;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.IExpr.*;
import org.smtlib.impl.SMTExpr;

/** This logic does not allow quantifiers or uninterpreted functions */
public class LRA extends Logic {

	public LRA(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}
	
	public boolean isConst(IExpr expr) {
		if (expr instanceof IExpr.INumeral) return true;
		if (expr instanceof IExpr.IDecimal) return true;
		if (!(expr instanceof IExpr.IFcnExpr)) return false;
		IExpr.IFcnExpr f = (IExpr.IFcnExpr)expr;
		if (f.head().toString().equals("-") && f.args().size() == 1) {
			expr = f.args().get(0);
			if (expr instanceof IExpr.INumeral) return true;
			if (expr instanceof IExpr.IDecimal) return true;
			return false;
		}
		if (f.head().toString().equals("/") && f.args().size() == 2) {
			expr = f.args().get(0);
			if (!isInteger(expr)) return false;
			expr = f.args().get(1);
			if (expr instanceof IExpr.INumeral) {
				if (((IExpr.INumeral)expr).intValue() == 0) return false;
				return true;
			}
			return false;
		}
		return false;
	}
	
	@Override
	public void validExpression(IExpr expression) throws IVisitor.VisitorException {
		IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
			@Override
			public Void visit(IExpr.IFcnExpr e) throws IVisitor.VisitorException {
				if (e.args().size() == 2) {
					String fcn = e.head().toString();
					if (fcn.equals("*")) {
						if (!(isConst(e.args().get(0)) || isConst(e.args().get(1)))) {
								throw new IVisitor.VisitorException("The expression must be linear: ", e.pos()); // FIXME + smt.defaultPrinter.toString(e),e.pos());
						}
					} else if (fcn.equals("/")) {
						if (!(isConst(e.args().get(0)) && isConst(e.args().get(1)))) {
							throw new IVisitor.VisitorException("The expression must be linear: ", e.pos()); // FIXME + smt.defaultPrinter.toString(e),e.pos());
						}
					} else {
						super.visit(e); // checks all the arguments
					}
						
				} else {
					super.visit(e); // checks all the arguments
				}
				return (Void)null;
			}
		};
		expression.accept(visitor);
	}
	
	@Override
	public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
		// May declare constants, but not functions without definitions
		noFunctions(id,argSorts,resultSort,definition);
	}

	@Override
	public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
		noSorts(id,params,expr);
	}
}
