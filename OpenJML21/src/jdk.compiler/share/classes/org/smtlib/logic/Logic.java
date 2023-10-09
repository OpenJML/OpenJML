package org.smtlib.logic;

import java.util.Collection;
import java.util.List;

import org.smtlib.*;
import org.smtlib.IExpr.*;
import org.smtlib.impl.SMTExpr;

// FIXME - move some of this to ILogic - should the logic classes depend on SMTExpr.Logic?
//FIXME - document
public abstract class Logic extends SMTExpr.Logic implements ILanguage {

	public Logic(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}
	
	public void noQuantifiers(IExpr expression) throws IVisitor.VisitorException {
		IVisitor<Void> visitor = new IVisitor.TreeVisitor<Void>() {
			@Override
			public Void visit(IForall e) throws IVisitor.VisitorException {
				throw new IVisitor.VisitorException("A quantified expression is not allowed in the " + logicName + " logic",e.pos());
			}
			@Override
			public Void visit(IExists e) throws IVisitor.VisitorException {
				throw new IVisitor.VisitorException("A quantified expression is not allowed in the " + logicName + " logic",e.pos());
			}
		};
		expression.accept(visitor);
	}
	
	public void noFunctions(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {
		// May declare constants, but not functions without definitions
		if (argSorts.size() != 0 && definition == null) 
			throw new IVisitor.VisitorException("Declarations of uninterpreted functions are not allowed in this logic",id.pos());

	}
	
	public void noSorts(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {
		if (expr == null) throw new IVisitor.VisitorException("New sorts are not allowed in this logic",id.pos());
	}


	public boolean isInteger(IExpr expr) {
		if (expr instanceof IExpr.INumeral) return true;
		if (!(expr instanceof IExpr.IFcnExpr)) return false;
		IExpr.IFcnExpr f = (IExpr.IFcnExpr)expr;
		if (f.head().toString().equals("-") && f.args().size() == 1) {
			expr = f.args().get(0);
			if (expr instanceof IExpr.INumeral) return true;
			return false;
		}
		return false;
	}
	
	public boolean isFreeConstant(IExpr expr) {
		return (expr instanceof ISymbol);
//		if (!(expr instanceof IExpr.IFcnExpr)) return false;
//		IExpr.IFcnExpr f = (IExpr.IFcnExpr)expr;
//		return f.args().size() == 0;
	}
	
	public boolean isLinearInteger(IExpr expr) {
		// FIXME - should use a visitor; does not check inside quantified expressions
		if (expr instanceof IExpr.IFcnExpr) {
			IExpr.IFcnExpr f = (IExpr.IFcnExpr)expr;
			if (f.args().size() == 2) {
				String fcn = f.head().toString();
				IExpr lhs = f.args().get(0);
				IExpr rhs = f.args().get(1);
				if (fcn.equals("+") || fcn.equals("-")) {
					return isLinearInteger(lhs) && isLinearInteger(rhs);
				} else if (fcn.equals("*")) {
					return (isInteger(lhs) && isFreeConstant(rhs)) ||
							(isFreeConstant(lhs) && isInteger(rhs));
				} else if (fcn.equals("div") || fcn.equals("mod") || fcn.equals("abs")) {
					return false;
				} else { // Core functions
					return isLinearInteger(lhs) && isLinearInteger(rhs);
				}
			} else {
				int n = f.args().size();
				for (IExpr e: f.args()) {
					if (!isLinearInteger(e)) return false;
				}
				return true;
			}
		} else {
			return true;
		}
	}
}
