/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

// FIXME - document IVisitor, including an example of an implementation and a discussion about accept; not sure it is used
// FIXME - figure out how to properly do Nullable for generic types
// FIXME - do a review of all of the visit methods to be sure we have the structure correct

import org.smtlib.ICommand.IScript;
import org.smtlib.IExpr.IAsIdentifier;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IAttributedExpr;
import org.smtlib.IExpr.IBinaryLiteral;
import org.smtlib.IExpr.IBinding;
import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IError;
import org.smtlib.IExpr.IExists;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IForall;
import org.smtlib.IExpr.IHexLiteral;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.ILet;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IParameterizedIdentifier;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IResponse.IAssertionsResponse;
import org.smtlib.IResponse.IAssignmentResponse;
import org.smtlib.IResponse.IAttributeList;
import org.smtlib.IResponse.IProofResponse;
import org.smtlib.IResponse.IUnsatCoreResponse;
import org.smtlib.IResponse.IValueResponse;
import org.smtlib.ISort.IAbbreviation;
import org.smtlib.ISort.IApplication;
import org.smtlib.ISort.IFamily;
import org.smtlib.ISort.IFcnSort;
import org.smtlib.ISort.IParameter;

/** This is a visitor interface for visitors over IExpr ASTs. Each AST class implements
 * an accept method that calls the appropriate element of the IVisitor class. An implementation
 * of the IVisitor class will implement an appropriate action in the visit() method.
 * The type parameter T is the return type of the visit method.
 */
public interface IVisitor</*@Nullable*/T extends /*@Nullable*/ Object> {
	public /*@Nullable*/T visit(IAttribute<?> e) throws VisitorException;
	//public /*@Nullable*/T visit(IAttributeValue e) throws VisitorException;
	public /*@Nullable*/T visit(IAttributedExpr e) throws VisitorException;
	public /*@Nullable*/T visit(IBinaryLiteral e) throws VisitorException;
	public /*@Nullable*/T visit(IBinding e) throws VisitorException;
	public /*@Nullable*/T visit(IDecimal e) throws VisitorException;
	public /*@Nullable*/T visit(IError e) throws VisitorException;
	public /*@Nullable*/T visit(IExists e) throws VisitorException;
	public /*@Nullable*/T visit(IFcnExpr e) throws VisitorException;
	public /*@Nullable*/T visit(IForall e) throws VisitorException;
	public /*@Nullable*/T visit(IHexLiteral e) throws VisitorException;
	//public /*@Nullable*/T visit(IIdentifier e) throws VisitorException;
	public /*@Nullable*/T visit(IKeyword e) throws VisitorException;
	public /*@Nullable*/T visit(ILet e) throws VisitorException;
	//public /*@Nullable*/T visit(ILiteral e) throws VisitorException;
	public /*@Nullable*/T visit(INumeral e) throws VisitorException;
	public /*@Nullable*/T visit(IDeclaration e) throws VisitorException;
	public /*@Nullable*/T visit(IParameterizedIdentifier e) throws VisitorException;
	public /*@Nullable*/T visit(IAsIdentifier e) throws VisitorException;
	public /*@Nullable*/T visit(IStringLiteral e) throws VisitorException;
	public /*@Nullable*/T visit(ISymbol e) throws VisitorException;
	public /*@Nullable*/T visit(IScript e) throws VisitorException;
	public /*@Nullable*/T visit(ICommand e) throws VisitorException;
	
	public /*@Nullable*/T visit(ISort.IFamily s) throws VisitorException;
	public /*@Nullable*/T visit(ISort.IAbbreviation s) throws VisitorException;
	public /*@Nullable*/T visit(ISort.IApplication s) throws VisitorException;
	public /*@Nullable*/T visit(ISort.IFcnSort s) throws VisitorException;
	public /*@Nullable*/T visit(ISort.IParameter s) throws VisitorException;
	
	public /*@Nullable*/T visit(ILogic s) throws VisitorException;
	public /*@Nullable*/T visit(ITheory s) throws VisitorException;
	
	public /*@Nullable*/T visit(IResponse e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IError e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IAssertionsResponse e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IAssignmentResponse e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IProofResponse e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IValueResponse e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IUnsatCoreResponse e) throws VisitorException;
	public /*@Nullable*/T visit(IResponse.IAttributeList e) throws VisitorException;

	/** This class is an implementation of IVisitor, meant to be used as a base class
	 * for further derivation; it implements all of the visitors to simply return null
	 * - that is it will not walk the tree without further implementation.
	 * @param <T> the type of the return value of each visitor
	 */
	// FIXME - revisit the annotations. SHould all the methods have Nullable returns or all of them not?
	static public class NullVisitor</*@Nullable*/T extends /*@Nullable*/Object> implements IVisitor</*@Nullable*/T> {

		@Override
		public /*@Nullable*/T visit(IAttribute<?> e) throws VisitorException {
			return null;
		}

//		@Override
//		public /*@Nullable*/T visit(IAttributeValue e) throws VisitorException {
//			return null;
//		}

		@Override
		public /*@Nullable*/T visit(IAttributedExpr e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IBinaryLiteral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IBinding e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IDecimal e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IError e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(org.smtlib.IResponse.IError e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IExists e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IFcnExpr e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IForall e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IHexLiteral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IKeyword e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(ILet e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(INumeral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IDeclaration e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IParameterizedIdentifier e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IAsIdentifier e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IStringLiteral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(ISymbol e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IScript e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(ICommand e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IResponse e) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IFamily s) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IAbbreviation s) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IApplication s) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IFcnSort s) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IParameter s) throws VisitorException {
			return null;
		}

		@Override
		public T visit(ILogic s) throws VisitorException {
			return null;
		}

		@Override
		public T visit(ITheory s) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IAssertionsResponse e) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IAssignmentResponse e) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IProofResponse e) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IValueResponse e) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IUnsatCoreResponse e) throws VisitorException {
			return null;
		}

		@Override
		public T visit(IAttributeList e) throws VisitorException {
			return null;
		}

	}
	
	/** This class is an implementation of IVisitor meant fur further derivation:
	 * each visitor is implemented to visit its children without doing anything else;
	 * the default return value is null.
	 * @param <T> the type of the return value
	 */
	public class TreeVisitor</*@Nullable*/T> implements IVisitor</*@Nullable*/T> {

		@Override
		public /*@Nullable*/T visit(IAttribute<?> e) throws VisitorException {
			e.keyword().accept(this);
			if (e.attrValue() instanceof IAccept) {
				((IAccept)e.attrValue()).accept(this);
			}
			return null;
		}

//		@Override
//		public /*@Nullable*/T visit(IAttributeValue e) throws VisitorException {
//			return null;
//		}

		@Override
		public /*@Nullable*/T visit(IAttributedExpr e) throws VisitorException {
			e.expr().accept(this);
			for (IAttribute<?> a: e.attributes()) a.accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IBinaryLiteral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IBinding e) throws VisitorException {
			e.parameter().accept(this);
			e.expr().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IDecimal e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IError e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(org.smtlib.IResponse.IError e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IExists e) throws VisitorException {
			for (IDeclaration d: e.parameters()) d.accept(this);
			e.expr().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IFcnExpr e) throws VisitorException {
			e.head().accept(this);
			for (IExpr p: e.args()) p.accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IForall e) throws VisitorException {
			for (IDeclaration d: e.parameters()) d.accept(this);
			e.expr().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IHexLiteral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IKeyword e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(ILet e) throws VisitorException {
			for (IBinding d: e.bindings()) d.accept(this);
			e.expr().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(INumeral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IDeclaration e) throws VisitorException {
			e.parameter().accept(this);
			e.sort().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IParameterizedIdentifier e) throws VisitorException {
			e.headSymbol().accept(this);
			for (INumeral n: e.numerals()) n.accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IAsIdentifier e) throws VisitorException {
			e.head().accept(this);
			e.qualifier().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IStringLiteral e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(ISymbol e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IScript e) throws VisitorException {
			for (ICommand c: e.commands()) c.accept(this);
			return null;
		}

		// This should be implemented by each command, so this could be abstract
		// For now at least, we implement it here to avoid the nuisance of 
		// requiring implementations when it is not needed
		@Override
		public /*@Nullable*/T visit(ICommand e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IResponse e) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IFamily s) throws VisitorException {
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IAbbreviation s) throws VisitorException {
			s.identifier().accept(this);
			for (IParameter p: s.parameters()) p.accept(this);
			s.sortExpression().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IApplication s) throws VisitorException {
			s.family().accept(this);
			for (ISort ss: s.parameters()) ss.accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IFcnSort s) throws VisitorException {
			for (ISort ss: s.argSorts()) ss.accept(this);
			s.resultSort().accept(this);
			return null;
		}

		@Override
		public /*@Nullable*/T visit(IParameter s) throws VisitorException {
			s.symbol().accept(this);
			return null;
		}
		
		@Override
		public /*@Nullable*/T visit(ILogic s) throws VisitorException {
			s.logicName().accept(this);
			for (IAttribute<?> attr: s.attributes().values()) {
				attr.accept(this);
			}
			return null;
		}

		@Override
		public /*@Nullable*/T visit(ITheory s) throws VisitorException {
			s.theoryName().accept(this);
			for (IAttribute<?> attr: s.attributes().values()) {
				attr.accept(this);
			}
			return null;
		}

		@Override
		public T visit(IAssertionsResponse e) throws VisitorException {
			for (IExpr t : e.assertions()) {
				t.accept(this);
			}
			return null;
		}

		@Override
		public T visit(IAssignmentResponse e) throws VisitorException {
			for (IResponse.IPair<ISymbol,Boolean> p : e.assignments()) {
				p.first().accept(this);
			}
			return null;
		}

		@Override
		public T visit(IProofResponse e) throws VisitorException {
			// TODO - add content to a proof object
			return null;
		}

		@Override
		public T visit(IValueResponse e) throws VisitorException {
			for (IResponse.IPair<IExpr,IExpr> p : e.values()) {
				p.first().accept(this);
				p.second().accept(this);
			}
			return null;
		}

		@Override
		public T visit(IUnsatCoreResponse e) throws VisitorException {
			for (ISymbol s: e.names()) {
				s.accept(this);
			}
			return null;
		}

		@Override
		public T visit(IAttributeList e) throws VisitorException {
			for (IAttribute<?> a : e.attributes()) {
				a.accept(this);
			}
			return null;
		}

	}

	/** An Exception class to use if there is a problem during execution of an
	 * IVisitor (e.g. in printing or translating formulae). 
	 * @author David R. Cok
	 */
	public static class VisitorException extends Exception implements IPos.IPosable {
		private static final long serialVersionUID = 1L;
		/** Position information about the textual location of the error */
		/*@Nullable*/ /*@ReadOnly*/ public IPos pos; 
		
		@Override
		public /*@Nullable*/ /*@ReadOnly*/IPos pos() { return pos; }
		
		@Override
		public void setPos(/*@Nullable*/ /*@ReadOnly*/IPos pos) { this.pos = pos; }

		/** Constructor for an exception */
		public VisitorException(String msg, /*@Nullable*//*@ReadOnly*/IPos pos) { 
			super(msg); 
			this.pos = pos; 
		}
		
		/** Constructor taking an exception */
		public VisitorException(Throwable e) {
			super(e);
			this.pos = null;
		}
		
		/** Constructor taking an exception */
		public VisitorException(Throwable e, /*@Nullable*/IPos pos) {
			super(e);
			this.pos = pos;
		}
	}

}