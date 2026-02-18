/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.sexpr;

import java.io.*;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.List;

import org.smtlib.*;
import org.smtlib.ICommand.IScript;
import org.smtlib.IExpr.IAsIdentifier;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IAttributedExpr;
import org.smtlib.IExpr.IBinaryLiteral;
import org.smtlib.IExpr.IBinding;
import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.IDeclaration;
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

/** This class writes out SMT-LIB ASTs as concrete S-expression syntax; aside from white space
 * between tokens it should simply reverse what the Parser class does.  */
public class Printer implements IPrinter, org.smtlib.IVisitor</*@Nullable*/ Void> {
	
	static public SMT.Configuration smtConfig;
	
	/** The writer to write text to */
	/*@Nullable*/ protected Writer w;
	
	/** The writer to write text to */
	public Writer writer() { return w; }
	
	/** The system-dependent line termination */
	static public final String eol = System.getProperty("line.separator");

	/** Creates a printer object */
	public Printer(Writer w) {
		this.w = w;
	}
	
	@Override
	public Printer newPrinter(Writer w) {
		return new Printer(w);
	}
	
	/** Prints the argument to the receiver */
	@Override
	public <T extends IAccept> void print(T expr) throws IVisitor.VisitorException {
		expr.accept(this);
	}
	
	/** Returns the argument as a String using a Printer of the same type as the receiver,
	 * but does not modify the receiver.
	 */
	@Override
	public <T extends IAccept> String toString(T expr) {
		try {
			StringWriter sw = new StringWriter();
			expr.accept(new Printer(sw));
			return sw.toString();
		} catch (IVisitor.VisitorException e) {
			return "<<ERROR: " + e.getMessage() + ">>";
		}
	}

	/** Writes the given expression and outputs as a String */
	static public <T extends IAccept> String write(T e) {
		try {
			StringWriter w = new StringWriter();
			e.accept(new Printer(w));
			return w.toString();
		} catch (IVisitor.VisitorException ex) {
			return "<<ERROR: " + ex.getMessage() + ">>";
		}
	}

	/** Writes the given expression to the given writer */
	static public <T extends IAccept> void write(Writer w, T e) throws IVisitor.VisitorException {
		e.accept(new Printer(w));
		try { w.flush(); } catch (IOException ex) { throw new IVisitor.VisitorException(ex); }
	}

	/** Writes the given expression to the given stream */
	static public <T extends IAccept> void write(PrintStream w, T e)  throws IVisitor.VisitorException {
		Writer wr = new OutputStreamWriter(w);
		e.accept(new Printer(wr));
		try { 
			wr.flush(); w.flush(); 
		} catch (IOException ex) { 
			throw new IVisitor.VisitorException(ex); 
		}
	}

	/*@Nullable*/
	@Override
	public Void visit(INumeral e) throws IVisitor.VisitorException {
		try { w.append(e.value().toString()); } catch (IOException ex) { throw new IVisitor.VisitorException(ex); }
		return null;
	}

	/*@Nullable*/
	@Override
	public Void visit(ISymbol e) throws IVisitor.VisitorException { // FIX - need s-expr representation of ids from anywhere
		try { w.append(e.toString()); } catch (IOException ex) { throw new IVisitor.VisitorException(ex); }  
		return null; // FIXME - need an encoding - this gives the original text
	}

	/*@Nullable*/
	@Override
	public Void visit(IDecimal e) throws IVisitor.VisitorException {
		try { w.append(e.value().toPlainString()); } catch (IOException ex) { throw new IVisitor.VisitorException(ex); }
		return null;
	}

	@Override
	public Void visit(IBinaryLiteral e) throws IVisitor.VisitorException {
		try { 
			w.append("#b");
			w.append(e.value()); 
		} catch (IOException ex) { 
			throw new IVisitor.VisitorException(ex); 
		}
		return null;
	}

	@Override
	public Void visit(IHexLiteral e) throws IVisitor.VisitorException {
		try { 
			w.append("#x");
			w.append(e.value());
		} catch (IOException ex) { 
			throw new IVisitor.VisitorException(ex); 
		}
		return null;
	}

	/*@Nullable*/
	@Override
	public Void visit(IStringLiteral e) throws IVisitor.VisitorException {
		// The toString method returns a string that is fully escaped and has enclosing quotes
		try { w.append(e.toString()); } catch (IOException ex) { throw new IVisitor.VisitorException(ex);  }
		return null;
	}

	/*@Nullable*/
	@Override
	public Void visit(IKeyword e) throws IVisitor.VisitorException {
		try { w.append(e.toString()); } catch (IOException ex) { throw new IVisitor.VisitorException(ex);  }
		return null; // FIXME - need an encoding, not the original string
	}

	/*@Nullable*/
	@Override
	public Void visit(org.smtlib.IExpr.IError e) throws IVisitor.VisitorException {
		try { 
			w.append("(error ");
			w.append(smtConfig.utils.quote(e.value())); 
			w.append(")");
		} catch (IOException ex) { throw new IVisitor.VisitorException(ex); }
		return null;
	}

	@Override
	public Void visit(IParameterizedIdentifier e) throws IVisitor.VisitorException {
		try {
			w.append("(" + Utils.UNDERSCORE + " ");
			e.headSymbol().accept(this);
			for (INumeral n: e.numerals()) {
				w.append(" ");
				w.append(n.value().toString());
			}
			w.append(")");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex);
		}
		return null;
	}

	@Override
	public Void visit(IAsIdentifier e) throws IVisitor.VisitorException {
		try {
			w.append("(" + Utils.AS + " ");
			e.head().accept(this);
			w.append(" ");
			e.qualifier().accept(this);
			w.append(")");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex,e.pos());
		}
		return null;
	}

	@Override
	public Void visit(IFcnExpr e) throws IVisitor.VisitorException {
		try {
			w.append("(");
			e.head().accept(this);
			for (IExpr a: e.args()) {
				w.append(" ");
				if (a != null) a.accept(this);
				else w.append("???");
			}
			w.append(")");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex,e.pos());
		}
		return null;
	}

	@Override
	public Void visit(IForall e) throws IVisitor.VisitorException {
		try {
			w.append("(" + Utils.FORALL + " (");
			for (IDeclaration a: e.parameters()) {
				a.accept(this);
				w.append(" ");
			}
			w.append(") ");
			e.expr().accept(this);
			w.append(")");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex,e.pos());
		}
		return null;
	}

	@Override
	public Void visit(IExists e) throws IVisitor.VisitorException {
		try {
			w.append("(" + Utils.EXISTS + " (");
			for (IDeclaration a: e.parameters()) {
				a.accept(this);
				w.append(" ");
			}
			w.append(") ");
			e.expr().accept(this);
			w.append(")");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex,e.pos());
		}
		return null;
	}

	@Override
	public Void visit(ILet e) throws IVisitor.VisitorException {
		try {
			w.append("(" + Utils.LET + " (");
			for (IBinding a: e.bindings()) {
				a.accept(this);
				w.append(" ");
			}
			w.append(") ");
			e.expr().accept(this);
			w.append(")");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex,e.pos());
		}
		return null;
	}

	@Override
	public Void visit(IAttribute<? extends IAttributeValue> e) throws IVisitor.VisitorException {
		try {
			/*@Nullable*/IAttributeValue o;
			e.keyword().accept(this);
			if (e.keyword().toString().equals(":pattern")) w.append(" (");
			if ((o=e.attrValue()) != null) {
				w.append(" ");
				o.accept(this);
			}
            if (e.keyword().toString().equals(":pattern")) w.append(" )");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex,e.pos());
		}
		return null;
	}

	@Override
	public Void visit(IAttributedExpr e) throws IVisitor.VisitorException {
		try {
			w.append("(" + Utils.NAMED_EXPR + " ");
			e.expr().accept(this);
			for (IAttribute<?> a: e.attributes()) {
				w.append(" ");
				a.accept(this);
			}
			w.append(")");
		} catch (IOException ex) {
			throw new VisitorException(ex,e.pos());
		}
		return null;
	}

	@Override
	public Void visit(IDeclaration e) throws IVisitor.VisitorException {
		try {
			w.append("(");
			e.parameter().accept(this);
			w.append(" ");
			e.sort().accept(this);
			w.append(")");
		} catch (IOException ex) {
			throw new VisitorException(ex,e.pos());
		}
		return null;
	}

	@Override
	public Void visit(IBinding e) throws IVisitor.VisitorException {
		try {
			w.append("(");
			e.parameter().accept(this);
			w.append(" ");
			e.expr().accept(this);
			w.append(")");
		} catch (IOException ex) {
			throw new VisitorException(ex,e.pos());
		}
		return null;
	}

	@Override
	public Void visit(IScript e) throws IVisitor.VisitorException {
		int n = 0;
		try {
			IStringLiteral filename = e.filename();
			List<ICommand> commands = e.commands();
			if (filename != null) {
				filename.accept(this);
			} else if (commands != null) {
				w.append("(");
				w.append(eol);
				for (ICommand c: commands) {
					c.accept(this);
					w.append(eol);
					w.flush();
				}
				w.append(")");
			} else {
				w.append("\"<ERROR: Script has no content>\"");
			}
		} catch (IOException ex) {
			throw exc(ex,null);
		}
		return null;
	}
	
	public static class WithLines extends Printer {

		/** Creates a printer object */
		public WithLines(Writer w) {
			super(w);
		}

		@Override
		public WithLines newPrinter(Writer w) {
			return new WithLines(w);
		}
		
		/** Writes the given expression to the given stream */
		static public <T extends IAccept> void write(PrintStream w, T e)  throws IVisitor.VisitorException {
			Writer wr = new OutputStreamWriter(w);
			e.accept(new Printer.WithLines(wr));
			try { 
				wr.flush(); w.flush(); 
			} catch (IOException ex) { 
				throw new IVisitor.VisitorException(ex); 
			}
		}

		@Override
		public Void visit(IScript e) throws IVisitor.VisitorException {
			int n = 0;
			try {
				IStringLiteral filename = e.filename();
				List<ICommand> commands = e.commands();
				if (filename != null) {
					filename.accept(this);
				} else if (commands != null) {
					w.append("(");
					w.append(eol);
					for (ICommand c: commands) {
						w.append((++n) + ": ");
						c.accept(this);
						w.append(eol);
						w.flush();
					}
					w.append(")");
				} else {
					w.append("\"<ERROR: Script has no content>\"");
				}
			} catch (IOException ex) {
				throw exc(ex,null);
			}
			return null;
		}
		

	}

	@Override
	public Void visit(ICommand e) throws IVisitor.VisitorException {
		Class<?> clazz = e.getClass();
		try {
			Method m = clazz.getMethod("write",Printer.class);
			m.invoke(e,this);
		} catch (IllegalAccessException ex) {
			throw new IVisitor.VisitorException(ex,
					e instanceof IPos.IPosable ? ((IPos.IPosable)e).pos() : null);
		} catch (InvocationTargetException ex) {
			throw new VisitorException(ex.getTargetException(),
					e instanceof IPos.IPosable ? ((IPos.IPosable)e).pos() : null);
		} catch (NoSuchMethodException ex) {
			throw new VisitorException("No write method for " + clazz + " and " + this.getClass(),null);
		}
		return null;
	}

	@Override
	public Void visit(IFamily s) throws IVisitor.VisitorException {
		try {
			w.append("( ");
			s.identifier().accept(this);
			w.append(") ");
			s.arity().accept(this);
			w.append(" )");
		} catch (IOException ex) {
			throw exc(ex,s);
		}
		return null;
	}

	@Override
	public Void visit(IAbbreviation s) throws IVisitor.VisitorException {
		try {
			w.append("(");
			s.identifier().accept(this);
			w.append(" (");
			for (ISort ss: s.parameters()) {
				ss.accept(this);
				w.append(" ");
			}
			w.append(") ");
			s.sortExpression().accept(this);
			w.append(")");
		} catch (IOException ex) {
			throw exc(ex,s);
		}
		return null;
	}

	@Override
	public Void visit(IApplication s) throws IVisitor.VisitorException {
		try {
			if (s.parameters().size() == 0) {
				s.family().accept(this);
			} else {
				w.append("(");
				s.family().accept(this);
				for (ISort ss: s.parameters()) {
					w.append(" ");
					ss.accept(this);
				}
				w.append(")");
			}
		} catch (IOException ex) {
			throw exc(ex,s);
		}
		return null;
	}

	@Override
	public Void visit(IFcnSort s) throws IVisitor.VisitorException {
		try {
			w.append("( ");
			for (ISort ss: s.argSorts()) {
				ss.accept(this);
				w.append(" ");
			}
			w.append(") -> ");
			s.resultSort().accept(this);
		} catch (IOException ex) {
			throw exc(ex,s);
		}
		return null;
	}

	@Override
	public Void visit(IParameter s) throws IVisitor.VisitorException {
		s.symbol().accept(this);
		return null;
	}

	@Override
	public Void visit(ILogic s) throws IVisitor.VisitorException {
		try {
			w.append("(logic ");
			s.logicName().accept(this);
			for (IAttribute<?> attr: s.attributes().values()) {
				w.append(" ");
				attr.accept(this);
			}
			w.append(")");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex,null);// TODO - change if ILogic becomes IPosable
		}
		return null;
	}

	@Override
	public Void visit(ITheory s) throws IVisitor.VisitorException {
		try {
			w.append("(theory ");
			s.theoryName().accept(this);
			for (IAttribute<?> attr: s.attributes().values()) {
				w.append(" ");
				attr.accept(this);
			}
			w.append(")");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex,null); // TODO - change if ITheory becomes IPosable
		}
		return null;
	}

	@Override
	public Void visit(IResponse e) throws IVisitor.VisitorException {
		// Since S-expressions are not in the abstract syntax, they
		// end up here
		if (e instanceof ISexpr.ISeq) {
			return visit((ISexpr.ISeq)e);
		} else {
			throw new VisitorException("Undelegated IResponse in Printer for " + e.getClass(),null);
		}
	}
	
	/** Utility function to create an exception using the message from the first argument and the
	 * position from the second, if it is IPosable.
	 */
	public IVisitor.VisitorException exc(Exception ex, Object possiblePos) {
		return new IVisitor.VisitorException(ex,
			possiblePos instanceof IPos.IPosable ? ((IPos.IPosable)possiblePos).pos() : null);
	}
	
	/** Utility function to print error messages in this printer's format */
	public String error(String message) {
		return "(error " + smtConfig.utils.quote(message) + ")";
	}

	@Override
	public Void visit(IResponse.IError e) throws IVisitor.VisitorException {
		try {
			w.append(error(e.errorMsg()));
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex);
		}
		return null;
	}

	@Override
	public Void visit(IAssertionsResponse e) throws IVisitor.VisitorException {
		try {
			w.append("(");
			w.append(eol);
			for (IExpr n : e.assertions()) {
				n.accept(this);
				w.append(eol);
			}
			w.append(")");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex);
		}
		return null;
	}

	@Override
	public Void visit(IAssignmentResponse e) throws IVisitor.VisitorException {
		try {
			w.append("(");
			for (IResponse.IPair<ISymbol,Boolean> p : e.assignments()) {
				w.append("(");
				p.first().accept(this);
				w.append(" ");
				w.append(p.second().toString()); // FIXME - change when we do not use Boolean
				w.append(")");
			}
			w.append(")");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex);
		}
		return null;
	}

	@Override
	public Void visit(IProofResponse e) throws IVisitor.VisitorException {
		// TODO when proofs are defined
		try {
			w.append("PROOF");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex);
		}
		return null;
	}

	@Override
	public Void visit(IValueResponse e) throws IVisitor.VisitorException {
		try {
			w.append("(");
			for (IResponse.IPair<IExpr,IExpr> p : e.values()) {
				w.append("(");
				p.first().accept(this);
				w.append(" ");
				p.second().accept(this);
				w.append(")");
			}
			w.append(")");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex);
		}
		return null;
	}

	@Override
	public Void visit(IUnsatCoreResponse e) throws IVisitor.VisitorException {
		try {
			w.append("(");
			for (ISymbol n : e.names()) {
				n.accept(this);
				w.append(" ");
			}
			w.append(")");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex);
		}
		return null;
	}

	@Override
	public Void visit(IAttributeList e) throws IVisitor.VisitorException {
		try {
			w.append("(");
			for (IAttribute<?> n : e.attributes()) {
				n.accept(this);
				w.append(" ");
			}
			w.append(")");
		} catch (IOException ex) {
			throw new IVisitor.VisitorException(ex);
		}
		return null;
	}

//	public Void visit(ISexpr.IToken<?> e) throws IVisitor.VisitorException {
//		try {
//			expr.accept(this); 
//		} catch (IOException ex) { throw new IVisitor.VisitorException(ex); }
//		return null;
//	}

	/*@Nullable*/
	public Void visit(ISexpr.ISeq e) throws IVisitor.VisitorException {
		try {
			w.append("(");
			for (ISexpr expr: e.sexprs()) { 
				w.append(" "); 
				expr.accept(this); 
			} 
			w.append(" )");
		} catch (IOException ex) { throw new IVisitor.VisitorException(ex); }
		return null;
	}
}
