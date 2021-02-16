package org.smtlib.solvers;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.io.StringWriter;
import java.io.Writer;

import org.smtlib.IAccept;
import org.smtlib.IVisitor;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IExists;
import org.smtlib.IExpr.IForall;
import org.smtlib.sexpr.Utils;


public class Printer extends org.smtlib.sexpr.Printer {

	/** Creates a printer object */
	public Printer(Writer w) {
		super(w);
	}
	
	@Override
	public Printer newPrinter(Writer w) {
		return new Printer(w);
	}
	
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
	
	@Override
	public Void visit(IForall e) throws IVisitor.VisitorException {
		if (e.parameters().size() == 1 && e.parameters().get(0).sort().isBool()) {
			try {
				w.append("(and (" + Utils.LET + " ((");
				for (IDeclaration a: e.parameters()) {
					a.parameter().accept(this);
					w.append(" true)) ");
				}
				e.expr().accept(this);
				w.append(") (" + Utils.LET + " ((");
				for (IDeclaration a: e.parameters()) {
					a.parameter().accept(this);
					w.append(" false)) ");
				}
				e.expr().accept(this);
				w.append("))");
			} catch (IOException ex) {
				throw new IVisitor.VisitorException(ex,e.pos());
			}
			return null;
		} else {
			return super.visit(e);
		}
	}

	@Override
	public Void visit(IExists e) throws IVisitor.VisitorException {
		if (e.parameters().size() == 1 && e.parameters().get(0).sort().isBool()) {
			try {
				w.append("(or (" + Utils.LET + " ((");
				for (IDeclaration a: e.parameters()) {
					a.parameter().accept(this);
					w.append(" true)) ");
				}
				e.expr().accept(this);
				w.append(") (" + Utils.LET + " ((");
				for (IDeclaration a: e.parameters()) {
					a.parameter().accept(this);
					w.append(" false)) ");
				}
				e.expr().accept(this);
				w.append("))");
			} catch (IOException ex) {
				throw new IVisitor.VisitorException(ex,e.pos());
			}
			return null;
		} else {
			return super.visit(e);
		}
	}



}
