package org.smtlib.solvers;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.smtlib.*;
import org.smtlib.IExpr.IBinaryLiteral;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IHexLiteral;
import org.smtlib.IExpr.IParameterizedIdentifier;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.sexpr.ISexpr;
import org.smtlib.sexpr.ISexpr.ISeq;
import org.smtlib.sexpr.Sexpr;

public class Solver_z3_2_11 extends Solver_z3_4_3 {

	/** Creates an instance of the Z3 solver */
	public Solver_z3_2_11(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
		super(smtConfig,executable);
		cmds = new String[]{ executable, "/smt2","/in","/m"}; 
		solverProcess.setCmd(cmds);
		NAME_VALUE = "z3-2.11";
		VERSION_VALUE = "2.11";
	}

	@Override
	public IResponse start() {
		try {
			solverProcess.start(false);
			// FIXME - enable the following lines when the Z3 solver supports them
//			if (smtConfig.solverVerbosity > 0) solverProcess.sendNoListen("(set-option :verbosity ",Integer.toString(smtConfig.solverVerbosity),")");
//			if (!smtConfig.batch) solverProcess.sendNoListen("(set-option :interactive-mode true)"); // FIXME - not sure we can do this - we'll lose the feedback
			// Can't turn off printing success, or we get no feedback
			//solverProcess.sendAndListen("(set-option :print-success true)\n"); // Z3 4.3.0 needs this because it mistakenly has the default for :print-success as false
			//if (smtConfig.nosuccess) solverProcess.sendAndListen("(set-option :print-success false)");
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Started Z3-2.11 ");
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}
	
	@Override 
	public IResponse get_value(IExpr... terms) {
		// FIXME - do we really want to call get-option here? it involves going to the solver?
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_MODELS)))) {
			return smtConfig.responseFactory.error("The get-value command is only valid if :produce-models has been enabled");
		}
		if (!smtConfig.responseFactory.sat().equals(checkSatStatus) && !smtConfig.responseFactory.unknown().equals(checkSatStatus)) {
			return smtConfig.responseFactory.error("A get-value command is valid only after check-sat has returned sat or unknown");
		}
		try {
			solverProcess.sendNoListen("(get-value (");
			for (IExpr e: terms) {
				solverProcess.sendNoListen(" ",translate(e));
			}
			String r = solverProcess.sendAndListen("))\n");
			IResponse response = parseResponse(r);
			if (response instanceof ISeq) {
				List<ISexpr> valueslist = new LinkedList<ISexpr>();
				Iterator<ISexpr> iter = ((ISeq)response).sexprs().iterator();
				for (IExpr e: terms) {
					if (!iter.hasNext()) break;
					List<ISexpr> values = new LinkedList<ISexpr>();
					values.add(new Sexpr.Expr(e));
					values.add(iter.next());
					valueslist.add(new Sexpr.Seq(values));
				}	
				return new Sexpr.Seq(valueslist);
			}
			return response;
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	/** Translates an S-expression into Z3 syntax */
	@Override
	protected String translate(IAccept sexpr) throws IVisitor.VisitorException {
		// The z3 solver uses the standard S-expression concrete syntax, but not quite
		// so we have to use our own translator
		StringWriter sw = new StringWriter();
		sexpr.accept(new Translator(sw));
		return sw.toString();
	}
	
	public class Translator extends Solver_z3_4_3.Translator {
		
		public Translator(Writer w) { super (w); }
		
		@Override
		public Void visit(IBinaryLiteral e) throws IVisitor.VisitorException {
			try {
				w.append( "bv" + e.intValue() + "[" + e.length() + "]" );
			} catch (IOException ex) {
				throw new IVisitor.VisitorException(ex,e.pos());
			}
			return null;
		}

		@Override
		public Void visit(IHexLiteral e) throws IVisitor.VisitorException {
			try {
				w.append( "bv" + e.intValue() + "[" + (4*e.length()) + "]" );
			} catch (IOException ex) {
				throw new IVisitor.VisitorException(ex,e.pos());
			}
			return null;
		}

//		@Override
//		public String visit(IAttributedExpr e) throws IVisitor.VisitorException {
//			return e.expr().accept(this); // FIXME - not doing anything with names
//		}

		@Override
		public Void visit(IParameterizedIdentifier e) throws IVisitor.VisitorException {
			try {
				String s = e.headSymbol().toString();
				if (s.matches("bv[0-9]+")) {
					int length = e.numerals().get(0).intValue();
					w.append( s + "[" + length + "]" );
				} else {
					super.visit(e);
				}
			} catch (IOException ex) {
				throw new IVisitor.VisitorException(ex,e.pos());
			}
			return null;
		}

//		@Override
//		public Void visit(IForall e) throws IVisitor.VisitorException {
//			try {
//				w.append("(forall (");
//				for (IDeclaration d: e.parameters()) {
//					w.append("(");
//					d.parameter().accept(this);
//					w.append(" ");
//					d.sort().accept(this);
//					w.append(")");
//				}
//				w.append(") ");
//				e.expr().accept(this);
//				w.append(")");
//			} catch (IOException ex) {
//				throw new IVisitor.VisitorException(ex,e.pos());
//			}
//			return null;
//		}
//
//		@Override
//		public Void visit(IExists e) throws IVisitor.VisitorException {
//			try {
//				w.append("(exists (");
//				for (IDeclaration d: e.parameters()) {
//					w.append("(");
//					d.parameter().accept(this);
//					w.append(" ");
//					d.sort().accept(this);
//					w.append(")");
//				}
//				w.append(") ");
//				e.expr().accept(this);
//				w.append(")");
//			} catch (IOException ex) {
//				throw new IVisitor.VisitorException(ex,e.pos());
//			}
//			return null;
//		}
//
//		@Override
//		public String visit(ILet e) throws IVisitor.VisitorException {
//			StringBuffer sb = new StringBuffer();
//			sb.append("(let (");
//			for (IBinding d: e.bindings()) {
//				sb.append("(");
//				sb.append(d.parameter().accept(this));
//				sb.append(" ");
//				sb.append(d.expr().accept(this));
//				sb.append(")");
//			}
//			sb.append(") ");
//			sb.append(e.expr().accept(this));
//			sb.append(")");
//			return sb.toString();
//		}

		@Override
		public Void visit(IFcnExpr e) throws IVisitor.VisitorException {
			try {
				Iterator<IExpr> iter = e.args().iterator();
				if (!iter.hasNext()) throw new VisitorException("Did not expect an empty argument list",e.pos());
				IQualifiedIdentifier fcn = e.head();
				String fcnname = fcn.toString(); // FIXME - fcn.accept(this);
				int length = e.args().size();
				if (fcnname.equals("=") || fcnname.equals("<") || fcnname.equals(">") || fcnname.equals("<=") || fcnname.equals(">=")) {
					// chainable
					chainable(fcnname,iter);
				} else if (fcnname.equals("xor")) {
					// left-associative operators that need grouping
					leftassoc(fcnname,length,iter);
				} else if (length > 1 && fcnname.equals("-")) {
					// left-associative operators that need grouping
					leftassoc(fcnname,length,iter);
				} else if (fcnname.equals("=>")) {
					// right-associative operators that need grouping
					if (!iter.hasNext()) {
						throw new VisitorException("=> operation without arguments",e.pos());
					}
					rightassoc(fcnname,iter);
				} else {
					// no associativity 
					w.append("( ");
					w.append(fcnname);
					while (iter.hasNext()) {
						w.append(" ");
						iter.next().accept(this);
					}
					w.append(" )");
				}
			} catch (IOException ex) {
				throw new IVisitor.VisitorException(ex,e.pos());
			}
			return null;
		}
			
	}

}
