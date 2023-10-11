/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.io.IOException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.smtlib.ICommand.IScript;
import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.*;
import org.smtlib.ICommand.Idefine_fun;
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
import org.smtlib.IExpr.*;
import org.smtlib.IVisitor.VisitorException;
import org.smtlib.SMT.Configuration.SMTLIB;

// Note - simplify appears to have problems if the set of assertions pushed
// via BG_PUSH are not consistent.  At least, it does not produce counterexample
// information in that case.

/** The adapter that drives the Simplify solver.
 * <P>
 * Note on implementation.  Simplify allows only either pushing an assertion to
 * the background or checking that it is valid.  Assertions that are pushed (via BG_PUSH)
 * appear to be filtered out of counterexamples.  Thus for now we will only use
 * BG_PUSH for background theory axioms; for the rest we will accumulate all assertions
 * into one giant AND (in the conjunction field) and then assert them all at once to Simplify
 * when check-sat is called.  The usual push and pop will not be sent to Simplify - rather
 * we save the state of 'conjunction' ourselves.  This implements the letter if not the
 * spirit of push and pop, and it may have performance implications.  If it does, we'll
 * optimize the implementation then. */
public class Solver_simplify extends Solver_test implements ISolver {
	
	/** Just to hold the command line to launch Simplify */
	String cmds[] = new String[1]; 
	
	/** The external process driver, initialized in start() */
	protected SolverProcess solverProcess;
	
	/** Accumulates the translated expressions from various asserts, in order
	 * to send them all at once with a check-sat command.
	 */
	private String conjunction = "";

	/** The stack on which to save instances of 'conjunction' */
	private List<String> pushesStack = new LinkedList<String>();
	{
		pushesStack.add("");
	}
	
	/** Constructor with standard signature for invocation through reflection */
	public Solver_simplify(SMT.Configuration smtConfig, String executable) {
		super(smtConfig,"");
		cmds[0] = executable;
		solverProcess = new SolverProcess(cmds,">\t",smtConfig.logfile);
	}
	
	@Override
	public IResponse start() {
		super.start();
		solverProcess.start(true);
		try {
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Started simplify");
			solverProcess.sendAndListen("(BG_PUSH (FORALL (B X Y) (IMPLIES (EQ B |@true|) (EQ (" + ite_term + " B X Y) X))))\n");
			solverProcess.sendAndListen("(BG_PUSH (FORALL (B X Y) (IMPLIES (NEQ B |@true|) (EQ (" + ite_term + " B X Y) Y))))\n");
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Failed to assert background formulae at start");
		}
		return smtConfig.responseFactory.success();
	}
	
	@Override
	public IResponse exit() {
		solverProcess.exit();
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("Ended simplify ");
		//process = null;
		return super.exit();
	}

	@Override
	public IResponse assertExpr(IExpr sexpr) {
		IResponse res = super.assertExpr(sexpr);
		if (!res.isOK()) return res;
		try {
			String translatedSexpr = translate(sexpr);
			if (translatedSexpr == null) {
				return smtConfig.responseFactory.error("Failure in translating expression: " + smtConfig.defaultPrinter.toString(sexpr), sexpr.pos());
			}
			conjunction = conjunction + " \n" + translatedSexpr;
			//String s = solverProcess.sendAndListen("(BG_PUSH ",translatedSexpr," )\r\n");
			//System.out.println("HEARD: " + s);
		} catch (VisitorException e) {
			return smtConfig.responseFactory.error(e.getMessage(),e.pos);
		}
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse get_assertions() {
		return super.get_assertions();
	}
	
	@Override
	public IResponse check_sat() {
		IResponse res = super.check_sat();
		if (res.isError()) return res;
		try {
//			String s = solverProcess.sendAndListen("(BG_PUSH (EQ 0 0))\r\n");
//			s = solverProcess.sendAndListen("(EQ 0 1)\r\n");
//			if (s.contains("Valid.")) res = smtConfig.responseFactory.unsat();
//			else if (s.contains("Invalid.")) res = smtConfig.responseFactory.sat();
//			else res = smtConfig.responseFactory.unknown();
			
			String msg = "(NOT (AND TRUE " + conjunction + "\n))\n";
			String s = solverProcess.sendAndListen(msg);
			// FIXME - what about errors in SImplify
			//smtConfig.log.logOut("HEARD: " + s);
			if (s.contains("Valid.")) res = smtConfig.responseFactory.unsat();
			else if (s.contains("Invalid.")) res = smtConfig.responseFactory.sat();
			else res = smtConfig.responseFactory.unknown();
			checkSatStatus = res;
//			s = solverProcess.sendAndListen("(BG_POP)\r\n");
			
		} catch (IOException e) {
			res = smtConfig.responseFactory.error("Failed to check-sat");
		}
		return res;
	}

	@Override
	public IResponse declare_fun(Ideclare_fun cmd) {
		IResponse res = super.declare_fun(cmd);
		if (res.isError()) return res;
		try {
			if (cmd.resultSort().isBool() && cmd.argSorts().size() > 0) {
				StringBuilder sb = new StringBuilder();
				sb.append("(DEFPRED (");
				sb.append(translate(cmd.symbol()));
				int n = cmd.argSorts().size();
				for (int i = 0; i<n; i++) {
					sb.append(" X");  // FIXME - fix this
					sb.append(i);
				}
				sb.append("))\n");
				String s = solverProcess.sendAndListen(sb.toString());
				// FIXME - check for error in s -- System.out.println("HEARD " + s);
				res = smtConfig.responseFactory.success();
			} else {
				res = smtConfig.responseFactory.success();
			}
		} catch (IOException e) {
			res = smtConfig.responseFactory.error("Failed to declare-fun: " + e.getMessage(),null); // FIXME - position?
		} catch (IVisitor.VisitorException e) {
			res = smtConfig.responseFactory.error("Failed to declare-fun: " + e.getMessage(),null);
		}
		return res;
	}

	@Override
	public IResponse define_fun(Idefine_fun cmd) {
		IResponse res = super.define_fun(cmd);
		if (res.isError()) return res;
		try {
			if (cmd.resultSort().isBool() && cmd.parameters().size() > 0) {
				StringBuilder sb = new StringBuilder();
				sb.append("(DEFPRED (");
				sb.append(translate(cmd.symbol()));
				int n = cmd.parameters().size();
				for (int i = 0; i<n; i++) {
					sb.append(" X");
					sb.append(i);
				}
				sb.append("))\n");
				String s = solverProcess.sendAndListen(sb.toString());
				// FIXME - check for error in s -- System.out.println("HEARD " + s);
				res = smtConfig.responseFactory.success();
			} else {
				res = smtConfig.responseFactory.success();
			}
			IExpr.IFactory f = smtConfig.exprFactory;
			assertExpr(f.fcn(f.symbol("="),cmd.symbol(),cmd.expression()));
					
		} catch (IOException e) {
			res = smtConfig.responseFactory.error("Failed to declare-fun: " + e.getMessage(),null); // FIXME - position?
		} catch (IVisitor.VisitorException e) {
			res = smtConfig.responseFactory.error("Failed to declare-fun: " + e.getMessage(),null);
		}
		return res;
	}

	//@ requires number >= 0;
	@Override
	public IResponse pop(int number) {
		IResponse status = super.pop(number);
		if (!status.isOK()) return status;
		try {
			while (--number >= 0) { 
				conjunction = pushesStack.remove(0);
				String s = solverProcess.sendAndListen("(BG_POP)");
				// FIXME - check for error in s -- System.out.println("HEARD " + s);
			}
			return smtConfig.responseFactory.success();
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Failed to push");
		}
	}

	//@ requires number >= 0;
	@Override
	public IResponse push(int number) {
		IResponse status = super.push(number);
		if (!status.isOK()) return status;
		try {
			while (--number >= 0) { 
				pushesStack.add(0,conjunction);
				String s = solverProcess.sendAndListen("(BG_PUSH (EQ 0 0))");
				// FIXME - check for error in s -- System.out.println("HEARD " + s);
			}
			return smtConfig.responseFactory.success();
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Failed to push");
		}
	}

	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
		// FIXME - discrimninate among logics
		boolean lSet = logicSet != null;
		IResponse status = super.set_logic(logicName,pos);
		if (!status.isOK()) return status;
		if (logicName.contains("BV")) {
			return smtConfig.responseFactory.error("The simplify solver does not yet support the bit-vector theory",pos);
		}
		if (lSet) {
			pushesStack.clear();
			push(1);
		}
		return smtConfig.responseFactory.success();

	}

	@Override
	public IResponse set_option(IKeyword option, IAttributeValue value) {
		if (option.value().equals(Utils.PRODUCE_ASSIGNMENTS)) return smtConfig.responseFactory.unsupported();
		if (option.value().equals(Utils.PRODUCE_MODELS)) return smtConfig.responseFactory.unsupported();
		if (option.value().equals(Utils.PRODUCE_PROOFS)) return smtConfig.responseFactory.unsupported();
		if (option.value().equals(Utils.PRODUCE_UNSAT_CORES)) return smtConfig.responseFactory.unsupported();
//		if (option.value().equals(":expand-definitions") && smtConfig.atLeastVersion(SMTLIB.V25)) return smtConfig.responseFactory.unsupported();

		return super.set_option(option,value);
	}

	@Override
	public IResponse set_info(IKeyword option, IAttributeValue value) {
		return super.set_info(option,value);
	}

	@Override
	public IResponse get_option(IKeyword key) {
		String option = key.value();
		if (Utils.INTERACTIVE_MODE.equals(option) && !smtConfig.isVersion(SMTLIB.V20)) option = Utils.PRODUCE_ASSERTIONS;
		IAttributeValue value = options.get(option);
		if (value == null) return smtConfig.responseFactory.unsupported();
		return value;
	}

	@Override
	public IResponse get_info(IKeyword key) {
		super.get_info(key);
		IKeyword option = key;
		IAttributeValue lit;
		if (Utils.ERROR_BEHAVIOR.equals(option)) {
			lit = smtConfig.exprFactory.symbol(Utils.CONTINUED_EXECUTION);
		} else if (Utils.AUTHORS.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString("David Detlefs and Greg Nelson and James B. Saxe");
		} else if (Utils.VERSION.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString("1.5.4");
		} else if (Utils.NAME.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString("simplify");
		} else if (Utils.REASON_UNKNOWN.equals(option)) {
			return smtConfig.responseFactory.unsupported();
		} else if (Utils.ALL_STATISTICS.equals(option)) {
			return smtConfig.responseFactory.unsupported();
		} else {
			return smtConfig.responseFactory.unsupported();
		}
		IAttribute<?> attr = smtConfig.exprFactory.attribute(key,lit);
		return smtConfig.responseFactory.get_info_response(attr);
	}

// Pure overrides are redundant
//	@Override
//	public IResponse declare_sort(Ideclare_sort cmd) {
//		return super.declare_sort(cmd);
//	}
//
//	@Override
//	public IResponse define_fun(Idefine_fun cmd){
//		return super.define_fun(cmd);
//	}
//
//	@Override
//	public IResponse define_sort(Idefine_sort cmd){
//		return super.define_sort(cmd);
//	}
	
	// These are all currently unsupported
//	@Override
//	public IResponse get_proof() {
//		return smtConfig.responseFactory.error("The get-proof command is not implemented for simplify"); // FIXME - get-proof for simplify
//	}
//	
//	@Override
//	public IResponse get_value(IExpr ... terms) {
//		return smtConfig.responseFactory.error("The get-value command is not implemented for simplify"); // FIXME - get-value for simplify
//	}
//	
//	@Override
//	public IResponse get_assignment() {
//		return smtConfig.responseFactory.error("The get-assignment command is not implemented for simplify"); // FIXME - get-assignment for simplify
//	}
//	
//	@Override
//	public IResponse get_unsat_core() {
//		return smtConfig.responseFactory.error("The get-proof command is not implemented for simplify"); // FIXME - get-proof for simplify
//	}

	@Override
	public IResponse get_value(IExpr... terms) {
		TypeChecker tc = new TypeChecker(symTable);
		try {
			for (IExpr term: terms) {
				term.accept(tc);
			}
		} catch (IVisitor.VisitorException e) {
			tc.result.add(smtConfig.responseFactory.error(e.getMessage()));
		} finally {
			if (!tc.result.isEmpty()) return tc.result.get(0); // FIXME - report all errors?
		}
		// FIXME - do we really want to call get-option here? it involves going to the solver?
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_MODELS)))) {
			return smtConfig.responseFactory.error("The get-value command is only valid if :produce-models has been enabled");
		}
		if (!smtConfig.responseFactory.sat().equals(checkSatStatus) && !smtConfig.responseFactory.unknown().equals(checkSatStatus)) {
			return smtConfig.responseFactory.error("A get-value command is valid only after check-sat has returned sat or unknown");
		}
		return smtConfig.responseFactory.unsupported();
	}



	
	public /*@Nullable*/String translate(IExpr expr) throws IVisitor.VisitorException {
		Translator t = new Translator(typemap,smtConfig);
		String r = expr.accept(t);
		if (t.conjuncts.isEmpty()) return r;
		String and = "(AND ";
		for (String c: t.conjuncts) {
			and = and + c + " ";
		}
		and = and + r + " )";
		return and;
	}
	/* Translating simplify:
	 *  Simplify has no type definitions
	 *  It does not require declaring symbols before use - it presumes
	 *  a symbol is a term or a predicate constant or a function when it
	 *  first sees one.  
	 *  New predicates are defined with DEFPRED
	 *  It has a strict distinction between terms and formulas, so
	 *  	- there are different symbols for equality (EQ and IFF)
	 *  	- there are different symbols for inequality (NEQ and (IFF p (NOT q)))
	 *  	- DISTINCT operates only on terms (and the result is a formula)
	 *  
	 *  
	 *  QUESTIONS: what about overloaded functions
	 */
	/*    SMTLIB			SIMPLIFY
	 * FORMULAE:
	 * (or p q r ...)	(OR p q r ...)
	 * (and p q r ...)	(AND p q r ...)
	 * (not p)			(NOT p)
	 * (=> p q r ...)	(IMPLIES p (IMPLIES q r...))
	 * (xor p q r ...)	(NOT ( IFF ( NOT (IFF p q)) r )) ...
	 * (= p q r ...)	(IFF (IFF p q) r)  -- formulas
	 * (= p q r ...)	(AND (EQ p q ) ( EQ q r) ...)  -- terms
	 * (distinct p q r)	-- does not make sense for more than 2 arguments if the arguments are boolean 
	 * (distinct x y z)	(DISTINCT x y z)  -- x,y,z are terms, result is a formula
	 * true				TRUE - when used as a formula
	 * false			FALSE - when used as a formula
	 * (ite b p q)		_ITEB for formula arguments; _ITET for term arguments
	 * 
	 * < <= > >=		< <= > >= - arguments are terms, result is a formula
	 *
	 * TERMS
	 * + - *			+ - *
	 * 	    			select store  - for arrays
	 * 
	 * In simplify EQ NEQ < <= > >= DISTINCT take terms as arguments, produce formulas
	 * how to handle boolean terms???
	 */

	/* Simplify ids:
	 * 		a) sequence of alpha, digits, underscore, beginning with alpha
	 *      b) sequence of ! # $ % & * + - , / : < = > ? @ [ ] ^ _ { } ~
	 *               excludes | ( ) ` \ ; " ' , 
	 * 		c) printable characters and space except \ |, surrounded by |
	 *           - also allows undocumented 'escape sequences'
	 *  To translate from SMT-LIB use form (c), but have to remove
	 *  explicit tabs, newlines, crs; also any \-escape sequences
	 */
	

	/** Name of an if-then-else construct on term arguments */ 
	static private String ite_term = "_ITE";
	
	static Map<String,String> fcnNames = new HashMap<String,String>();
	static Set<String> logicNames = new HashSet<String>();
	static Set<String> reservedWords  = new HashSet<String>();
	static Set<String> nonchainables  = new HashSet<String>();
	static {
		// FIXME - this builds in the theories - we should abstract both the naming and the mappings for arbitrary arguments
		// Translations of SMT-LIB standard concrete names to Simplify names
		// Anything not here is considered to be uninterpreted and the
		// SMT-LIB name will be encoded into a unique Simplify name
		fcnNames.put("or","OR");  // >2 arguments OK for simplify (left-assoc)
		fcnNames.put("not","NOT");
		fcnNames.put("and","AND");  // >2 arguments OK for simplify (left-assoc)
		fcnNames.put("=","EQ");		  // >2 arguments NOT OK for simplify (chainable)
		fcnNames.put("=>","IMPLIES"); // >2 arguments NOT OK for simplify (right-assoc)
		fcnNames.put("distinct","DISTINCT"); // >2 arguments OK for simplify (pairwise)
		fcnNames.put("xor","NEQ");			// >2 arguments NOT OK for simplify (left-assoc)
		fcnNames.put("+","+");				// >2 arguments  OK for simplify (left-assoc)
		fcnNames.put("-","-");				// >2 arguments NOT OK for simplify (left-assoc)
		fcnNames.put("*","*");				// >2 arguments  OK for simplify (left-assoc)
		fcnNames.put(">",">");				// >2 arguments NOT OK for simplify	(left-assoc)		
		fcnNames.put(">=",">=");			// >2 arguments NOT OK for simplify (chainable)
		fcnNames.put("<","<");				// >2 arguments NOT OK for simplify (chainable)
		fcnNames.put("<=","<=");			// >2 arguments NOT OK for simplify (chainable)
		fcnNames.put("true","TRUE");
		fcnNames.put("false","FALSE");
		fcnNames.put("ite",ite_term);
		
		fcnNames.put("select","select");
		fcnNames.put("store","store");

		nonchainables.addAll(Arrays.asList(new String[]{ "EQ", ">", "<", ">=", "<=", "IFF" }));
		
		reservedWords.addAll(Arrays.asList(new String[]
		  { "FORALL","EXISTS","LET",
			"OR","AND","IMPLIES","EXPLIES","XOR","DISTINCT","IFF","NOT","TRUE","FALSE",
			"EQ","NEQ","DISTINCT","PATS",
			"+","-","*",">",">=","<","<=","store","select","@true",
			"LBLPOS","LBLNEG","LBL","ORDER",
			"BG_PUSH","BG_POP","DEFPRED","DEFPREDMAP",
			ite_term,
			}
		));
		
		// These are formulas and take formulas as arguments
		logicNames.addAll(Arrays.asList(new String[]
		   { "OR","AND","IMPLIES","EXPLIES","XOR","IFF","NOT","FORALL","EXISTS"}));
	}
	
	static public class Translator implements IVisitor<String> {
		boolean isFormula = true;
		final private Map<IExpr,ISort> typemap;
		final private SMT.Configuration smtConfig;
		private List<String> conjuncts = new LinkedList<String>();
		
		public Translator(Map<IExpr,ISort> typemap, SMT.Configuration smtConfig) {
			this.typemap = typemap;
			this.smtConfig = smtConfig;
		}

		@Override
		public String visit(IDecimal e) throws IVisitor.VisitorException {
			throw new VisitorException("The simplify solver cannot handle decimal literals",e.pos());
		}

		@Override
		public String visit(IStringLiteral e) throws IVisitor.VisitorException {
			throw new VisitorException("The simplify solver cannot handle string literals",e.pos());
		}

		@Override
		public String visit(INumeral e) throws IVisitor.VisitorException {
			return e.value().toString();
		}

		@Override
		public String visit(IBinaryLiteral e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Binary literal in an expression to be translated",e.pos());
		}

		@Override
		public String visit(IHexLiteral e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Hex literal in an expression to be translated",e.pos());
		}

		@Override
		public String visit(IFcnExpr e) throws IVisitor.VisitorException {
			boolean resultIsFormula = this.isFormula;
			StringBuilder sb = new StringBuilder();
			try {
				Iterator<IExpr> iter = e.args().iterator();
				if (!iter.hasNext()) throw new VisitorException("Did not expect an empty argument list",e.pos());
				if (!(e.head() instanceof ISymbol)) {
					throw new VisitorException("Have not yet implemented parameterized bit-vector functions",e.pos());
				}
				ISymbol fcn = (ISymbol)e.head();
				String newName = fcn.accept(this);
				
				// Determine if the arguments are formulas or terms
				if (resultIsFormula) {
					if (newName != null && logicNames.contains(newName)) {
						// Propositional boolean item
						this.isFormula = true;
					} else if (e.args().size() <= 1) {
						this.isFormula = false;
					} else {
						IExpr arg = e.args().get(1); // Use argument 1 for ite's sake
						ISort sort = typemap.get(arg);
						if (sort == null) {
							throw new VisitorException("INTERNAL ERROR: Encountered an un-sorted expression node: " + smtConfig.defaultPrinter.toString(arg),arg.pos());
						}
						if (sort.isBool()) {
							// Some functions can take both bool and non-bool arguments:
							//   EQ NEQ DISTINCT ite
							this.isFormula = resultIsFormula;
							if ("EQ".equals(newName)) newName = "IFF";
						} else {
							// Arguments must be terms
							this.isFormula = false;
						}
					}
				} else {
					this.isFormula = false;
				}

				ISort s = typemap.get(e);
				if (s == null) {
					throw new VisitorException("INTERNAL ERROR: Encountered an un-sorted expression node: " + smtConfig.defaultPrinter.toString(e),e.pos());
				}
				if (s.isBool() && !resultIsFormula) {
					throw new VisitorException("Use of boolean in a term position is not yet implemented in the Simplify adapter",e.pos()); // FIXME - booleans as terms
				}

				if (isFormula && newName.equals("NEQ")) {
					// for formulas, NEQ is (NOT (IFF p q ...))
					// In simplify, IFF is not implicitly chainable
					int length = e.args().size();
					if ((length&1)==0) sb.append("(NOT ");
					sb.append(leftassoc("IFF",length,iter));
					if ((length&1)==0) sb.append(")");
											
				} else if (newName.equals("IMPLIES")) {
					// right-associative operators that need grouping
					if (!iter.hasNext()) {
						throw new VisitorException("implies (=>) operation without arguments",e.pos());
					}
					sb.append(rightassoc(newName,iter));

				} else if (newName.equals("DISTINCT")) {
					// in simplify, DISTINCT is just for term arguments but the result is a formula
					if (isFormula) {
						// arguments are formulas, result is formula
						if (e.args().size() > 2) {
							// More than two distinct boolean values?
							sb.append("FALSE");
						} else {
							sb.append("(NOT (IFF");
							while (iter.hasNext()) {
								sb.append(" ");
								sb.append(iter.next().accept(this));
							}
							sb.append(" ))");
						}
					} else if (resultIsFormula) {
						// arguments are terms, result is formula - standard use in Simplify
						sb.append("(DISTINCT");
						while (iter.hasNext()) {
							sb.append(" ");
							sb.append(iter.next().accept(this));
						}
						sb.append(")");
					} else {
						// used in a term position
						throw new VisitorException("Use of DISTINCT in a term position is not yet implemented in the Simplify adapter",e.pos()); // FIXME - distinact as a term
					}
				} else if (ite_term.equals(newName)) {
					if (isFormula) {
						sb.append("(AND (IMPLIES ");
						sb.append(e.args().get(0).accept(this));
						sb.append(" ");
						sb.append(e.args().get(1).accept(this));
						sb.append(")");
						sb.append("(IMPLIES (NOT ");
						sb.append(e.args().get(0).accept(this));
						sb.append(") ");
						sb.append(e.args().get(2).accept(this));
						sb.append("))");
					}
				}
				if (e.args().size() > 2 && nonchainables.contains(newName)) {
					Iterator<IExpr> iter2 = e.args().iterator();
					sb.append("(AND ");

					IExpr left = iter2.next();
					while (iter2.hasNext()) {
						IExpr right = iter2.next();
						sb.append("(" + newName + " ");
						sb.append(left.accept(this));
						sb.append(" ");
						sb.append(right.accept(this));
						sb.append(")");
						left = right;
					}
					sb.append(")");
				}
				if (e.args().size() > 2 && (newName.equals("-") || newName.equals("/"))) {
					Iterator<IExpr> iter2 = e.args().iterator();
					sb.append(leftassoc(newName,e.args().size(),iter2));
				}
				
				if (sb.length() == 0) {
					sb.append("( ");
					sb.append(newName);
					while (iter.hasNext()) {
						sb.append(" ");
						sb.append(iter.next().accept(this));
					}
					sb.append(" )");
				}
			} finally {
				this.isFormula = resultIsFormula;
			}
			return sb.toString();
		}
		
		//@ requires iter.hasNext();
		private <T extends IExpr> String rightassoc(String fcnname, Iterator<T> iter ) throws IVisitor.VisitorException {
			T n = iter.next();
			if (!iter.hasNext()) {
				return n.accept(this);
			} else {
				StringBuilder sb = new StringBuilder();
				sb.append("(");
				sb.append(fcnname);
				sb.append(" ");
				sb.append(n.accept(this));
				sb.append(" ");
				sb.append(rightassoc(fcnname,iter));
				sb.append(")");
				return sb.toString();
			}
		}

		//@ requires iter.hasNext();
		//@ requires length > 0;
		private <T extends IExpr> String leftassoc(String fcnname, int length, Iterator<T> iter ) throws IVisitor.VisitorException {
			if (length == 1) {
				return iter.next().accept(this);
			} else {
				StringBuilder sb = new StringBuilder();
				sb.append("(");
				sb.append(fcnname);
				sb.append(" ");
				sb.append(leftassoc(fcnname,length-1,iter));
				sb.append(" ");
				sb.append(iter.next().accept(this));
				sb.append(")");
				return sb.toString();
			}
		}

		@Override
		public String visit(ISymbol e) throws IVisitor.VisitorException {
			// Symbols do not necessarily have sorts - e.g. if they are function names
			ISort sort = typemap.get(e);
			if (!isFormula && sort != null && sort.isBool()) {
				throw new VisitorException("Use of boolean in a term position is not yet implemented in the Simplify adapter",e.pos()); // FIXME - booleans as terms
			}
			// Simplify does not allow tab, newline, cr in identifiers;
			// these are allowed by SMTLIB.
			// Note that neither simplify nor SMTLIB allows \ or |
			// All other printable characters are allowed in both.
			String oldName = e.value();
			String newName = fcnNames.get(oldName);
			if (newName != null) {
				// There is a direct translation of a pre-defined SMT-LIB name
				// into a simplify equivalent - use it.
			} else {
				// Use the ? character as an escape
				newName = oldName.replace("?","??").replace("\n","?n").replace("\r","?r").replace("\t","?t");
				if (reservedWords.contains(newName)) {
					newName = newName + "?!";
				}
				newName = "|" + newName + "|";
			}
			return newName;
		}

		@Override
		public String visit(IKeyword e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Keyword in an expression to be translated",e.pos());
		}

		@Override
		public String visit(IError e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Error token in an expression to be translated",e.pos());
		}

		@Override
		public String visit(IParameterizedIdentifier e) throws IVisitor.VisitorException {
			if (!isFormula && typemap.get(e).isBool()) {
				throw new VisitorException("Use of boolean in a term position is not yet implemented in the Simplify adapter",e.pos()); // FIXME - booleans as terms
			}
			// Since there is no overloading, the head will be a new symbol
			// and we don't need to worry that it collides with a pre- or user-defined
			// function name
			String v = e.headSymbol().accept(this); // This will come back with bars
			if (v.charAt(0) != '|') {
				throw new VisitorException("INTERNAL ERROR: Do not expect to ever have a pre-defined name within a parameterized identifier",e.headSymbol().pos());
			}
			v = v.substring(0,v.length()-1);
			for (INumeral n: e.numerals()) {
				v = v + "?" + n.toString();
			}
			return v + "|";
		}

		@Override
		public String visit(IForall e) throws IVisitor.VisitorException {
			if (!isFormula) {
				throw new VisitorException("Use of forall in a term position is not yet implemented in the Simplify adapter",e.pos()); // FIXME - booleans as terms
			}
			StringBuilder sb = new StringBuilder();
			sb.append("(FORALL (");
			for (IDeclaration d: e.parameters()) {
				if (d.sort().isBool()) {
					throw new VisitorException("Boolean quantifiers are not implemented in the Simplify adapter",e.pos()); // FIXME - booleans as terms
				}
				sb.append(d.parameter().accept(this));
				sb.append(" ");
			}
			sb.append(") ");
			sb.append(e.expr().accept(this));
			sb.append(")");
			return sb.toString();
		}

		@Override
		public String visit(IExists e) throws IVisitor.VisitorException {
			if (!isFormula) {
				throw new VisitorException("Use of exists in a term position is not yet implemented in the Simplify adapter",e.pos()); // FIXME - booleans as terms
			}
			StringBuilder sb = new StringBuilder();
			sb.append("(EXISTS (");
			for (IDeclaration d: e.parameters()) {
				if (d.sort().isBool()) {
					throw new VisitorException("Boolean quantifiers are not implemented in the Simplify adapter",e.pos()); // FIXME - booleans as terms
				}
				sb.append(d.accept(this));
				sb.append(" ");
			}
			sb.append(") ");
			sb.append(e.expr().accept(this));
			sb.append(")");
			return sb.toString();
		}
		
		@Override 
		public String visit(IDeclaration e) throws IVisitor.VisitorException {
			StringBuilder sb = new StringBuilder();
			sb.append(e.parameter().accept(this));
			return sb.toString();
		}

		@Override
		public String visit(ILet e) throws IVisitor.VisitorException {
			// Simplify does not have let
			// We can create a new temp variable (or function of any quantified parameters)
			// and then use that.
			for (IBinding b : e.bindings()) {
				String r = b.expr().accept(this);
				ISort s = typemap.get(b.expr());
				// FIXME - don't use toString - also need to map to a unique new temporary
				r = (s.isBool()? "(IFF " : "(EQ ") + b.parameter().accept(this) + " " + r + " )";
				conjuncts.add(r);
			}
			return e.expr().accept(this);
			//throw new VisitorException("Use of let is not yet implemented in the Simplify adapter",e.pos()); // FIXME - let in Simplify
		}

		@Override 
		public String visit(IBinding e) throws IVisitor.VisitorException {
//			StringBuilder sb = new StringBuilder();
//			sb.append(e.parameter().accept(this));
//			return sb.toString();
			throw new VisitorException("Use of bindings is not yet implemented in the Simplify adapter",e.pos()); // FIXME - let in Simplify
		}

		@Override
		public String visit(IAttribute<?> e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IAttributedExpr e) throws VisitorException {
			// FIXME - ignoring the name - should use a LBL expression
			StringBuilder sb = new StringBuilder();
			sb.append("(LBL ");
			sb.append(e.attributes().get(0).attrValue().toString()); // Use the standard printer FIXME
			sb.append(" ");
			sb.append(e.expr().accept(this));
			sb.append(")");
			return sb.toString();
		}

		@Override
		public String visit(org.smtlib.IResponse.IError e)
				throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IAsIdentifier e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IScript e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(ICommand e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IFamily s) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IAbbreviation s) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IApplication s) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IFcnSort s) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IParameter s) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(ILogic s) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(ITheory s) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IResponse e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IAssertionsResponse e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IAssignmentResponse e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IProofResponse e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IValueResponse e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IUnsatCoreResponse e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String visit(IAttributeList e) throws VisitorException {
			// TODO Auto-generated method stub
			return null;
		}


//		@Override
//		public String visit(IScript e) throws IVisitor.VisitorException {
//			throw new VisitorException(e,"Did not expect a Script in an expression to be translated");
//		}

//		@Override
//		public String visit(IResponse e) throws IVisitor.VisitorException {
//			throw new VisitorException(e,"Did not expect a IResponse in an expression to be translated");
//		}
//		
	}


}
