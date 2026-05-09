/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.*;

import org.smtlib.ICommand.Ideclare_const;
import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.ICommand.Ideclare_sort;
import org.smtlib.ICommand.Idefine_fun;
import org.smtlib.ICommand.Idefine_sort;
import org.smtlib.*;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IPos.IPosable;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.impl.Response;

/** This class is a Solver implementation that simply type-checks formulae and checks that
 * commands are used correctly; it does not do any proving.
 */
public class Solver_test implements ISolver {
	
	/** A reference to the configuration used by this SMT instance. */
	protected SMT.Configuration smtConfig;
	
	/** Returns the reference to the configuration currently in use. */
	public SMT.Configuration smt() { return smtConfig; }

	/** The symbol table used by this solver */
	public SymbolTable symTable; // TODO - public for the sake of C_what - change to protected
	
	/** The data structure that maintains the solver's assertion set stack */
	protected List<List<IExpr>> assertionSetStack = new LinkedList<List<IExpr>>();
	
	/** Internal state variable - set non-null once the logic is set. */
	protected String logicSet = null;
	
	/** Internal state variable - set to sat, unsat, unknown when check-sat is run
	 * and then to null whenever an additional push, popo, assert, declare- or define-
	 * command is executed.  This is used in checking those commands that depend on the
	 * above set of conditions.
	 */
	protected /*@Nullable*/IResponse checkSatStatus;
	
	public /*@Nullable*/IResponse checkSatStatus() { return checkSatStatus; }

	/** A map holding the sorts of subexpressions, used for distinguishing formulas and terms
	 * for solvers for which that needs to be done.
	 */
	protected Map<IExpr,ISort> typemap = new HashMap<IExpr,ISort>();
	
	/** The data structure that maintains the current values of options and info items for this solver. */
	protected Map<String,IAttributeValue> options = new HashMap<String,IAttributeValue>();
	
	
	
	/** Constructor for an instance of this test solver class; the second argument is ignored - it is 
	 * present just for uniformity with other solvers, for which that argument is a path to the relevant
	 * executable.  This constructor is called by reflection, upon knowing the name of the solver ("test").
	 * @param smtConfig a reference to the configuration instance in use
	 * @param exec the executable for the solver, ignored for the case of this test solver
	 */
	public Solver_test(SMT.Configuration smtConfig, String exec) {
		this.smtConfig = smtConfig;
		options.putAll(smt().utils.defaults);
		this.symTable = new SymbolTable(smtConfig);
		checkSatStatus = null;
	}
	
	@Override
	public IResponse start() {
		assertionSetStack.add(0,new LinkedList<IExpr>());
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#start");
		return smtConfig.responseFactory.success();
	}
	
	@Override
	public IResponse reset() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#reset");
		assertionSetStack.clear();
		assertionSetStack.add(0,new LinkedList<IExpr>());
		symTable.clear(false);
		typemap.clear();
		logicSet = null;
		// Set all options and info to default values
		options.putAll(smt().utils.defaults);
		((Response.Factory)smtConfig.responseFactory).printSuccess = true;
		smtConfig.verbose = 0;
		smtConfig.log.out = System.out;
		smtConfig.log.diag = System.err;
		smtConfig.globalDeclarations = false;
		checkSatStatus = null;

		return smtConfig.responseFactory.success();
	}

	@Override public void comment(String comment) {
		// No action
	}
	
	@Override
	public IResponse reset_assertions() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#reset-assertions");
		// Remove all pushed frames
		IResponse r = pop(assertionSetStack.size()-1);
		// Remove assertions, but not necessarily global declarations
		assertionSetStack.get(0).clear();
		if (!smt().globalDeclarations) {
			symTable.clear(true);
			// FIXME - should we do anything with typemap? In general isn't typemap a big leaky thing?
		}
		return r;
	}

	@Override
	public IResponse exit() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#exit");
		return smtConfig.responseFactory.success();
	}
	
	@Override
	public void forceExit() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#forceexit");
	}
	
	@Override
	public IResponse echo(IStringLiteral arg) {
		return arg;
	}

	@Override
	public IResponse assertExpr(IExpr expr) {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#assert " + expr);
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before an assert command is issued");
		}
		List<IResponse> errs = TypeChecker.check(this.symTable,expr,typemap);
		if (errs != null && !errs.isEmpty()) {
			return errs.get(0); // FIXME - return all errors, not just the first
		}
		if (assertionSetStack.isEmpty()) {
			return smtConfig.responseFactory.error("All assertion sets have been popped from the stack");
		}
		assertionSetStack.get(0).add(expr);
		checkSatStatus = null;
		return smtConfig.responseFactory.success();
	}
	
	@Override
	public IResponse get_assertions() {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a get-assertions command is issued");
		}
		// FIXME - do we really want to call get-option here? it involves going to the solver?
		if (!smtConfig.relax && !Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_ASSERTIONS)))) {
			String key;
			if (smtConfig.atLeastVersion(SMTLIB.V25)) key = ":produce-assertions";
			else key = ":interactive-mode";
			return smtConfig.responseFactory.error("The get-assertions command is only valid if " + key + " has been enabled");
		}
		List<IExpr> combined = new LinkedList<IExpr>();
		Iterator<List<IExpr>> iter = assertionSetStack.listIterator();
		addAssertions(combined,iter);
		return smtConfig.responseFactory.get_assertions_response(combined);
	}
	
	/** This method adds all the IExpr items in the lists produced from the iter argument into
	 * the list referenced by the combined argument; the resulting order is to have the items on the
	 * end of the iter sequence added first into the combined list.
	 * @param combined the resulting combined, in-order, sequence of 
	 * @param iter an iterator producing a sequence of Lists of IExpr
	 */
	private void addAssertions(List<IExpr> combined, Iterator<List<IExpr>> iter) {
		if (iter.hasNext()) {
			List<IExpr> list = iter.next();
			addAssertions(combined,iter);
			combined.addAll(list);
		}
	}

	@Override
	public IResponse check_sat() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#check-sat");
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a check-sat command is issued");
		}
		checkSatStatus = smtConfig.responseFactory.unknown();
		return checkSatStatus;
	}
	
	@Override
	public IResponse check_sat_assuming(IExpr ... exprs) {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#check-sat-assuming");
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a check-sat-assuming command is issued");
		}
		for (IExpr e: exprs) {
			if (e instanceof IFcnExpr && ((IFcnExpr)e).args().size() != 0) {
				IFcnExpr f = (IFcnExpr)e;
				if (f.args().size() != 1 || !f.head().toString().equals("not")) {
					return smtConfig.responseFactory.error("Each element of a check-sat-assuming command must be either p or (not p), where p is a Bool constant");
				}
				e = f.args().get(0);
			}
			if (!(e instanceof IIdentifier)) {
				return smtConfig.responseFactory.error("Expected a simple identifier: " + e); // FIXME - use pretty printer?
			}
			List<IResponse> responses = TypeChecker.check(symTable, e);
			if (!responses.isEmpty()) return responses.get(0); // FIXME - return all?
			List<SymbolTable.Entry> entries = symTable.lookup((IIdentifier)e).get(0);
			if (entries.size() != 1) {
				return smtConfig.responseFactory.error("No zero-arity declaration of symbol " + e); // FIXME - use pretty printer?
			}
			if (!entries.get(0).sort.isBool()) {
				return smtConfig.responseFactory.error("Expected a Bool symbol: " + e + " has sort " + entries.get(0).sort); // FIXME - use pretty printer?
			}
		}
		
		checkSatStatus = smtConfig.responseFactory.unknown();
		return checkSatStatus;
	}
	
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
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_MODELS)))) {
			return smtConfig.responseFactory.error("The get-value command is only valid if :produce-models has been enabled");
		}
		if (!smtConfig.responseFactory.sat().equals(checkSatStatus) && !smtConfig.responseFactory.unknown().equals(checkSatStatus)) {
			return smtConfig.responseFactory.error("A get-value command is valid only after check-sat has returned sat or unknown");
		}
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse get_assignment() {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_ASSIGNMENTS)))) {
			return smtConfig.responseFactory.error("The get-assignment command is only valid if :produce-assignments has been enabled");
		}
		if (checkSatStatus != smtConfig.responseFactory.sat() && checkSatStatus != smtConfig.responseFactory.unknown()) {
			return smtConfig.responseFactory.error("The get-assignment command is only valid immediately after check-sat returned sat or unknown");
		}
		return smtConfig.responseFactory.unsupported();
	}
	
	@Override
	public IResponse get_proof() {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_PROOFS)))) {
			return smtConfig.responseFactory.error("The get-proof command is only valid if :produce-proofs has been enabled");
		}
		if (checkSatStatus != smtConfig.responseFactory.unsat()) {
			return smtConfig.responseFactory.error("The get-proof command is only valid immediately after check-sat returned unsat");
		}
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse get_model() {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_MODELS)))) {
			return smtConfig.responseFactory.error("The get-model command is only valid if :produce-models has been enabled");
		}
		if (checkSatStatus == smtConfig.responseFactory.unsat()) {
			return smtConfig.responseFactory.error("The get-model command is only valid immediately after check-sat returned sat or unknown");
		}
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse get_unsat_core() {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_UNSAT_CORES)))) {
			return smtConfig.responseFactory.error("The get-unsat-core command is only valid if :produce-unsat-cores has been enabled");
		}
		if (checkSatStatus != smtConfig.responseFactory.unsat()) {
			return smtConfig.responseFactory.error("The get-unsat-core command is only valid immediately after check-sat returned unsat");
		}
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse pop(int number) {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#pop " + number);
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a pop command is issued");
		}
		if (number < 0) throw new SMT.InternalException("Internal bug: A pop command called with a negative argument: " + number);
		if (assertionSetStack.size() <= number) {
			return smtConfig.responseFactory.error("The argument to a pop command is too large: " + number + " vs. a maximum of " + (assertionSetStack.size()-1));
		} else {
			while (--number >= 0) {
				assertionSetStack.remove(0); 
				symTable.pop(); 
			}
		}
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("###stack size " + assertionSetStack.size());
		checkSatStatus = null;
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse push(int number) {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#push " + number);
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a push command is issued");
		}
		if (number < 0) throw new SMT.InternalException("Internal bug: A push command called with a negative argument: " + number);
		while (--number >= 0) { 
			assertionSetStack.add(0,new LinkedList<IExpr>()); 
			symTable.push(); 
		}
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("###stack size " + assertionSetStack.size());
		checkSatStatus = null;
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#set-logic " + logicName);
		if (logicSet != null) {
			if (!smtConfig.relax) return smtConfig.responseFactory.error("Logic is already set");
			symTable.clear(false);
			assertionSetStack.clear();
			assertionSetStack.add(0,new LinkedList<IExpr>());
		}
		IResponse res = smtConfig.utils.loadLogic(logicName,symTable,pos);
		if (res != null) return res;
		logicSet = logicName;
		return smtConfig.responseFactory.success();
	}
	
	@Override
	public IResponse set_option(IKeyword key, IAttributeValue value) { // FIXME - only strictlyl supported options
		String option = key.value();
		if (Utils.PRINT_SUCCESS.equals(option)) {
			if (!(Utils.TRUE.equals(value) || Utils.FALSE.equals(value))) {
				// This message is duplicated in the C_set_option constructor
//				return smtConfig.responseFactory.error("The value of the " + option + " option must be 'true' or 'false'");
			} else {
				// FIXME - make this more abstract
				((Response.Factory)smtConfig.responseFactory).printSuccess = !Utils.FALSE.equals(value);
			}
		}
		if (logicSet != null && (Utils.INTERACTIVE_MODE.equals(option)||Utils.PRODUCE_ASSERTIONS.equals(option))) {
			return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
		}
//		if (Utils.PRODUCE_ASSIGNMENTS.equals(option) || 
//				//Utils.PRODUCE_MODELS.equals(option) || 
//				Utils.PRODUCE_PROOFS.equals(option) ||
//				Utils.PRODUCE_UNSAT_CORES.equals(option)) {
//			if (logicSet) return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
//			return smtConfig.responseFactory.unsupported();
//		}
		if (Utils.VERBOSITY.equals(option)) {
			IAttributeValue v = options.get(option);
			smtConfig.verbose = (v instanceof INumeral) ? ((INumeral)v).intValue() : 0;
		} else if (Utils.DIAGNOSTIC_OUTPUT_CHANNEL.equals(option)) {
			// Actually, v should never be anything but IStringLiteral - that should
			// be checked during parsing
			String name = (value instanceof IStringLiteral)? ((IStringLiteral)value).value() : "stderr";
			if (name.equals("stdout")) {
				smtConfig.log.diag = System.out;
			} else if (name.equals("stderr")) {
				smtConfig.log.diag = System.err;
			} else {
				try {
					FileOutputStream f = new FileOutputStream(name,true); // append
					smtConfig.log.diag = new PrintStream(f);
				} catch (java.io.IOException e) {
					return smtConfig.responseFactory.error("Failed to open or write to the diagnostic output " + e.getMessage(),value.pos());
				}
			}
		} else if (Utils.REGULAR_OUTPUT_CHANNEL.equals(option)) {
			// Actually, v should never be anything but IStringLiteral - that should
			// be checked during parsing
			String name = (value instanceof IStringLiteral)?((IStringLiteral)value).value() : "stdout";
			if (name.equals("stdout")) {
				smtConfig.log.out = System.out;
			} else if (name.equals("stderr")) {
				smtConfig.log.out = System.err;
			} else {
				try {
					FileOutputStream f = new FileOutputStream(name,true); // append
					smtConfig.log.out = new PrintStream(f);
				} catch (java.io.IOException e) {
					return smtConfig.responseFactory.error("Failed to open or write to the regular output " + e.getMessage(),value.pos());
				}
			}
		} else if (Utils.GLOBAL_DECLARATIONS.equals(option)) {
			smtConfig.globalDeclarations = Utils.TRUE.equals(value);
		}
		if (Utils.INTERACTIVE_MODE.equals(option) && !smtConfig.isVersion(SMTLIB.V20)) option = Utils.PRODUCE_ASSERTIONS;
		options.put(option,value);
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse get_option(IKeyword key) {
		String v = key.value();
		if (Utils.INTERACTIVE_MODE.equals(v) && !smtConfig.isVersion(SMTLIB.V20)) v = Utils.PRODUCE_ASSERTIONS;
		IAttributeValue value = options.get(v);
		//if (smtConfig.isVersion(SMTLIB.V20))
		if (value == null) return smtConfig.responseFactory.unsupported();
		return value;
	}
	
	@Override
	public IResponse set_info(IKeyword key, IAttributeValue value) {
		if (Utils.infoKeywords.contains(key)) {
			return smtConfig.responseFactory.error("Setting the value of a pre-defined keyword is not permitted: "+ 
					smtConfig.defaultPrinter.toString(key),key.pos());
		}
		options.put(key.value(),value);
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse get_info(IKeyword key) { // FIXME - only strictly supported infoflags
		IKeyword option = key;
		IAttributeValue lit;
		if (Utils.ERROR_BEHAVIOR.equals(option)) {
			lit = smtConfig.exprFactory.symbol(Utils.CONTINUED_EXECUTION);
		} else if (Utils.NAME.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString(org.smtlib.Utils.TEST_SOLVER);
		} else if (Utils.AUTHORS.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString(Utils.AUTHORS_VALUE);
		} else if (Utils.VERSION.equals(option)) {
			lit = smtConfig.exprFactory.unquotedString(Utils.VERSION_VALUE);
			
		} else if (Utils.REASON_UNKNOWN.equals(option)) {
			return smtConfig.responseFactory.unsupported();
		} else if (Utils.ALL_STATISTICS.equals(option)) {
			return smtConfig.responseFactory.unsupported();
			
//		} else if ((value = Utils.stringInfo.get(option)) != null) {
//			lit = smtConfig.exprFactory.unquotedString(value);
		} else {
			return smtConfig.responseFactory.unsupported();
		}
		IAttribute<?> attr = smtConfig.exprFactory.attribute(key,lit);
		return smtConfig.responseFactory.get_info_response(attr);
	}
	
	protected String encode(IIdentifier id) {
		return id.toString(); // FIXME composite definitions; encode the String?
	}

	@Override 
	public IResponse declare_const(Ideclare_const cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-const command is issued");// FIXME - position and on other similar statements
		}
		String encodedName = encode(cmd.symbol());
		List<IResponse> list = TypeChecker.checkFcn(symTable, cmd.symbol(), new LinkedList<ISort>(), cmd.resultSort(),cmd instanceof IPosable ? ((IPosable)cmd).pos(): null);
		if (list.isEmpty()) {
			ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(new ISort[0],cmd.resultSort());
			SymbolTable.Entry entry = new SymbolTable.Entry(cmd.symbol(),fcnSort,null);
			if (symTable.add(entry,false)) { 
				checkSatStatus = null;
				return smtConfig.responseFactory.success();
			} else {
				return smtConfig.responseFactory.error("Symbol " + encodedName + " is already defined",cmd.symbol().pos());
			}
		} else {
			return list.get(0); // FIXME - return all?
		}
	}

	@Override 
	public IResponse declare_fun(Ideclare_fun cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-fun command is issued");// FIXME - position and on other similar statements
		}
		String encodedName = encode(cmd.symbol());
		List<IResponse> list = TypeChecker.checkFcn(symTable, cmd.symbol(), cmd.argSorts(),cmd.resultSort(),cmd instanceof IPosable ? ((IPosable)cmd).pos(): null);
		if (list.isEmpty()) {
			ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(cmd.argSorts().toArray(new ISort[cmd.argSorts().size()]),cmd.resultSort());
			SymbolTable.Entry entry = new SymbolTable.Entry(cmd.symbol(),fcnSort,null);
			if (symTable.add(entry,false)) { 
				checkSatStatus = null;
				return smtConfig.responseFactory.success();
			} else {
				return smtConfig.responseFactory.error("Symbol " + encodedName + " is already defined",cmd.symbol().pos());
			}
		} else {
			return list.get(0); // FIXME - return all?
		}
	}

	@Override
	public IResponse define_fun(Idefine_fun cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a define-fun command is issued");
		}
		String encodedName = encode(cmd.symbol());
		List<IResponse> list = TypeChecker.checkFcn(symTable, typemap, cmd.symbol(), cmd.parameters(),cmd.resultSort(),cmd.expression(),cmd instanceof IPosable ? ((IPosable)cmd).pos(): null);
		if (list.isEmpty()) {
			ISort args[] = new ISort[cmd.parameters().size()];
			int i = 0;
			for (IExpr.IDeclaration d: cmd.parameters()) {
				args[i++] = d.sort(); // FIXME - use resolved sort?
				//newp.add(smtConfig.exprFactory.declaration(d.parameter(),d.sort(),d.pos()));
			}
			ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(args,cmd.resultSort());
			SymbolTable.Entry entry = new SymbolTable.Entry(cmd.symbol(),fcnSort,null);
			entry.definition = cmd.expression();
			if (symTable.add(entry,false)) { 
				checkSatStatus = null;
				return smtConfig.responseFactory.success();
			} else {
				return smtConfig.responseFactory.error("Symbol " + encodedName + " is already defined",cmd.symbol().pos());
			}
		} else {
			return list.get(0); // FIXME - return all?
		}
	}
	
	@Override 
	public IResponse declare_sort(Ideclare_sort cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-sort command is issued");
		}
		List<IResponse> list = TypeChecker.checkSortAbbreviation(symTable,cmd.sortSymbol(),null,null);
		boolean b = list.isEmpty();
		if (b) {
			INumeral sortArity = cmd.arity();
			b = symTable.addSortDefinition(cmd.sortSymbol(),sortArity);
			if (!b) return smtConfig.responseFactory.error("The identifier is already declared to be a sort: " + 
					smtConfig.defaultPrinter.toString(cmd.sortSymbol()), cmd.sortSymbol().pos());
			checkSatStatus = null;
			return smtConfig.responseFactory.success();
		} else {
			return list.get(0); // FIXME - return all errors?
		}
	}
	
	@Override
	public IResponse define_sort(Idefine_sort cmd) {
		if (logicSet == null) {
			return smtConfig.responseFactory.error("The logic must be set before a define-sort command is issued");
		}
		List<IResponse> list = TypeChecker.checkSortAbbreviation(symTable,cmd.sortSymbol(),cmd.parameters(),cmd.expression());
		boolean b = list.isEmpty();
		if (b) {
			b = symTable.addSortDefinition(cmd.sortSymbol(),cmd.parameters(),cmd.expression());
			if (!b) return smtConfig.responseFactory.error("The identifier is already declared to be a sort: " + 
				smtConfig.defaultPrinter.toString(cmd.sortSymbol()), cmd.sortSymbol().pos());
			else {
				checkSatStatus = null;
				return smtConfig.responseFactory.success();
			}
		} else {
			return list.get(0); // FIXME - return all errors?
		}
	}
	
}
