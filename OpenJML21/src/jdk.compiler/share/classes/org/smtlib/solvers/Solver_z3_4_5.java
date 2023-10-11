/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

// Items not implemented:
//   attributed expressions
//   get-values get-assignment get-proof get-unsat-core
//   some error detection and handling

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.io.StringWriter;
import java.io.Writer;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.smtlib.*;
import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.ICommand.Ideclare_sort;
import org.smtlib.ICommand.Idefine_fun;
import org.smtlib.ICommand.Idefine_sort;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IParser.ParserException;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.impl.Pos;
import org.smtlib.sexpr.Printer;

/** This class is an adapter that takes the SMT-LIB ASTs and translates them into Z3 commands */
public class Solver_z3_4_5 extends AbstractSolver implements ISolver {
	
	protected String NAME_VALUE = "z3-4.3"; // FIXME - should get rid of this
	

	protected int linesOffset = 0;
	
	/** A reference to the SMT configuration */
	protected SMT.Configuration smtConfig;

	/** A reference to the SMT configuration */
	public SMT.Configuration smt() { return smtConfig; }
	
	/** The command-line arguments for launching the Z3 solver */
	protected String cmds[];
	protected String cmds_win[] = new String[]{ "", "/smt2","/in","SMTLIB2_COMPLIANT=true"}; 
	protected String cmds_mac[] = new String[]{ "", "-smt2","-in","SMTLIB2_COMPLIANT=true"}; 
	protected String cmds_unix[] = new String[]{ "", "-smt2","-in"}; 

	/** The object that interacts with external processes */
	protected SolverProcess solverProcess;
	
	/** The parser that parses responses from the solver */
	protected org.smtlib.sexpr.Parser responseParser;
	
	/** Set to true once a set-logic command has been executed */
	protected boolean logicSet = false;
	
	/** The checkSatStatus returned by check-sat, if sufficiently recent, otherwise null */
	protected /*@Nullable*/ IResponse checkSatStatus = null;
	
	@Override
	public /*@Nullable*/IResponse checkSatStatus() { return checkSatStatus; }

	/** The number of pushes less the number of pops so far */
	protected int pushesDepth = 0;
	
	/** Map that keeps current values of options */
	protected Map<String,IAttributeValue> options = new HashMap<String,IAttributeValue>();
	
	/** Creates an instance of the Z3 solver */
	public Solver_z3_4_5(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
		this.smtConfig = smtConfig;
		if (isWindows) {
			cmds = cmds_win;
		} else if (isMac) {
			cmds = cmds_mac;
		} else {
			cmds = cmds_unix;
		}
		cmds[0] = executable;
		options.putAll(smtConfig.utils.defaults);
		double timeout = smtConfig.timeout;
		if (timeout > 0) {
			List<String> args = new java.util.ArrayList<String>(cmds.length+1);
			args.addAll(Arrays.asList(cmds));
			if (isWindows) args.add("/t:" + Integer.toString((int)timeout));
			else           args.add("-t:" + Integer.toString((int)timeout));
			cmds = args.toArray(new String[args.size()]);
		}
		solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile);
		responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source("",null));
	}

	/** Creates an instance of the Z3 solver */
	public Solver_z3_4_5(SMT.Configuration smtConfig, /*@NonNull*/ String[] command) {
		this.smtConfig = smtConfig;
		cmds = command;
		options.putAll(smtConfig.utils.defaults);
		double timeout = smtConfig.timeout;
		if (timeout > 0) {
			List<String> args = new java.util.ArrayList<String>(cmds.length+1);
			args.addAll(Arrays.asList(cmds));
			if (isWindows) args.add("/t:" + Integer.toString((int)timeout));
			else           args.add("-t:" + Integer.toString((int)timeout));
			cmds = args.toArray(new String[args.size()]);
		}
		solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile);
		responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source("",null));
	}

	public IResponse sendCommand(ICommand cmd) {
		String translatedCmd = null;
		try {
			translatedCmd = translate(cmd);
			return parseResponse(solverProcess.sendAndListen(translatedCmd,"\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + translatedCmd + " " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + translatedCmd + " " + e);
		}
	}
	
	public IResponse sendCommand(String cmd) {
		try {
			return parseResponse(solverProcess.sendAndListen(cmd,"\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + cmd + " " + e);
		}
	}
	

	@Override
	public IResponse start() {
		try {
			solverProcess.start(false);
			// FIXME - enable the following lines when the Z3 solver supports them
//			if (smtConfig.solverVerbosity > 0) solverProcess.sendNoListen("(set-option :verbosity ",Integer.toString(smtConfig.solverVerbosity),")");
//			if (!smtConfig.batch) solverProcess.sendNoListen("(set-option :interactive-mode true)"); // FIXME - not sure we can do this - we'll lose the feedback
			// Can't turn off printing success, or we get no feedback
			solverProcess.sendAndListen("(set-option :print-success true)\n"); // Z3 4.3.0 needs this because it mistakenly has the default for :print-success as false
			linesOffset ++; 
			//if (smtConfig.nosuccess) solverProcess.sendAndListen("(set-option :print-success false)");
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Started "+NAME_VALUE+" ");
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}
	
	@Override
	public IResponse exit() {
		try {
			solverProcess.sendAndListen("(exit)\n");
			solverProcess.exit();
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Ended Z3 ");
			return successOrEmpty(smtConfig);
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}
	
	@Override
	public void forceExit() {
		if (solverProcess != null) solverProcess.exit();
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("Ended Z3 forcibly");
	}



	@Override 
	public void comment(String comment) {
		try {
			solverProcess.sendNoListen(comment);
		} catch (IOException e) {
			// FIXME;
		}
	}

	/** Translates an S-expression into Z3 syntax */
	protected String translate(IAccept sexpr) throws IVisitor.VisitorException {
		// The z3 solver uses the standard S-expression concrete syntax, but not quite
		// so we have to use our own translator
		StringWriter sw = new StringWriter();
		sexpr.accept(new Translator(sw));
		return sw.toString();
	}
	
	/** Translates an S-expression into standard SMT syntax */
	protected String translateSMT(IAccept sexpr) throws IVisitor.VisitorException {
		// The z3 solver uses the standard S-expression concrete syntax, but not quite
		StringWriter sw = new StringWriter();
		org.smtlib.sexpr.Printer.write(sw,sexpr);
		return sw.toString();
	}
	
	protected IResponse parseResponse(String response) {
		try {
			if (response.startsWith("stderr")) response = response.replace("stderr", "\"stderr\"");
			else if (response.startsWith("stdout")) response = response.replace("stdout", "\"stdout\"");
			Pattern oldbv = Pattern.compile("bv([0-9]+)\\[([0-9]+)\\]");
			Matcher mm = oldbv.matcher(response);
			while (mm.find()) {
				long val = Long.parseLong(mm.group(1));
				int base = Integer.parseInt(mm.group(2));
				String bits = "";
				for (int i=0; i<base; i++) { bits = ((val&1)==0 ? "0" : "1") + bits; val = val >>> 1; }
				response = response.substring(0,mm.start()) + "#b" + bits + response.substring(mm.end(),response.length());
				mm = oldbv.matcher(response);
			}
			if (isMac && response.startsWith("success")) return smtConfig.responseFactory.success(); // IFXME - this is just to avoid a problem with the Mac Z3 implementation
			if (response.contains("error")  && !response.contains(":error")) {
				// Z3 returns an s-expr (always?)
				// FIXME - (1) the {Print} also needs {Space}; (2) err_getValueTypes.tst returns a non-error s-expr and then an error s-expr - this fails for that case
				//Pattern p = Pattern.compile("\\p{Space}*\\(\\p{Blank}*error\\p{Blank}+\"(([\\p{Space}\\p{Print}^[\\\"\\\\]]|\\\\\")*)\"\\p{Blank}*\\)\\p{Space}*");
				Pattern p = Pattern.compile("\\p{Space}*\\(\\p{Blank}*error\\p{Blank}+\"(([\\p{Print}\\p{Space}&&[^\"\\\\]]|\\\\\")*)\"\\p{Blank}*\\)");
				Matcher m = p.matcher(response);
				String concat = "";
				while (m.lookingAt()) {
					if (!concat.isEmpty()) concat = concat + "; ";
					String matched = m.group(1);
					String prefix = "line ";
					int offset = prefix.length();
					if (matched.startsWith(prefix)) {
						int k = matched.indexOf(' ',offset);
						String number = matched.substring(offset, k);
						try {
							int n = Integer.parseInt(number);
							matched = prefix + (n-linesOffset) + matched.substring(k);
						} catch (NumberFormatException e) {
							// Just continue
						}
					}
					concat = concat + matched;
					m.region(m.end(0),m.regionEnd());
				}
				if (!concat.isEmpty()) response = concat;
				return smtConfig.responseFactory.error(response);
			}
			responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source(response,null));
			return responseParser.parseResponse(response);
		} catch (ParserException e) {
			return smtConfig.responseFactory.error("ParserException while parsing response: " + response + " " + e);
		}
	}

	@Override
	public IResponse assertExpr(IExpr sexpr) {
		IResponse response;
		if (pushesDepth <= 0) {
			return smtConfig.responseFactory.error("All assertion sets have been popped from the stack");
		}
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before an assert command is issued");
		}
		try {
			String s = solverProcess.sendAndListen("(assert ",translate(sexpr),")\n");
			response = parseResponse(s);
			checkSatStatus = null;
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Failed to assert expression: " + e + " " + sexpr);
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to assert expression: " + e + " " + sexpr);
		}
		return response;
	}
	
	@Override
	public IResponse get_assertions() {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a get-assertions command is issued");
		}
		// FIXME - do we really want to call get-option here? it involves going to the solver?
		if (!smtConfig.relax && !Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_ASSERTIONS)))) {
			return smtConfig.responseFactory.error("The get-assertions command is only valid if :interactive-mode has been enabled");
		}
		try {
			StringBuilder sb = new StringBuilder();
			String s;
			int parens = 0;
			do {
				s = solverProcess.sendAndListen("(get-assertions)\n");
				int p = -1;
				while (( p = s.indexOf('(',p+1)) != -1) parens++;
				p = -1;
				while (( p = s.indexOf(')',p+1)) != -1) parens--;
				sb.append(s.replace('\n',' ').replace("\r",""));
			} while (parens > 0);
			s = sb.toString();
			org.smtlib.sexpr.Parser p = new org.smtlib.sexpr.Parser(smtConfig,new org.smtlib.impl.Pos.Source(s,null));
			List<IExpr> exprs = new LinkedList<IExpr>();
			try {
				if (p.isLP()) {
					p.parseLP();
					while (!p.isRP() && !p.isEOD()) {
						IExpr e = p.parseExpr();
						exprs.add(e);
					}
					if (p.isRP()) {
						p.parseRP();
						if (p.isEOD()) return smtConfig.responseFactory.get_assertions_response(exprs); 
					}
				}
			} catch (Exception e ) {
				// continue - fall through
			}
			return smtConfig.responseFactory.error("Unexpected output from the Z3 solver: " + s);
		} catch (IOException e) {
			return smtConfig.responseFactory.error("IOException while reading Z3 reponse");
		}
	}
	


	@Override
	public IResponse check_sat() {
		IResponse res;
		try {
			if (!logicSet) {
				return smtConfig.responseFactory.error("The logic must be set before a check-sat command is issued");
			}
			String s = solverProcess.sendAndListen("(check-sat)\n");
			//smtConfig.log.logDiag("HEARD: " + s);  // FIXME - detect errors - parseResponse?
			
			if (solverProcess.isRunning(false)) {
				if (s.contains("unsat")) res = smtConfig.responseFactory.unsat();
				else if (s.contains("sat")) res = smtConfig.responseFactory.sat();
				else res = smtConfig.responseFactory.unknown();
			} else {
				res = smtConfig.responseFactory.error("Solver has unexpectedly terminated");
			}

			checkSatStatus = res;
		} catch (IOException e) {
			res = smtConfig.responseFactory.error("Failed to check-sat");
		}
		return res;
	}
	
	@Override
	public IResponse reset() {
		logicSet = false;
	    return sendCommand("(reset)");
	}

	@Override
	public IResponse reset_assertions() {
		return smtConfig.responseFactory.unsupported();
	    //return sendCommand("(reset-assertions)");
	}

	@Override
	public IResponse pop(int number) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a pop command is issued");
		}
//		if (number < 0) throw new SMT.InternalException("Internal bug: A pop command called with a negative argument: " + number);
//		if (number > pushesDepth) return smtConfig.responseFactory.error("The argument to a pop command is too large: " + number + " vs. a maximum of " + (pushesDepth));
//		if (number == 0) return  successOrEmpty(smtConfig);
		try {
			checkSatStatus = null;
			pushesDepth -= number;
			return parseResponse(solverProcess.sendAndListen("(pop ",Integer.toString(number),")\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse push(int number) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a push command is issued");
		}
		if (number < 0) throw new SMT.InternalException("Internal bug: A push command called with a negative argument: " + number);
		checkSatStatus = null;
		if (number == 0) return smtConfig.responseFactory.success();
		try {
			pushesDepth += number;
			IResponse r = parseResponse(solverProcess.sendAndListen("(push ",Integer.toString(number),")\n"));
			// FIXME - actually only see this problem on Linux
			if (r.isError() && !isWindows) return successOrEmpty(smtConfig);
			return r;
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
		// FIXME - discrimninate among logics
		
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#set-logic " + logicName);
		if (logicSet) {
			if (!smtConfig.relax) return smtConfig.responseFactory.error("Logic is already set");
			pop(pushesDepth);
		}
		pushesDepth++;
		logicSet = true;
		// Z3 behaves differently if the ALL logic is actually set, as compared to not setting a logic.
		if (logicName.equals("ALL")) {
			return smtConfig.responseFactory.success();
		} else try {
			return parseResponse(solverProcess.sendAndListen("(set-logic ",logicName,")\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e,pos);
		}
	}

	@Override
	public IResponse set_option(IKeyword key, IAttributeValue value) {
		String option = key.value();
		if (Utils.PRINT_SUCCESS.equals(option)) {
			if (!(Utils.TRUE.equals(value) || Utils.FALSE.equals(value))) {
				return smtConfig.responseFactory.error("The value of the " + option + " option must be 'true' or 'false'");
			}
		}
		if (logicSet && (Utils.INTERACTIVE_MODE.equals(option)||Utils.PRODUCE_ASSERTIONS.equals(option))) {
			return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
		}
		if (Utils.PRODUCE_ASSIGNMENTS.equals(option) || 
				Utils.PRODUCE_PROOFS.equals(option) ||
				Utils.PRODUCE_UNSAT_CORES.equals(option)) {
			if (logicSet) return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
//			return smtConfig.responseFactory.unsupported();
		}
		if (Utils.PRODUCE_MODELS.equals(option)) {
			if (logicSet) return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
		}
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
					FileOutputStream f = new FileOutputStream(name,true); // true -> append
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
		}
		// Save the options on our side as well
		options.put(Utils.INTERACTIVE_MODE.equals(option) && !smtConfig.isVersion(SMTLIB.V20) ? Utils.PRODUCE_ASSERTIONS : option,value);
		IResponse r = checkPrintSuccess(smtConfig,key,value);
		if (r != null) return r;

		try {
			solverProcess.sendAndListen("(set-option ",option," ",value.toString(),")\n");// FIXME - detect errors
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
		
		return successOrEmpty(smtConfig);
	}

	@Override
	public IResponse get_option(IKeyword key) { // FIXME - use the solver?
		String option = key.value();
		IAttributeValue value = options.get(Utils.INTERACTIVE_MODE.equals(option) && !smtConfig.isVersion(SMTLIB.V20)? Utils.PRODUCE_ASSERTIONS : option);
		if (value == null) return smtConfig.responseFactory.unsupported();
		return value;
	}

	@Override
	public IResponse get_info(IKeyword key) {
		return sendCommand("(get-info " + key + ")");
	}
	
	@Override
	public IResponse set_info(IKeyword key, IAttributeValue value) {
		if (Utils.infoKeywords.contains(key)) {
			return smtConfig.responseFactory.error("Setting the value of a pre-defined keyword is not permitted: "+ 
					smtConfig.defaultPrinter.toString(key),key.pos());
		}
		return sendCommand(new org.smtlib.command.C_set_info(key,value));
	}


	@Override
	public IResponse declare_fun(Ideclare_fun cmd) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-fun command is issued");
		}
		try {
			checkSatStatus = null;
			return parseResponse(solverProcess.sendAndListen(translate(cmd),"\n"));
			
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse define_fun(Idefine_fun cmd) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a define-fun command is issued");
		}
		try {
			checkSatStatus = null;
			return parseResponse(solverProcess.sendAndListen(translate(cmd),"\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse declare_sort(Ideclare_sort cmd) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-sort command is issued");
		}
		try {
			checkSatStatus = null;
			return parseResponse(solverProcess.sendAndListen(translate(cmd),"\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse define_sort(Idefine_sort cmd) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a define-sort command is issued");
		}
		try {
			checkSatStatus = null;
			return parseResponse(solverProcess.sendAndListen(translate(cmd),"\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}
	
	@Override 
	public IResponse get_proof() {
//		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_PROOFS)))) {
//			return smtConfig.responseFactory.error("The get-proof command is only valid if :produce-proofs has been enabled");
//		}
//		if (checkSatStatus != smtConfig.responseFactory.unsat()) {
//			return smtConfig.responseFactory.error("The get-proof command is only valid immediately after check-sat returned unsat");
//		}
		try {
			return parseResponse(solverProcess.sendAndListen("(get-proof)\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override 
	public IResponse get_unsat_core() {
//		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_UNSAT_CORES)))) {
//			return smtConfig.responseFactory.error("The get-unsat-core command is only valid if :produce-unsat-cores has been enabled");
//		}
//		if (checkSatStatus != smtConfig.responseFactory.unsat()) {
//			return smtConfig.responseFactory.error("The get-unsat-core command is only valid immediately after check-sat returned unsat");
//		}
		try {
			return parseResponse(solverProcess.sendAndListen("(get-unsat-core)\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override 
	public IResponse get_assignment() {
//		// FIXME - do we really want to call get-option here? it involves going to the solver?
//		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_ASSIGNMENTS)))) {
//			return smtConfig.responseFactory.error("The get-assignment command is only valid if :produce-assignments has been enabled");
//		}
//		if (checkSatStatus != smtConfig.responseFactory.sat() && checkSatStatus != smtConfig.responseFactory.unknown()) {
//			return smtConfig.responseFactory.error("The get-assignment command is only valid immediately after check-sat returned sat or unknown");
//		}
		try {
			return parseResponse(solverProcess.sendAndListen("(get-assignment)\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override 
	public IResponse get_value(IExpr... terms) {
//		// FIXME - do we really want to call get-option here? it involves going to the solver?
//		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_MODELS)))) {
//			return smtConfig.responseFactory.error("The get-value command is only valid if :produce-models has been enabled");
//		}
//		if (!smtConfig.responseFactory.sat().equals(checkSatStatus) && !smtConfig.responseFactory.unknown().equals(checkSatStatus)) {
//			return smtConfig.responseFactory.error("A get-value command is valid only after check-sat has returned sat or unknown");
//		}
		try {
			solverProcess.sendNoListen("(get-value (");
			for (IExpr e: terms) {
				solverProcess.sendNoListen(" ",translate(e));
			}
			String r = solverProcess.sendAndListen("))\n");
			IResponse response = parseResponse(r);
//			if (response instanceof ISeq) {
//				List<ISexpr> valueslist = new LinkedList<ISexpr>();
//				Iterator<ISexpr> iter = ((ISeq)response).sexprs().iterator();
//				for (IExpr e: terms) {
//					if (!iter.hasNext()) break;
//					List<ISexpr> values = new LinkedList<ISexpr>();
//					values.add(new Sexpr.Expr(e));
//					values.add(iter.next());
//					valueslist.add(new Sexpr.Seq(values));
//				}	
//				return new Sexpr.Seq(valueslist);
//			}
			return response;
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	public class Translator extends Printer { //extends IVisitor.NullVisitor<String> {
		
		public Translator(Writer w) { super(w); }

//		@Override
//		public String visit(IDecimal e) throws IVisitor.VisitorException {
//			return translateSMT(e);
//		}
//
//		@Override
//		public String visit(IStringLiteral e) throws IVisitor.VisitorException {
//			throw new VisitorException("The Z3 solver cannot handle string literals",e.pos());
//		}
//
//		@Override
//		public String visit(INumeral e) throws IVisitor.VisitorException {
//			return e.value().toString();
//		}
//
//		@Override
//		public String visit(IBinaryLiteral e) throws IVisitor.VisitorException {
//			return "#b" + e.value();
//		}
//
//		@Override
//		public String visit(IHexLiteral e) throws IVisitor.VisitorException {
//			return "#x" + e.value();
//		}

		@Override
		public Void visit(IFcnExpr e) throws IVisitor.VisitorException {
			// Only - for >=2 args is not correctly done, but we can't delegate to translateSMT because it might be a sub-expression.
			Iterator<IExpr> iter = e.args().iterator();
			if (!iter.hasNext()) throw new VisitorException("Did not expect an empty argument list",e.pos());
			IQualifiedIdentifier fcn = e.head();
			int length = e.args().size();
			if (length > 2 && (fcn instanceof IIdentifier) && fcn.toString().equals("-")) {
				leftassoc(fcn.toString(),length,iter);
			} else {
				super.visit(e);
			}
			return null;
//			String fcnname = fcn.accept(this);
//			StringBuilder sb = new StringBuilder();
//			int length = e.args().size();
//			if (length > 2 && (fcnname.equals("=") || fcnname.equals("<") || fcnname.equals(">") || fcnname.equals("<=") || fcnname.equals(">="))) {
//				// chainable
//				return chainable(fcnname,iter);
//			} else if (fcnname.equals("xor")) {
//				// left-associative operators that need grouping
//				return leftassoc(fcnname,length,iter);
//			} else if (length > 1 && fcnname.equals("-")) {
//				// left-associative operators that need grouping
//				return leftassoc(fcnname,length,iter);
//			} else if (fcnname.equals("=>")) {
//				// right-associative operators that need grouping
//				if (!iter.hasNext()) {
//					throw new VisitorException("=> operation without arguments",e.pos());
//				}
//				return rightassoc(fcnname,iter);
//			} else {
//				// no associativity 
//				sb.append("(");
//				sb.append(fcnname);
//				while (iter.hasNext()) {
//					sb.append(" ");
//					sb.append(iter.next().accept(this));
//				}
//				sb.append(")");
//				return sb.toString();
//			}
		}

		//@ requires iter.hasNext();
		//@ requires length > 0;
		protected <T extends IExpr> void leftassoc(String fcnname, int length, Iterator<T> iter ) throws IVisitor.VisitorException {
			if (length == 1) {
				iter.next().accept(this);
			} else {
				try {
					w.append("(");
					w.append(fcnname);
					w.append(" ");
					leftassoc(fcnname,length-1,iter);
					w.append(" ");
					iter.next().accept(this);
					w.append(")");
				} catch (IOException ex) {
					throw new IVisitor.VisitorException(ex,null); // FIXME - null ?
				}
			}
		}

		//@ requires iter.hasNext();
		protected <T extends IExpr> void rightassoc(String fcnname, Iterator<T> iter ) throws IVisitor.VisitorException {
			T n = iter.next();
			if (!iter.hasNext()) {
				n.accept(this);
			} else {
				try {
					w.append("(");
					w.append(fcnname);
					w.append(" ");
					n.accept(this);
					w.append(" ");
					rightassoc(fcnname,iter);
					w.append(")");
				} catch (IOException ex) {
					throw new IVisitor.VisitorException(ex,null); // FIXME - null ?
				}
			}
		}

		
		//@ requires iter.hasNext();
		//@ requires length > 0;
		protected <T extends IAccept> void chainable(String fcnname, Iterator<T> iter ) throws IVisitor.VisitorException {
			try {
				w.append("(and ");
				T left = iter.next();
				while (iter.hasNext()) {
					w.append("(");
					w.append(fcnname);
					w.append(" ");
					left.accept(this);
					w.append(" ");
					(left=iter.next()).accept(this);
					w.append(")");
				}
				w.append(")");
			} catch (IOException ex) {
				throw new IVisitor.VisitorException(ex,null); // FIXME - null ?
			}
		}


//		@Override
//		public String visit(ISymbol e) throws IVisitor.VisitorException {
//			return translateSMT(e);
//		}
//
//		@Override
//		public String visit(IKeyword e) throws IVisitor.VisitorException {
//			throw new VisitorException("Did not expect a Keyword in an expression to be translated",e.pos());
//		}
//
//		@Override
//		public String visit(IError e) throws IVisitor.VisitorException {
//			throw new VisitorException("Did not expect a Error token in an expression to be translated", e.pos());
//		}
//
//		private final String zeros = "00000000000000000000000000000000000000000000000000";
//		@Override
//		public String visit(IParameterizedIdentifier e) throws IVisitor.VisitorException {
//			return translateSMT(e);
//		}
//
//		@Override
//		public String visit(IAsIdentifier e) throws IVisitor.VisitorException {
//			return translateSMT(e);
//		}
//
//		@Override
//		public String visit(IForall e) throws IVisitor.VisitorException {
//			return translateSMT(e);
//		}
//
//		@Override
//		public String visit(IExists e) throws IVisitor.VisitorException {
//			return translateSMT(e);
//		}
//
//		@Override
//		public String visit(ILet e) throws IVisitor.VisitorException {
//			return translateSMT(e);
//		}
//
//		@Override
//		public String visit(IAttribute<?> e) throws IVisitor.VisitorException {
//			throw new UnsupportedOperationException("visit-IAttribute");
//		}
//
//		@Override
//		public String visit(IAttributedExpr e) throws IVisitor.VisitorException {
//			return translateSMT(e);
//		}
//
//		@Override
//		public String visit(IDeclaration e) throws IVisitor.VisitorException {
//			throw new UnsupportedOperationException("visit-IDeclaration");
//		}
//
//		@Override
//		public String visit(ISort.IFamily s) throws IVisitor.VisitorException {
//			return s.identifier().accept(this);
//		}
//		
//		@Override
//		public String visit(ISort.IAbbreviation s) throws IVisitor.VisitorException {
//			throw new UnsupportedOperationException("visit-ISort.IAbbreviation");
//		}
//		
//		@Override
//		public String visit(ISort.IApplication s) throws IVisitor.VisitorException {
//			return translateSMT(s);
//		}
//		
//		@Override
//		public String visit(ISort.IFcnSort s) throws IVisitor.VisitorException {
//			throw new UnsupportedOperationException("visit-ISort.IFcnSort");
//		}
//		
//		@Override
//		public String visit(ISort.IParameter s) throws IVisitor.VisitorException {
//			throw new UnsupportedOperationException("visit-ISort.IParameter");
//		}
//		
//		@Override
//		public String visit(ICommand command) throws IVisitor.VisitorException {
//			if (command instanceof ICommand.Iassert) {
//				return "(assert " + ((ICommand.Iassert)command).expr().accept(this) + ")";
//			} else {
//				return translateSMT(command);
//			}
//		}
	}
}
