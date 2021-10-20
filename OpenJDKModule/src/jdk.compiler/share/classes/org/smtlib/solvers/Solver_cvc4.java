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
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.smtlib.*;
import org.smtlib.ICommand.Ideclare_const;
import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.ICommand.Ideclare_sort;
import org.smtlib.ICommand.Idefine_fun;
import org.smtlib.ICommand.Idefine_sort;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IParser.ParserException;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.impl.Pos;
import org.smtlib.impl.Response;
import org.smtlib.sexpr.Utils;

/** This class is an adapter that takes the SMT-LIB ASTs and translates them into SMT commands */
public class Solver_cvc4 extends AbstractSolver implements ISolver {
		
	/** A reference to the SMT configuration */
	protected SMT.Configuration smtConfig;

	/** A reference to the SMT configuration */
	@Override
	public SMT.Configuration smt() { return smtConfig; }
	
	/** The command-line arguments for launching the solver */
	protected String cmds[];
	protected String cmds_win[] = new String[]{ "", "--lang","smt","--interactive","--incremental","--quiet", "--produce-models","--no-full-saturate-quant"}; 
	protected String cmds_mac[] = new String[]{ "", "--lang","smt","--interactive","--incremental","--quiet", "--produce-models"}; 
	protected String cmds_unix[] = new String[]{ "", "--lang","smt","--interactive","--incremental","--quiet", "--produce-models" };

	/** The parser that parses responses from the solver */
	protected org.smtlib.sexpr.Parser responseParser;
	
	/** The checkSatStatus returned by check-sat, if sufficiently recent, otherwise null */
	private /*@Nullable*/ IResponse checkSatStatus = null;
	
	@Override
	public /*@Nullable*/IResponse checkSatStatus() { return checkSatStatus; }

	// FIXME - get rid of this?
	/** Map that keeps current values of options */
	protected Map<String,IAttributeValue> options = new HashMap<String,IAttributeValue>();
	
	/** Creates an instance of the solver */
    public Solver_cvc4(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
        this(smtConfig, executable, "CVC4> ");
    }
    
    public Solver_cvc4(SMT.Configuration smtConfig, /*@NonNull*/ String executable, String prompt) {
		this.smtConfig = smtConfig;
		if (isWindows) {
			cmds = cmds_win;
		} else if (isMac) {
			cmds = cmds_mac;
            if (smtConfig.seed != 0) {
                cmds = new String[cmds.length+1];
                cmds = Utils.cat(cmds,"--seed",""+smtConfig.seed);
            }
		} else {
			cmds = cmds_unix;
            if (smtConfig.seed != 0) {
                cmds = new String[cmds.length+1];
                cmds = Utils.cat(cmds,"--seed",""+smtConfig.seed);
            }
		}
		cmds[0] = executable;
		options.putAll(smtConfig.utils.defaults);
		double timeout = smtConfig.timeout;
		if (timeout > 0) {
			List<String> args = new java.util.ArrayList<String>(cmds.length+1);
			args.addAll(Arrays.asList(cmds));
			args.add("--tlimit-per=" + Long.toString(Math.round(1000*timeout+0.5)));
			cmds = args.toArray(new String[args.size()]);
		}
		solverProcess = new SolverProcess(cmds,prompt,smtConfig.logfile);
//		{
//			
//			@Override
//			public String listen() throws IOException {
//				// FIXME - need to put the two reads in parallel, otherwise one might block on a full buffer, preventing the other from completing
//				String err = listenThru(errors,null);
//				String out = listenThru(fromProcess,endMarker);
//				err = err + listenThru(errors,null);
//				if (out.endsWith(endMarker)) out = out.substring(0,out.length()-endMarker.length());
//				if (log != null) {
//					if (!out.isEmpty()) { log.write(";OUT: "); log.write(out); log.write(eol); log.flush(); } // input usually ends with a prompt and no line terminator
//					if (!err.isEmpty()) { log.write(";ERR: "); log.write(err); log.flush(); } // input usually ends with a line terminator, we think
//				}
//				return err.isEmpty() ? out : err;
//			}};

		responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source("",null));
	}
	
//	public Solver_cvc4(SMT.Configuration smtConfig, /*@NonNull*/ String[] executable) {
//		this.smtConfig = smtConfig;
//		cmds = executable;
//		solverProcess = new SolverProcess(cmds,"\n","solver.out.cvc4"); // FIXME - what prompt?
//		responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source("",null));
//	}
	
	@Override
	public IResponse start() {
		try {
			solverProcess.start(false);
//			if (smtConfig.solverVerbosity > 0) solverProcess.sendNoListen("(set-option :verbosity ",Integer.toString(smtConfig.solverVerbosity),")");
			//if (!smtConfig.batch) solverProcess.sendNoListen("(set-option :interactive-mode true)"); // FIXME - not sure we can do this - we'll lose the feedback
			// Can't turn off printing success, or we get no feedback
			solverProcess.sendAndListen("(set-option :print-success true)");
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Started CVC4 ");
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}
	
	/** Translates an S-expression into SMT syntax */
	protected String translate(IAccept sexpr) throws IVisitor.VisitorException {
		return translateSMT(sexpr);
	}
	
	/** Translates an S-expression into standard SMT syntax */
	protected String translateSMT(IAccept sexpr) throws IVisitor.VisitorException {
		StringWriter sw = new StringWriter();
		org.smtlib.solvers.Printer.write(sw,sexpr);
		return sw.toString();
	}
	
	public IResponse sendCommand(ICommand cmd) {
		String translatedCmd = null;
		try {
			translatedCmd = translate(cmd);
			if (cmd instanceof Ideclare_const) translatedCmd = "(declare-fun " + ((Ideclare_const)cmd).symbol() + " () " + ((Ideclare_const)cmd).resultSort() + ")";
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
	
	protected IResponse parseResponse(String response) {
		try {
		    int k = response.indexOf('\n');
		    if (isMac && k >= 0 && k < response.length()-1) response = response.substring(k+1);
			if (response.contains("Error") && response.charAt(0) != '(') {
				return smtConfig.responseFactory.error(response);
			}
			if (response.contains("SmtEngine") && response.charAt(0) != '(') {
				// The one instance I know of this is when the prover states that
				// it is turning off produce-models mode because of non-linear
				// arithmetic. We will not pass this along.
				return smtConfig.responseFactory.success();
			}
			responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source(response,null));
			return responseParser.parseResponse(response);
		} catch (ParserException e) {
			return smtConfig.responseFactory.error("ParserException while parsing response: " + response + " " + e);
		}
	}

	@Override
	public IResponse exit() {
			IResponse response = sendCommand("(exit)");
			solverProcess.exit();
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Ended SMT ");
			solverProcess = null;
			return response;
	}

	@Override
	public IResponse assertExpr(IExpr sexpr) {
		try {
			return sendCommand("(assert " + translate(sexpr) + ")");
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Failed to assert expression: " + e + " " + sexpr);
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to assert expression: " + e + " " + sexpr);
		}
	}
	
	@Override
	public IResponse get_assertions() {
		// FIXME - do we really want to call get-option here? it involves going to the solver?
		
		// FIXME - try sendCOmmand
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
			return smtConfig.responseFactory.error("Unexpected output from the solver: " + s);
		} catch (IOException e) {
			return smtConfig.responseFactory.error("IOException while reading solver's reponse");
		}
	}
	


	@Override
	public IResponse check_sat() {
		IResponse res;
		try {
			// Try sendCommand
			String s = solverProcess.sendAndListen("(check-sat)\n");
			//smtConfig.log.logDiag("HEARD: " + s);  // FIXME - detect errors - parseResponse?
			
//			if (s.contains("unsat")) res = smtConfig.responseFactory.unsat();
//			else if (s.contains("sat")) res = smtConfig.responseFactory.sat();
//			else if (s.contains("unknown")) res = smtConfig.responseFactory.unknown();
//			else 
			if (solverProcess.isRunning(false)) res = parseResponse(s);
			else res = smtConfig.responseFactory.error("Solver has unexpectedly terminated");
			checkSatStatus = res;
		} catch (Exception e) {
			res = smtConfig.responseFactory.error("Failed to check-sat");
		}
		return res;
	}

	@Override
	public IResponse reset() {
	    return sendCommand("(reset)");
	}

	@Override
	public IResponse reset_assertions() {
	    return sendCommand("(reset-assertions)");
	}

	@Override
	public IResponse pop(int number) {
	    return sendCommand("(pop " + number + ")");
	}

	@Override
	public IResponse push(int number) {
		return sendCommand("(push " + number + ")");
	}

	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
		// FIXME - discrimninate among logics
		
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#set-logic " + logicName);
		if (logicName.equals("ALL")) logicName = "ALL_SUPPORTED";
		return sendCommand("(set-logic " + logicName + ")");
	}

	@Override
	public IResponse set_option(IKeyword key, IAttributeValue value) {
		
		// FIXME - clarify all this - perhaps leave it to cvc4
		String option = key.value();
//		if (Utils.PRINT_SUCCESS.equals(option)) {
//			if (!(Utils.TRUE.equals(value) || Utils.FALSE.equals(value))) {
//				return smtConfig.responseFactory.error("The value of the " + option + " option must be 'true' or 'false'");
//			}
//		}
		if (Utils.VERBOSITY.equals(option)) {
			IAttributeValue v = options.get(option);
			smtConfig.verbose = (v instanceof INumeral) ? ((INumeral)v).intValue() : 0;
		} else 
			if (Utils.DIAGNOSTIC_OUTPUT_CHANNEL.equals(option)) {
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

		options.put(option,value);

		IResponse r = checkPrintSuccess(smtConfig,key,value);
		if (r != null) return r;
		return sendCommand(new org.smtlib.command.C_set_option(key,value));

//		if (!Utils.PRINT_SUCCESS.equals(option)) {
//			return sendCommand(new org.smtlib.command.C_set_option(key,value));
//		} else {
//			return smtConfig.responseFactory.success();
//		}
	}

	@Override
	public IResponse get_option(IKeyword key) {
		if (printSuccess.equals(key)) return smtConfig.nosuccess ? Utils.FALSE : Utils.TRUE;
		IResponse resp = sendCommand(new org.smtlib.command.C_get_option(key));
		if (resp instanceof Response.Seq) {
			// FIXME - this is an adjustment for CVC4's non-standard behavior
			IAttributeValue v = ((Response.Seq)resp).attributes().get(0).attrValue();
//			responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source("true",null));
			try {
			if (v instanceof IStringLiteral) {
				String s = ((IStringLiteral)v).value();
				if (key.toString().equals(":random-seed")) {
					try {
						resp = smtConfig.exprFactory.numeral(s);
					} catch (Exception e) {
						resp = smtConfig.exprFactory.numeral("0");
					}
					return resp;
				}
				if (key.toString().equals(":verbosity")) {
					resp = smtConfig.exprFactory.numeral(s);
					return resp;
				}
				if (s.equals("1")) {
					resp = responseParser.parseResponse("true");
					return resp;
				}
				if (s.equals("0")) {
					resp = responseParser.parseResponse("false");
					return resp;
				}
				
			}
			} catch (ParserException e) {}
			return v;
		}
		return resp;
	}

	@Override
	public IResponse get_info(IKeyword key) {
		return sendCommand(new org.smtlib.command.C_get_info(key));
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
		return sendCommand(cmd);
	}

	@Override
	public IResponse define_fun(Idefine_fun cmd) {
		return sendCommand(cmd);
	}

	@Override
	public IResponse declare_sort(Ideclare_sort cmd) {
		return sendCommand(cmd);
	}

	@Override
	public IResponse define_sort(Idefine_sort cmd) {
		return sendCommand(cmd);
	}
	
	@Override 
	public IResponse get_proof() {
		return sendCommand("(get-proof)");
	}

	@Override 
	public IResponse get_unsat_core() {
		return sendCommand("(get-unsat-core)");
	}

	@Override 
	public IResponse get_assignment() {
		return sendCommand("(get-assignment)");
	}

	@Override 
	public IResponse get_value(IExpr... terms) {
		// Try passing in command FIXME
		//return sendCommand(new org.smtlib.command.C_get_value(terms));
		try {
			solverProcess.sendNoListen("(get-value (");
			for (IExpr e: terms) {
				solverProcess.sendNoListen(" ",translate(e));
			}
			String r = solverProcess.sendAndListen("))\n");
			IResponse response = parseResponse(r);
			return response;
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + e);
		}
	}


}
