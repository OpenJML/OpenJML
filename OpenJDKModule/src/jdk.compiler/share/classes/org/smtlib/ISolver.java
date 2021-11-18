/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import org.smtlib.ICommand.Ideclare_const;
import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.ICommand.Ideclare_sort;
import org.smtlib.ICommand.Idefine_fun;
import org.smtlib.ICommand.Idefine_sort;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.IStringLiteral;


/** This is the interface to be implemented by any solver adapter;
 * there is an abstract method for each SMT-LIB command */
public interface ISolver {

	/** Returns the configuration object with which the solver is initialized */
	SMT.Configuration smt();
	
	/** Current check-sat status; returns sat, unsat, unknown, error, or null */ // TODO - be more specific
	/*@Nullable*/ IResponse checkSatStatus();
	
	/** Starts the solver; this is not an SMT-LIB command, but it is convenient in some implementations
	 * to separate the starting and initialization from the construction of the solver instance.
	 * @return success or error
	 */
	IResponse start();
	
	/** Reset the solver to the start state.
	 * @return success or error
	 */
	IResponse reset();
	
	/** Remove asserted assertions, depending on the value of :global-declarations.
	 * @return success or error
	 */
	IResponse reset_assertions();
	
	/** Terminate the solver; no further commands are permitted.
	 * @return success or error
	 */
	IResponse exit();
	
	/** Terminate the solver forcibly, without using commands
	 */
	void forceExit();
	
	/** Echo the argument */
	IResponse echo(IStringLiteral arg);
	
	/** Send comment text - the argument must be white-space + legitimate comment text */
	void comment(String comment);
	
	/** Sets the logic the solver should use; the position argument is
	 * just used for position information in error messages.
	 * @return success or error
	 */
	IResponse set_logic(String logicName, /*@Nullable*/ IPos pos);
	
	/** Adds the given number of empty stack frames to the solver state.
	 * @param number non-negative number of stack frames to push
	 * @return success or error
	 */
	//@ requires number >= 0;
	IResponse push(int number);
	
	/** Pops the given number of stack frames from the solver state.
	 * @param number non-negative number of stack frames to pop
	 * @return success or error
	 */
	//@ requires number >= 0;
	IResponse pop(int number);
	
	/** Asserts the given expression into the solver state (in the top stack frame);
	 * the expression is expected to be already checked that it is a valid, well-formed and well-sorted
	 * expression in the current logic; returns success or error */
	IResponse assertExpr(IExpr expr); // Not named assert because that is a Java reserved word, though
										// the SMT-LIB command is 'assert'
	
	/** Checks whether the current state is satisfiable in the current logic.
	 * @return sat, unsat, unknown or error
	 */
	IResponse check_sat();
	
	/** Checks whether the current state is satisfiable in the current logic, under specified assumptions.
	 * @return sat, unsat, unknown or error
	 */
	IResponse check_sat_assuming(IExpr...  exprs);
	
	/** Defines a new uninterpreted constant; returns success or error*/
	IResponse declare_const(Ideclare_const cmd); // FIXME - use ISymbol, ISort as arguments?
	
	/** Defines a new uninterpreted constant or function; returns success or error*/
	IResponse declare_fun(Ideclare_fun cmd);
	
	/** Declares a new basic sort; returns success or error */
	IResponse declare_sort(Ideclare_sort cmd);

	/** Defines a new constant or function; returns success or error */
	IResponse define_fun(Idefine_fun cmd);
	
	/** Defines a new sort abbreviation; returns success or error */
	IResponse define_sort(Idefine_sort cmd);
	
	/** Sets an SMT-LIB option
	 * @param option the option whose value is to be set
	 * @param value the value to which to set it
	 * @return SUCCESS or an error or unsupported
	 */
	IResponse set_option(IKeyword option, IAttributeValue value);

	/** Sets an SMT-LIB info value
	 * @param key the info item whose value is to be set
	 * @param value the value to which to set it
	 * @return SUCCESS or an error or unsupported
	 */
	IResponse set_info(IKeyword key, IAttributeValue value);
	
	/** Returns a list of all the formulae that have been asserted in the current state.
	 * If the solver prints the list of assertions itself, then this method simply returns success.
	 * May only be used in interactive mode.  If interactive mode is not implemented,
	 * this command may return unsupported.
	 * @return success or a list of formulae (as Strings or terms?) // TODO is this what we want?
	 */
	IResponse get_assertions();
	
	/** Returns a proof that the current state is unsatisfiable. If the solver prints the proof itself,
	 * then it returns simply success. // TODO check is this what we want
	 * May only be issued if the :produce-proofs option is enabled.
	 * Supporting proof production is optional.
	 * @return error or success or unsupported (if proof production is not supported) or a proof
	 */
	IResponse get_proof();
	
	/** Returns a model of current satisfiable state */
	IResponse get_model();
	
	/** Returns a list of the names of formulae in the unsat core of the current (unsatisfiable) state.
	 * May only be issued if :produce-unsat-core is enabled.
	 * @return unsupported or error or a list of names (as ids)
	 */
	IResponse get_unsat_core();
	
	/** Returns a list of values for the given expressions.
	 * May only be used if :produce-models is enabled.
	 * @param terms expressions whose value in the current (Satisfiable) state is to be determined
	 * @return error or list of values (which may include IError instances)
	 */
	IResponse get_value(IExpr... terms);

	/** Retrieves values for all named formulae in the current (satisfiable) state.
	 * May only be used if :produce-assignments is enabled.
	 * @return error or a list of name-value pairs
	 */
	IResponse get_assignment();

	/** Gets the value of an SMT-LIB option
	 * 
	 * @param option the option whose value is desired
	 * @return TODO
	 */
	IResponse get_option(IKeyword option);

	/** Gets the value of an SMT-LIB information topic
	 * 
	 * @param option the info option whose value is desired
	 * @return TODO
	 */
	IResponse get_info(IKeyword option);
	
}
