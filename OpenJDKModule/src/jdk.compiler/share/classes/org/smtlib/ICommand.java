/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.util.List;

import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.ISort.IParameter;


/** This interface is the generic interface to command classes, providing functionality
 * to type-check the command and to execute it.
 * @author David R. Cok
 */
public interface ICommand extends IAccept {
	
	/** This interface defines classes that implement techniques for mapping a command name to a class
	 * that implements that command.
	 */
	public static interface IFinder {
		/** This method finds a class that implements the ICommand interface for the given class name */
		Class<? extends ICommand> findCommand(String name);
	}
	
	/** Executes the command on the given solver; presumes that the command type-checked
	 * successfully.
	 * @param solver the instance of the solver to use (note that solvers have state)
	 * @return the result of the command
	 */
	IResponse execute(ISolver solver);
	
	/** This is the interface to be used by a concrete ICommand factory. */
	static public interface IFactory {
		/** Creates a script object containing the given filename or the given set of commands */
		IScript script(/*@Nullable*/IStringLiteral filename, /*@Nullable*/List<ICommand> commands);
		
		/** Creates an assert command object, asserting the given expression */
		Iassert assertCommand(IExpr expr);
		
		/** Creates a check-sat command object */
		Icheck_sat check_sat();
		
		/** Creates a declare-fun command object */
		Ideclare_fun declare_fun(IIdentifier id, List<ISort> argSorts, ISort resultSort);
		
		/** Creates a declare-sort command object. */
		Ideclare_sort declare_sort(ISymbol sym, INumeral arity);
		
		/** Creates a define-fun command object */
		Idefine_fun define_fun(IIdentifier id, List<IDeclaration> declarations, ISort resultSort, IExpr expression);
		
		/** Creates a define-sort command object. */
		Idefine_sort define_sort(IIdentifier id, List<IParameter> parameters, ISort.IApplication expression);
		
		/** Creates an exit command object. */
		Iexit exit();
		
		/** Creates a get-assertions command object. */
		Iget_assertions get_assertions();
		
		/** Creates a get-assignment command object. */
		Iget_assignment get_assignment();
		
		/** Creates a get-info command object. */
		Iget_info get_info(IKeyword infoflag);
		
		/** Creates a get-option command object */
		Iget_option get_option(IKeyword option);
		
		/** Creates a get-proof command object. */
		Iget_proof get_proof();
		
		/** Creates a get-unsat-core command object. */
		Iget_unsat_core get_unsat_core();
		
		/** Creates a get-value command object. */
		Iget_value get_value(List<IExpr> exprs);
		
		/** Creates a push command object. */
		Ipush push(INumeral number);
		
		/** Creates a pop command object. */
		Ipop pop(INumeral number);
		
		/** Creates a set-logic command object */
		Iset_logic set_logic(ISymbol logic);
		
		/** Creates a set-info command object. */
		Iset_info set_info(IKeyword infoflag, IAttributeValue value);
		
		/** Creates a set-option command object. */
		Iset_option set_option(IKeyword option, IAttributeValue value);
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB scripts. A script may consist of a file or an explicit list of commands. */
	
	static public interface IScript extends IAccept {
		/*@Nullable*/ IStringLiteral filename();
		/*@Nullable*/ List<ICommand> commands();
		IResponse execute(ISolver solver);
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB assert commands. */
	static public interface Iassert extends ICommand {
		IExpr expr();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB check-sat commands. */
	static public interface Icheck_sat extends ICommand {
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB check-sat-assuming commands. */
	static public interface Icheck_sat_assuming extends ICommand {
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB declare-const commands. */
	static public interface Ideclare_const extends ICommand {
		ISymbol symbol();
		ISort resultSort();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB declare-fun commands. */
	static public interface Ideclare_fun extends ICommand {
		ISymbol symbol();
		List<ISort> argSorts();
		ISort resultSort();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB declare-sort commands. */
	static public interface Ideclare_sort extends ICommand {
		ISymbol sortSymbol();
		INumeral arity();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB define-fun commands. */
	static public interface Idefine_fun extends ICommand {
		ISymbol symbol();
		List<IDeclaration> parameters();
		ISort resultSort();
		IExpr expression();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB define-sort commands. */
	static public interface Idefine_sort extends ICommand {
		ISymbol sortSymbol();
		List<IParameter> parameters();
		ISort expression();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB exit commands. */
	static public interface Iexit extends ICommand {
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB get-assertions commands. */
	static public interface Iget_assertions extends ICommand {
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB get-assignment commands. */
	static public interface Iget_assignment extends ICommand {
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB get-info commands. */
	static public interface Iget_info extends ICommand {
		IKeyword infoflag();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB get-option commands. */
	static public interface Iget_option extends ICommand {
		IKeyword option();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB get-proof commands. */
	static public interface Iget_proof extends ICommand {
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB get-unsat-assumptions commands. */
	static public interface Iget_unsat_assumptions extends ICommand {
	}

	/** Interface to be implemented by all objects representing SMT-LIB get-unsat-core commands. */
	static public interface Iget_unsat_core extends ICommand {
	}

	/** Interface to be implemented by all objects representing SMT-LIB get-value commands. */
	static public interface Iget_value extends ICommand {
		//@ ensures exprs().size > 0;
		List<IExpr> exprs();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB pop commands. */
	static public interface Ipop extends ICommand {
		//@ ensures \result.intValue() >= 0;
		INumeral number();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB push commands. */
	static public interface Ipush extends ICommand {
		//@ ensures \result.intValue() >= 0;
		INumeral number();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB reset commands. */
	static public interface Ireset extends ICommand {
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB reset-assertions commands. */
	static public interface Ireset_assertions extends ICommand {
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB set-logic commands. */
	static public interface Iset_logic extends ICommand {
		ISymbol logic();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB set-info commands. */
	static public interface Iset_info extends ICommand {
		IKeyword infoflag();
		IAttributeValue value();
	}
	
	/** Interface to be implemented by all objects representing SMT-LIB set-option commands. */
	static public interface Iset_option extends ICommand {
		IKeyword option();
		/*@Nullable*/IAttributeValue value();
	}
}
