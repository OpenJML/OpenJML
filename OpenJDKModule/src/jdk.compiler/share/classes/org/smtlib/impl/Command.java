/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.impl;


import org.smtlib.*;
import org.smtlib.IPos.IPosable;

/** This abstract class is the base class for all commands within this implementation. */
public abstract class Command implements ICommand, IPosable {
	/** Default constructor - the base class Command's state just has the IPos value */
	public Command() {
		super();
		pos = null;
	}
	
	public /*@Nullable*//*@ReadOnly*/ String prefixText; 
	
	/** The textual position of the command, if any */
	protected /*@Nullable*//*@ReadOnly*/IPos pos;
	
	/** The textual position of the command, if any */
	@Override
	public /*@Nullable*//*@ReadOnly*/IPos pos() { return pos; }
	
	/** Setting the textual position of the command, if any */
	@Override
	public void setPos(/*@Nullable*//*@ReadOnly*/ IPos p) { pos = p; }
	
	/** The command name */
	abstract public String commandName();
	
	/** Utility method for logging errors */
	static public void error(SMT.Configuration smt, String msg, IPos pos) {
		smt.log.logError(smt.responseFactory.error(msg,pos));
	}

	/** For debugging only - use a Printer for real printing */
	@Override
	public String toString() {
		// FIXME - change to print from the parser source
		return (new org.smtlib.sexpr.Printer(null)).toString(this);
	}
	
}