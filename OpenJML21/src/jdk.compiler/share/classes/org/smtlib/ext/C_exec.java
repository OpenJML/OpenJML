/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.ext;

import java.io.IOException;

import org.smtlib.IParser.ParserException;
import org.smtlib.*;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the non-standard exec command */
public class C_exec extends Command implements Iexec {
	/** The command name */
	public static final String commandName = "exec";
	
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	/** The command script to be run */
	protected IScript script;
	
	/** Returns a reference to the command script to be run */
	@Override
	public IScript script() { return script; }

	/** Constructs a command object for the given script */
	public C_exec(IScript script) {
		this.script = script;
	}
	
	/** Parses the arguments of the command, producing a new command instance */
	static public /*@Nullable*/ C_exec parse(Parser p) throws ParserException {
		if (!p.smt().relax) {
			error(p.smt(),"Invalid SMT-LIB command: " + commandName,p.commandName.pos());
			return null;
		} 
		IScript script = p.parseScript();
		if (script == null) return null;
		return new C_exec(script);
	}

	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException {
		try {
			p.writer().append("(" + commandName + " ");
			script.accept(p);
			p.writer().append(")");
		} catch (IVisitor.VisitorException e) {
			p.error(e.getMessage());
		}
	}
	
	/** Executes the command, which executes the script */
	@Override
	public IResponse execute(ISolver solver) {
		return script().execute(solver);
	}

	@Override
	public </*@Nullable*/T> /*@Nullable*/T accept(IVisitor</*@Nullable*/T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
