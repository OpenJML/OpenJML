package org.smtlib.impl;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.smtlib.*;
import org.smtlib.ICommand.IScript;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IParser.ParserException;

/** This class implements the IScript interface, representing SMT-LIB command scripts */
public class Script implements IScript {
	// This class can hold either a filename from which to read commands
	// or a sequence of commands held directly; it should not have both
	
	//@ invariant (filename() == null) != (commands() != null);
	
	/** The filename of the script file */
	//@ spec_public
	protected /*@Nullable*/ IStringLiteral filename;
	
	/** The filename of the script file */
	//@ ensures \result == filename;
	@Override
	public /*@Nullable*/IStringLiteral filename() {
		return filename;
	}
	
	/** The list of commands */
	//@ spec_public
	protected /*@Nullable*/List<ICommand> commands;
	
	/** Returns a reference to the internal list */
	//@ ensures \result == commands;
	@Override
	public /*@Nullable*/List<ICommand> commands() {
		return commands;
	}

	/** Constructs a script with no commands */
	public Script() {
		filename = null;
		commands = new LinkedList<ICommand>();
	}
	
	/** Constructs the script with the given list of commands, hijacking the list itself */
	//@ requires (filename != null) != (list != null);
	public Script(/*@Nullable*/IStringLiteral filename, /*@Nullable*/List<ICommand> list) {
		this.filename = filename;
		this.commands = list;
	}
	
	/** Adds a command to the end of the script */
	//@ requires commands() != null;
	public void add(ICommand command) {
		if (commands == null) commands = new LinkedList<ICommand>();  // FIXME - test without this line
		commands.add(command);
	}
	
	public String kind() { return "script"; }  // FIXME - should override?

	/** Executes the current list */
	// FIXME _ should we have an incremental read and execute option?
	@Override
	public IResponse execute(ISolver solver) {
		SMT.Configuration smtConfig = solver.smt();
		/*@Mutable*/FileReader fileReader = null;
		List<ICommand> commands = this.commands;
		if (filename != null) {
			String filename = this.filename.value();
			try {
				fileReader = new FileReader(new File(filename));
				ISource source = smtConfig.smtFactory.createSource(new CharSequenceReader(fileReader),filename);
				IParser p = smtConfig.smtFactory.createParser(smtConfig,source);
				IScript script = p.parseScript();
				if (script == null) return smtConfig.responseFactory.error("Failed to parse the command script: " + filename,this.filename.pos());
				commands = script.commands();
			} catch (FileNotFoundException e) {
				return smtConfig.responseFactory.error(e.toString(),this.filename.pos());
			} catch (IOException e) {
				return smtConfig.responseFactory.error(e.toString(),this.filename.pos());
			} catch (ParserException e) {
				return smtConfig.responseFactory.error(e.toString(),e.pos());
			} finally {
				if (fileReader != null) {
					try { 
						fileReader.close(); 
					} catch (IOException e) { 
						return smtConfig.responseFactory.error("Failed to close input file: " + e,this.filename.pos());
					}
				}
			}
		}
		if (commands == null) {
			return smtConfig.responseFactory.error("INTERNAL ERROR: Unexpected null command list in a script");
		}
		Iterator<ICommand> iter = commands.iterator();
		IResponse response = smtConfig.responseFactory.success();
		ICommand s;
		while (iter.hasNext() && !response.isError()) {
			s = iter.next();
			// TODO: should we typecheck the entire script before executing it?
			response = s.execute(solver);
			// TODO: If we include this output, we need a way to control it via the API so OpenJML can control it
			//if (!r.isOK()) smtConfig.log.logDiag(smtConfig.defaultPrinter.toString(r));
		}
		return response;
	}
	
	/** The accept method for visitor classes; the type parameter is the return type of the accept and visit methods */
	@Override
	public </*@Nullable*/T> /*@Nullable*/T accept(IVisitor</*@Nullable*/T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}