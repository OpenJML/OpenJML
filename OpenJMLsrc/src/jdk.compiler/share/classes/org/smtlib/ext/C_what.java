/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.ext;

import java.io.IOException;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IParser.ParserException;
import org.smtlib.*;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;
import org.smtlib.solvers.Solver_test;

/** Implements the non-standard what command.  This command takes an arbitrary number of
 * arguments, all Symbols, and prints the Sort of each one; if there are no arguments,
 * the command prints all of the defined ids.
 * FIXME - the output is not in SExpr form.
 * @author David R. Cok
 *
 */
public class C_what extends Command implements Iwhat {

	/** The command name */
	public static final String commandName = "what";
	
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	/** The ids that are the arguments of the command */
	protected List<IIdentifier> ids;
	
	/** The ids that are the arguments of the command */
	@Override
	public List<IIdentifier> ids() { return ids; }

	public C_what(List<IIdentifier> ids) {
		this.ids = ids;
	}
	
	/** Parses the input concrete S-expression syntax to produce a command instance */
	static public /*@Nullable*/C_what parse(Parser p) throws IOException, ParserException {
		if (!p.smt().relax) {
			error(p.smt(),"Invalid SMT-LIB command: " + commandName, p.commandName.pos());
			return null;
		}
		List<IIdentifier> ids = new LinkedList<IIdentifier>();
		while (!p.isRP()) {
			if (p.isEOD()) {
				p.smt().log.logError(p.smt().responseFactory.error("Unexpected end of data while parsing a what command",
						p.savedlp == null ? null : p.pos(p.savedlp.pos().charStart(),p.currentPos())));
						// Note: actually p.savedlp should not ever be null - a bit defensive here
				return null;
			}
			IIdentifier id = p.parseIdentifier();
			if (id == null) return null;
			ids.add(id);
		}
		return new C_what(ids);
	}

	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException {
		try {
			p.writer().append("(" + commandName);
			for (IIdentifier id: ids()) {
				p.writer().append(" ");
				id.accept(p);
			}
			p.writer().append(")");
		} catch (IVisitor.VisitorException e) {
			p.error(e.getMessage());
		}
	}

	@Override
	public IResponse execute(ISolver solver) {
		SMT.Configuration smtConfig = solver.smt();
		if (!(solver instanceof Solver_test)) {
			return smtConfig.responseFactory.error("This kind of solver (" + solver.getClass() + ") is not able to execute a what command",null);
		}
		IPrinter printer = smtConfig.defaultPrinter;
		SymbolTable symTable = ((Solver_test)solver).symTable; 
		Iterator<IIdentifier> iter = ids().iterator();
		if (!iter.hasNext()) {
			// No arguments - print everything in the symbol table
			SymbolTable.Iterator symiter = symTable.iterator();
			while (symiter.hasNext()) {
				SymbolTable.Entry n = symiter.next();
				smtConfig.log.logOut(printer.toString(n.name) + " : " + printer.toString(n.sort));
			}
		} else {
			while (iter.hasNext()) {
				IIdentifier s = iter.next();
				ISort.IDefinition sortDef = symTable.lookupSort(s); 
				if (sortDef != null) smtConfig.log.logOut(printer.toString(s) + " : " + printer.toString(sortDef));
				else {
					Map<Integer,List<SymbolTable.Entry>> map = symTable.lookup(s);
					if (map != null && map.size() != 0) {
						for (List<SymbolTable.Entry> entrylist : map.values()) {
							for (SymbolTable.Entry entry: entrylist) {
								smtConfig.log.logOut(printer.toString(s) + " : " + printer.toString(entry.sort));
							}
						}
					} else {
						smtConfig.log.logOut(printer.toString(s) + " : -no entry- ");
					}
				}
			}
		}
		return smtConfig.responseFactory.success();
	}
	
	@Override
	public </*@Nullable*/T> /*@Nullable*/T accept(IVisitor</*@Nullable*/T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
