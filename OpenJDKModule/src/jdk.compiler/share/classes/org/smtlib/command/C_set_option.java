/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Iset_option;
import org.smtlib.*;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IParser.ParserException;
import org.smtlib.SMT.Configuration;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the set-option command */
public class C_set_option extends Command implements Iset_option {
	/** The command name */
	public static final String commandName = "set-option";
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	/** The keyword for the option to set */
	protected IKeyword option;
	
	/** The value of the option */
	protected IAttributeValue value;
	
	/** The keyword for the option to set */
	@Override
	public IKeyword option() { return option; }
	
	/** The new value of the option being set */
	@Override
	public IAttributeValue value() { return value; }

	/** Construct an instance of the command */
	public C_set_option(IKeyword keyword, IAttributeValue value) {
		super();
		this.option = keyword;
		this.value = value;
	}
	
	/** Creates a command instance by parsing the concrete S-expression syntax */
	static public /*@Nullable*/ C_set_option parse(Parser p) throws ParserException  {
		IKeyword key = p.parseKeyword();
		if (key == null) return null;
		IAttributeValue value = p.parseAttributeValue();
		if (value == null) return null;
		C_set_option c = new C_set_option(key,value);
		IResponse.IError r = c.checkOptionType(p.smt(), key, value);
		if (r == null) return c;
		p.smt().log.logError(r);
		return null;
	}


	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append("(" + commandName + " ");
		option.accept(p);
		p.writer().append(" ");
		value.accept(p);
		p.writer().append(")");
	}
	
	@Override
	public IResponse execute(ISolver solver) {
		if (prefixText != null) solver.comment(prefixText);
		return solver.set_option(option,value);
	}

	// FIXME-NOW review this method - checkOptionType - is it used?
	/** This method checks that the value for the given keyword has the correct type, when the keyword
	 * is used as the key for an SMT-LIB option.
	 * @param keyword the keyword controlling the type
	 * @param t the value being tested
	 * @return null or an error response
	 */
	public IResponse.IError checkOptionType(Configuration smtConfig, IKeyword keyword, IAttributeValue t) {
		String key = keyword.value();
		if (smtConfig.utils.boolOptions.contains(key)) {
			if (t instanceof IExpr.ISymbol && (((IExpr.ISymbol)t).value().equals("true") || ((IExpr.ISymbol)t).value().equals("false"))) return null;
			return smtConfig.responseFactory.error("Expected true or false as the value of " + keyword,t.pos());
		} else if (smtConfig.utils.stringOptions.contains(key)) {
			if (t instanceof IExpr.IStringLiteral) return null;
			return smtConfig.responseFactory.error("Expected a string as the value of " + keyword,t.pos());
		} else if (smtConfig.utils.numericOptions.contains(key)) {
			if (t instanceof IExpr.INumeral) return null;
			return smtConfig.responseFactory.error("Expected a numeral as the value of " + keyword,t.pos());
//		} else if (SMT.Configuration.atLeastVersion(SMTLIB.V25)) {
//			return smtConfig.responseFactory.error("Keyword not supported in V2.5 and higher: " + keyword,t.pos());
		} else {
			// Unspecified option - what kinds of values may it have? TODO
		}
		return null;
	}

	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
