/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.command;

import java.io.IOException;

import org.smtlib.ICommand.Iset_option;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IParser.ParserException;
import org.smtlib.*;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

/** Implements the set-info command */
public class C_set_info extends Command implements Iset_option {
	/** The command name */
	public static final String commandName = "set-info";
	/** The command name */
	@Override
	public String commandName() { return commandName; }
	
	/** The keyword for the option to set */
	protected IKeyword option;
	
	/** The value of the option, which in general can be any attribute value */
	protected /*@Nullable*/IAttributeValue value;
	
	/** The keyword for the option to set */
	@Override
	public IKeyword option() { return option; }
	
	/** The value of the option, which in general can be any attribute value */
	@Override
	public IAttributeValue value() { return value; }

	/** Construct an instance of the command */
	public C_set_info(IKeyword keyword, IAttributeValue value) {
		super();
		this.option = keyword;
		this.value = value;
	}
	
	/** Creates a command instance by parsing the concrete S-expression syntax */
	static public /*@Nullable*/ C_set_info parse(Parser p) throws ParserException  {
		IKeyword key = p.parseKeyword();
		if (key == null) return null;
		IAttributeValue value = p.parseAttributeValue();
		if (value == null) return null;
		return new C_set_info(key,value);

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
		return solver.set_info(option,value);
	}



	@Override
	public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
		return v.visit(this);
	}
}
