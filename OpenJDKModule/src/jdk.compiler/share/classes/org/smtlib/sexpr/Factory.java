/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.sexpr;

import java.io.InputStream;
import java.io.StringWriter;
import java.io.Writer;

import org.smtlib.IParser;
import org.smtlib.IPrinter;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.impl.Pos;

/** This is the factory for classes that are part of this particular concrete representation
 * of SMT-LIB syntax: Parser, Printer, Source for parsers.
 * @author David R. Cok
 */
public class Factory implements IParser.IFactory {
	
	@Override
	public Parser createParser(SMT.Configuration smtConfig, ISource source) {
		return new Parser(smtConfig, source);
	}
	
	@Override 
	public Pos.Source createSource(CharSequence cs, /*@Nullable*/String location) {
		return new Pos.Source(cs, location);
	}

	@Override 
	public Pos.Source createSource(SMT.Configuration smtConfig, java.io.File file) throws java.io.FileNotFoundException {
		return new Pos.Source(smtConfig, file);
	}
	
	@Override 
	public Pos.Source createSource(SMT.Configuration smtConfig, InputStream file, Object location) {
		return new Pos.Source(smtConfig, file, location);
	}
	
	@Override
	public IPrinter createPrinter(SMT.Configuration smtConfig, Writer w) {
		return new Printer(w);
	}
	
	/** This method will initialize the factories and default printer in the configuration
	 * with appropriate objects from this implementation; it should be called as part of
	 * initial set up of the configuration.
	 */
	static public void initFactories(SMT.Configuration config) {
		config.defaultPrinter = new Printer(new StringWriter());
		config.smtFactory = new Factory();
	}

}