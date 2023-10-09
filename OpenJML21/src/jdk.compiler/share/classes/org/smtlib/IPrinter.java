/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

/** An interface for printers to concrete syntax; factories are shared with Parsers
 * in IParser.IFactory.
 * @author David Cok
 */
public interface IPrinter {

	/** Prints the argument to the receiver */
	public <T extends IAccept> void print(T expr) throws IVisitor.VisitorException;
	
	/** Returns the argument as a String using a Printer of the same type as the receiver,
	 * but does not modify the receiver.
	 */
	public <T extends IAccept> String toString(T expr);
	
	public IPrinter newPrinter(java.io.Writer pw);

}
