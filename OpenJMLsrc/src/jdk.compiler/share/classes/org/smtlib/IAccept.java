/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

/** This interface is defined and implemented as a marker that
 * the accept method is available and to ensure that
 * subtypes implement the accept method
 * @author David Cok
 */
public interface IAccept {
	/** The accept method corresponding the IVisitor, to be implemented in each subclass
	 * as { return v.visit(this); }
	 * @param <T> the return type desired from the visit methods
	 * @param v the visitor class
	 * @return the value returned by the visit method
	 */
	<T extends /*@Nullable*/Object> T accept(IVisitor<T> v) throws IVisitor.VisitorException;
}
