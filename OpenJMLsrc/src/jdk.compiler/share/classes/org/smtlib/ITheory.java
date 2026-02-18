/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.util.Map;

import org.smtlib.IExpr.ISymbol;
import org.smtlib.IExpr.IKeyword;

/** This interface represents a definition of an SMT-LIB theory */
public interface ITheory extends IAccept {
	/** The name of the theory */
	ISymbol theoryName();
	
	/** The attributes (keyword-value pairs) of the theory. */
	//@ ensures \result.size() > 0;
	Map<IKeyword,IExpr.IAttribute<?>> attributes();
	
	/** The value of an attribute; returns null if the attribute does not exist for this theory */
	/*@Nullable*/IAttributeValue value(IKeyword keyword);
	
	// TODO - do we export the pre-defined symbols?
}
