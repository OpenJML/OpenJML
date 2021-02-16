/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.util.Map;

import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.ISymbol;

/** This interface represents a definition of an SMT_LIB logic */
public interface ILogic extends IAccept, ILanguage {
	/** The name of the logic */
	ISymbol logicName();
	
	/** The attributes of the logic */
	//@ ensures \result.size() > 0;
	Map<IKeyword,IAttribute<?>> attributes();
	
	/** The value of an attribute; returns null if the attribute does not exist for this logic. */
	/*@Nullable*/IAttributeValue value(IKeyword keyword);
}
