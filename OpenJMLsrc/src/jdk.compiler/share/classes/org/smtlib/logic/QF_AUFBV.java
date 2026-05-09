package org.smtlib.logic;

import java.util.Collection;

import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.ISymbol;

/** This logic does not allow quantifiers */
public class QF_AUFBV extends QF_UF {

	public QF_AUFBV(ISymbol name, Collection<IAttribute<?>> attributes) {
		super(name,attributes);
	}
	
	// FIXME - needs restriction on parameters of Array Sorts
}
