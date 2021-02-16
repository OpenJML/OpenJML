/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.sexpr;

import java.util.List;

import org.smtlib.IAccept;
import org.smtlib.IAttributeValue;
import org.smtlib.IPos.IPosable;

/** This interface represents S-expressions as used in SMT-LIB;
 * they are used as values for attributes in the standard concrete
 * syntax.  
 */
public interface ISexpr extends IPosable, IAttributeValue, IAccept {
	
	/** A word characterizing the subclass */
	String kind();
	
	/** Represents a sequence of S-expressions */
	public static interface ISeq extends ISexpr {
		List<ISexpr> sexprs();
	}
	
	/** Represents a single S-expression token */
	public static interface IToken<T> extends ISexpr  {
		T value();
	}
	
	/** A factory to create components of S-expressions */
	public static interface IFactory {  // FIXME - not used; is this class in the correct place?
		ISeq createSeq(List<ISexpr> sexprs);
		<T> IToken<T> createToken(T value);
	}
	
}
