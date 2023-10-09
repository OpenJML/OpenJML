/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

/** This is an interface that supplies information about a range in textual position within
 * a source of characters.
 * @author David R. Cok
 */
public interface IPos {
	
	/** This interface identifies classes that can have their position set */
	static public interface IPosable {
		/** Textual position of this object */
		/*@Nullable*//*@ReadOnly*/IPos pos();
		
		/** Setting the textual position*/
		void setPos(/*@Nullable*//*@ReadOnly*/IPos pos);

	}
	
	/** Returns the source object containing the characters */
	public abstract /*@Nullable*/ ISource source() /*@ReadOnly*/;
	
	/** The starting position within the character sequence (0-based) */
	public abstract int charStart() /*@ReadOnly*/;

	/** One beyond the last position of the character sequence range (0-based). */
	public abstract int charEnd() /*@ReadOnly*/;
}