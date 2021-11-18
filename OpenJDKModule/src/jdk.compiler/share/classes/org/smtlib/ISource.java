package org.smtlib;

/** This interface represents sources of characters.  The source need not be fully available at
 * any given time, but it does need to be able to supply characters at a given position on demand
 * and to determine line numbers from the beginning of the source.
 */
public interface ISource {
	// NOTE - the methods are not necessarily pure, since the internals may change.  However, the
	// implicit character content should not change.
	
	/** The internal character stream as a CharSequence.  We would like to avoid the constraint of
	 * having to have this kind of internal representation, but the parser uses Pattern and Matcher,
	 * which require a CharSequence.  The CharSequence might not contain all the characters that might
	 * ever be read, but will contain characters as they are read.
	 */
	CharSequence chars();
	
	/** Closes any open resources - the source is not usable after this call. */
	void close();
	
	/** User-specified identification of the location of the source; the user is responsible to use
	 * the result in the way in which the source object was created.
	 * @return the location object of the source
	 */
	/*@Nullable*/ Object location();
	
	/** Returns the character at the given character position within the source. Character positions 
	 * begin at 0.*/
	//@ requires pos >= 0;
	char charAt(int pos);
	
	/** Returns the character position of the beginning of the line containing the given position. 
	 * Character positions begin at 0.*/
	//@ requires pos >= 0;
	//@ ensures 0 <= \result && \result <= pos;
	int lineBeginning(int pos);
	
	/** Returns the text of the line containing the given position, at least through the given position,
	 * and always ending with a (perhaps added) line termination sequence. Character positions begin at 0.
	 * @param pos a character position
	 * @return the line of text containing that character position
	 */
	//@ requires pos >= 0;
	String textLine(int pos);
	
	/** Returns the number (beginning with 1) of the line containing the given character position (which begins at 0). */
	//@ requires pos >= 0;
	//@ ensures \result > 0;
	int lineNumber(int pos);
}