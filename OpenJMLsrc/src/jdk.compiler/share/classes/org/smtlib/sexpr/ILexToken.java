package org.smtlib.sexpr;

import org.smtlib.IPos;

/** An interface to indicate AST classes that are also lexical tokens in the 
 * concrete syntax. 
 * @author David R. Cok
 *
 */
public interface ILexToken {
	/** The lexical position of the token */
	/*@Nullable*//*@ReadOnly*/ IPos pos();
	
	/** A short word characterizing the class of token (e.g. "numeral")*/
	String kind();
	
	boolean isError();
}
