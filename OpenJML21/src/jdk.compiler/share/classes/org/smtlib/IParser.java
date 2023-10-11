/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.io.IOException;
import java.io.Writer;
import java.util.List;

import org.smtlib.IExpr.IBinding;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.impl.Sort;
import org.smtlib.IPrinter;

/** This is the interface to a parser for SMT-LIB.  The interface is independent
 * of the concrete syntax being used; a specific implementation of this interface
 * will implement a specific concrete syntax for the SMT-LIB abstract syntax.
 */
public interface IParser {
	
	/** Returns the configuration with which the parser was instantiated. */
	SMT.Configuration smt();
	
	/** Returns true if the parser is at the end of data */
	boolean isEOD() throws IOException, ParserException;
	
	/** Returns the most recent error, or null */
	IResponse.IError lastError();
	
	/** Skips remainder of current line */
	void abortLine();
	
	/** Parse an attribute (keyword with optional value), returning null with error messages
	 * if an error occurs.
	 */
	/*@Nullable*/IExpr.IAttribute<?> parseAttribute() throws ParserException;

	/** Parses a value for an attribute, returning null with error messages if an error occurs */
	/*@Nullable*/IAttributeValue parseAttributeValue() throws ParserException;

	/** Parses an SMT-LIB command, if the parser is looking at text representing
	 * a valid SMT-LIB command; returns null and logs errors if the text is not a
	 * valid command.
	 * @return the command or null
	 * @throws java.io.IOException if an IO problem happened during parsing
	 */
	/*@Nullable*/ ICommand parseCommand() throws IOException, ParserException;
	
	/** Parses an SMT-LIB command script.  The result is either a string literal or a 
	 * parenthesized list of commands (which are parenthesized themselves); the string literal
	 * denotes the name of a file from which the commands are read when the command is executed;
	 * if the script is included directly, it is parsed, but typechecking is performed in
	 * context upon execution.
	 * If any errors occur, messages are logged
	 * and null is returned, with the parser advancing through a matching right parenthesis.
	 * @return the parsed script
	 * @throws java.io.IOException if an IO error occurs in reading input
	 * @throws ParserException if an unrecoverable error occurs in parsing tokens
	 */
	/*@Nullable*/ ICommand.IScript parseScript() throws IOException, ParserException;
	
	/** Parses a term or formula; return null and log an error response if there is no term or formula */
	/*@Nullable*/ IExpr parseExpr()  throws ParserException;
	
	/** Parse an SMT-LIB symbol; return null and log an error response if there is no symbol */
	/*@Nullable*/ IExpr.ISymbol parseSymbol()  throws ParserException;
	
	/** Parse an SMT-LIB literal of any kind; return null and log an error response if there is no literal */
	/*@Nullable*/ IExpr.ILiteral parseLiteral()  throws ParserException;
	
	/** Parse an SMT-LIB numeral; return null and log an error response if there is no numeral */
	/*@Nullable*/ IExpr.INumeral parseNumeral()  throws ParserException;
	
	/** Parse an SMT-LIB decimal literal; return null and log an error response if there is no numeral */
	/*@Nullable*/ IExpr.IDecimal parseDecimal()  throws ParserException;
	
	/** Parse an SMT-LIB binary literal; return null and log an error response if there is no numeral */
	/*@Nullable*/ IExpr.IBinaryLiteral parseBinary()  throws ParserException;
	
	/** Parse an SMT-LIB hex literal; return null and log an error response if there is no numeral */
	/*@Nullable*/ IExpr.IHexLiteral parseHex()  throws ParserException;
	
	/** Parse an SMT-LIB string literal; return null and log an error response if there is no valid string literal */
	/*@Nullable*/ IExpr.IStringLiteral parseStringLiteral()  throws ParserException;
	
	/** Parse an SMT-LIB keyword; return null and log an error response if there is no valid keyword */
	/*@Nullable*/ IExpr.IKeyword parseKeyword()  throws ParserException;
	
	/** Parses a qualified identifier (either a symbol, a parameterized identifier, or an as identifier)
	 * from the token stream, returning null (with logged error messages) if there is not one.
	 */
	/*@Nullable*/ IQualifiedIdentifier parseQualifiedIdentifier() throws ParserException;

	/** Parses an identifier (either a symbol or a parameterized identifier)
	 * from the token stream, returning null (with logged error messages) if there is not one.
	 */
	/*@Nullable*/ IIdentifier parseIdentifier() throws ParserException;

	
	/** Parses a sort, returning null with error messages if a valid sort is not in the 
	 * next parser tokens.
	 */
	/*@Nullable*/ ISort parseSort(List<ISort.IParameter> parameters) throws ParserException;

		/** Parse an SMT-LIB logic; return null and log an error response if there is no valid logic definition */
	/*@Nullable*/ ILogic parseLogic() throws ParserException;
	
	/** Parse an SMT-LIB theory; return null and log an error response if there is no valid theory definition */
	/*@Nullable*/ ITheory parseTheory() throws ParserException;
	
	/** Parses a binding "(id expression)", returning null with error messages if an error occurs */
	/*@Nullable*/ IBinding parseBinding() throws IOException, ParserException;

	/** Parses a declaration "(id sort)", returning null with error messages if an error occurs */
	/*@Nullable*/ IDeclaration parseDeclaration() throws IOException, ParserException;
	
	/** Parses a parenthesized sequence of let-bindings, returning null with error messages if an error occurs */
	/*@Nullable*/ List<IBinding> parseBindings() throws IOException, ParserException;

	/** Parses a parenthesized sequence of IDeclaration items, returning null with error messages if an error occurs */
	/*@Nullable*/ List<IDeclaration> parseDeclarations() throws IOException, ParserException;
	
	/** The interface for the parser/printer factory */
	public static interface IFactory {
		/** Creates a parser that reads and parses concrete syntax from the given source */
		IParser createParser(SMT.Configuration smtConfig, ISource source);
		
		/** Creates a character source from the given CharSequence; the second argument is just to be
		 * used as a location designator.
		 */
		ISource createSource(CharSequence cs, /*@Nullable*/String filepath);
		
		/** Creates a character source from the given file */
		ISource createSource(SMT.Configuration smtConfig, java.io.File file) throws java.io.FileNotFoundException;

		/** Creates a character source from the given stream */
		ISource createSource(SMT.Configuration smtConfig, java.io.InputStream file, Object location);

		/** Creates a printer */
		IPrinter createPrinter(SMT.Configuration smtConfig, Writer w);
	}
	
	/** An exception thrown if parsing is to be aborted. */
	public static class ParserException extends Exception {
		private static final long serialVersionUID = 1L;
		
		/** The location of the parsing problem */
                @SuppressWarnings("serial")
		protected /*@Nullable*//*@ReadOnly*/ IPos pos;

		/** Creates a parse exception from the given error message and problem location */
		public ParserException(String msg, /*@Nullable*//*@ReadOnly*/IPos pos) { 
			super(msg); 
			this.pos = pos;
		}

		/** Returns the error position */
		public /*@Nullable*//*@ReadOnly*/ IPos pos() { return this.pos; }
	}
	
	/** An exception to be thrown if there is an unrecoverable problem scanning the syntax */
	public static class SyntaxException extends ParserException {
		private static final long serialVersionUID = 1L;

		/** Creates an exception from the given error message and problem location */
		public SyntaxException(String msg, /*@Nullable*//*@ReadOnly*/IPos pos) { super(msg, pos); }
	}
	
	/** An exception to be thrown if parsing is to be intentionally aborted (and restarted, ignoring 
	 * any tokens since the last successful call to the parser. */
	public static class AbortParseException extends ParserException {
		private static final long serialVersionUID = 1L;

		/** Creates an exception that intentionally aborts the current parse */
		public AbortParseException() { super("",null); }
	}
}
