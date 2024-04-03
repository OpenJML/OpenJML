/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.sexpr;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;
import java.util.regex.Matcher;

import org.smtlib.*;
import org.smtlib.ICommand.IScript;
import org.smtlib.IExpr.IAsIdentifier;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IBinaryLiteral;
import org.smtlib.IExpr.IBinding;
import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IHexLiteral;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.ILiteral;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.impl.*;
import org.smtlib.impl.SMTExpr.Keyword;
import org.smtlib.impl.SMTExpr.Numeral;
import org.smtlib.impl.SMTExpr.StringLiteral;
import org.smtlib.impl.SMTExpr.Symbol;

//import checkers.nullness.quals.Nullable;
/** Parses the standard SMT-LIB concrete syntax to produce ASTs of objects that
 * are instances of the org.smtlib.* interfaces.
 */
public class Parser extends Lexer implements IParser {
	/** A handle to the parent SMTConfig object, in order to see command-line options
	 * etc. that are fields of smtConfig */
	final private SMT.Configuration smtConfig;
	
	/** Returns a handle to the parent SMTConfig object, in order to see command-line options
	 * etc. that are fields of smtConfig */
	public SMT.Configuration smt() { return smtConfig; }
	
	/** The most recent error, or null */
	public /*@ Nullable */ IResponse.IError lastError = null;
	
	public /*@ Nullable */ IResponse.IError lastError() { return lastError; }
	
	/** The (common) factory used to generate objects */
	final protected IExpr.IFactory factory;
	
	/** Returns an IPos object for the given character start and end 
	 * positions and including a reference to the parser's source object. 
	 * @param start the start character position (counting from 0)
	 * @param end the end character position (one past the last actual character to be included)
	 * @return the IPos object representing the character range within the parser's current source
	 */
	public /*@Nullable*//*@ReadOnly*/ IPos pos(/*@Nullable*//*@ReadOnly*/IPos start, /*@Nullable*//*@ReadOnly*/IPos end) { 
		if (start == null || end == null) return null;
		return pos(start.charStart(),end.charEnd()); 
	}
	
	/** Returns an IPos object for the given character start and end 
	 * positions and including a reference to the parser's source object. 
	 * @param start the start character position (counting from 0)
	 * @param end the end character position (one past the last actual character to be included)
	 * @return the IPos object representing the character range within the parser's current source
	 */
	public /*@Nullable*/ IPos pos(int start, int end) { 
		return new Pos(start,end,source()); 
	} // Use factory instead of new Pos?
	
	/** Creates a Parser using an SMT configuration object and a source for
	 * characters; ordinarily use a factory to obtain a parser.
	 */
	public Parser(SMT.Configuration smtConfig, ISource src) {
		super(smtConfig, src);
		this.smtConfig = smtConfig;
		this.factory = smtConfig.exprFactory;
	}
		

	// See the documentation in the interface
	@Override
	public /*@Nullable*/ICommand.IScript parseScript() {
		// NOTE: interactive is set false here because it is only ever used for parsing exec scripts
		// if it is used to parse top-level scripts, we have to pass in the appropriate value
		boolean interactive = smtConfig.interactive;
		IScript scr;
		try {
			StringLiteral filename;
			if (!isLP()) {
				filename = parseStringLiteral();
				if (filename == null) return null;
				//scr = smtConfig.commandFactory.script(filename,null);
				scr = new Script(filename,null); // FIXME - use a factory, set position
				//scr = setPos(smtConfig.commandFactory.script(filename,null),filename.pos());// FIXME - set pos
			} else {
				// This loop skips over invalid commands, producing error messages (parseCommand
				// returns null); the resulting script is valid, but misses the invalid entries
				smtConfig.interactive = false;
				ICommand s;
				List<ICommand> res = new LinkedList<ICommand>();
				parseLP();
				boolean anyError = false;
				while (!isRP()) {
					s = parseCommand();
					if (s != null) res.add(s);
					else anyError = true;
				}
				ILexToken rp = parseRP();
				if (rp == null || anyError) return null;
				scr = new Script(null,res); // FIXME - use a factory, set position
				// FIXME set pos pos(lp.pos(),rp.pos(),source);
			}
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Completed input");
		} catch (ParserException e) {
			smtConfig.log.logError(smt().responseFactory.error(
					"A failure occurred while parsing a command: " + e,
					e.pos()));
			return null;
		} finally {
			smtConfig.interactive = interactive;
		}
		return scr;
	}
	
	/** This field is used to communicate the beginning LP while parsing commands */
	public /*@Nullable*/ ILexToken savedlp;
	
	/** This field is used only to communicate the position of the name of a command to the command creator
	 * (instead of using method arguments).
	 */
	public /*@ReadOnly*/ ISymbol commandName;
	
	/** Parses the next text in the source as a SMT-LIB command; if an error occurs, the error is logged
	 * and the method skips through a matching number of right parentheses
	 *  @return returns the parsed command, or EOD.eod if the end of input has been reached, 
	 *  or null if no valid command could be parsed
	 */
	//@ nullable
	/*@Nullable*/
	/*@Mutable*/
	public Command parseCommand() {
		boolean savedTopLevel = smtConfig.topLevel;
		Command command = null;
		try {
			while (true) { // The while loop is just so that AbortParseException can cause a retry
				try {
					ILexToken rp = null;
					savedlp = parseLP();
					if (savedlp == null) {
						// We have not consumed a token - if we don't we may get into
						// an infinite loop; if we skipThruRP, we may consume the
						// whole file - so we skip to an LP
						do { getToken(); } while (!isLP() && !isEOD());
						return null;
					}
					String prefixText = prefixCommentText;
					smtConfig.topLevel = false;
					Symbol sym = parseSymbolOrReservedWord("Expected a symbol here, not a #");
					if (sym == null) {
						skipThruRP();
						return null;
					}
					commandName = sym;
					String name = sym.value();
					try {
						// To create a command, we invoke the 'parse' method (that has a Parser argument)
						// in the class corresponding to the given command name.
						// The parse method is supposed to consume its argument from the parser source;
						// the method does not parse the final right-parenthesis or check that there is no
						// extraneous material beyond the last argument parsed - those checks are done here
						// for all commands. We also set the IPos value for the command here.
						// If an error occurs in parsing the command, an error message should be logged and
						// null returned (if null is returned, an error message is expected to have been logged).
						
						// This call translates a name to the class that implements the command with that name.
						// The user can change the lookup behavior by assigning a new command finder object in
						// the configuration
						Class<? extends ICommand> clazz = smt().commandFinder.findCommand(name);
						if (clazz == null) {
							lastError = error("Unknown command: " + name,sym.pos());
							command = null;
						} else {
							// Call the static parser method of the command class; that will create an
							// instance of the appropriate command, initialized according to the parsed data.
							// If the parse fails, null is returned and an error will have been logged.
							Method m = clazz.getMethod("parse",Parser.class);
							command = (Command)m.invoke(null,this);
							rp = null;
							if (command != null) {
								if (!isRP()) {
									lastError = error("Too many arguments or extraneous material after the command or missing right parenthesis",
											//pos(currentPos()-1,currentPos()));
											peekToken().pos());
								} else {
									rp = parseRP();
								}
							}
						}
					} catch (InvocationTargetException ex) {
                        ex.printStackTrace(System.out);
						if (ex.getTargetException() instanceof StackOverflowError) {
							lastError = error("Stack overflow occurred while parsing input", sym.pos());
							throw new ParserException(null,null);
						} else if (ex.getTargetException() instanceof OutOfMemoryError) {
							lastError = error("Out of memory error occurred while parsing input", sym.pos());
							throw new ParserException(null,null);
						} else {
							lastError = error(ex.getTargetException().toString(),sym.pos());
	                        ex.getTargetException().printStackTrace(System.out);
						}
					}
					if (command == null) {
						skipThruRP();
					} else if (rp == null) {
						skipThruRP();
						command = null;
					}
					if (command != null) {
						setPos(command,pos(savedlp.pos(),rp.pos()));
						command.prefixText = prefixText;
					}
				} catch (AbortParseException e) {
					smtConfig.log.logOut("Input aborted\n");
					smtConfig.topLevel = true;
					continue;
				} catch (ParserException e) {
					Matcher m = skipThroughEndOfLine.matcher(csr);
					m.region(matcher.regionStart(),matcher.regionEnd());
					if (e.getMessage() != null) lastError = smtConfig.log.logError(smtConfig.responseFactory.error(e.getMessage(),e.pos()));
					if (m.lookingAt()) {
						//smtConfig.log.logOut("SKIPPED " + m.start() + " " + m.end());
						matcher.region(m.end(),matcher.regionEnd());
					} else {
						//smtConfig.log.logOut("NOTHING TO SKIP");
					} // If the match fails, there was nothing left before the end of the line
				}
				break;
			}
		} catch (Exception e) {
			IPos pos = new Pos(0,0,null);
			lastError = smtConfig.responseFactory.error("Error while parsing command: " + e,pos);
			e.printStackTrace(System.out); // FIXME - should write to the log output
			smtConfig.log.logError(lastError);
		} finally {
			smtConfig.topLevel = savedTopLevel;
		}
		return command;
	}
	
	/** A helper check, called by command-specific parse methods in which the commands have no arguments */
	//@ requires savedlp != null && commandName != null;
	public boolean checkNoArg() {
		try {
			if (!isRP()) {
				if (isEOD()) {
					smtConfig.log.logError(smtConfig.responseFactory.error(
							"The input ends with an unmatched left parenthesis",
							pos(savedlp.pos(),savedlp.pos())));
					return false;
				}
				smtConfig.log.logError(smtConfig.responseFactory.error(
						"A " + commandName + " command takes no arguments",
						peekToken().pos())); 
				return false;
			} else {
				return true;
			}
		} catch (ParserException e) {
			smtConfig.log.logError(smt().responseFactory.error(
					"A failure occurred while parsing a command: " + e,
					e.pos()));
			return false;
		}

	}


	/** Parses an Sexpr
	 * @return an Sexpr or null if no more input
	 * @throws ParserException if a parsing problem occurred, such as an invalid token or mismatched parentheses
	 */
	// FIXME - should this log errors and return null instead of throwing an exception?
	/*@Nullable*/
	public ISexpr parseSexpr() throws ParserException {
		if (isEOD()) return null;
		ILexToken t = getToken();
		if (t.toString() == IPLexToken.RP) {
			throw new ParserException("Unexpected right parenthesis",t.pos());
		}
		if (t.toString() == IPLexToken.LP) {
			boolean saved = smtConfig.topLevel;
			smtConfig.topLevel = false;
			Sexpr res = parseSeq(t);
			smtConfig.topLevel = saved; // FIXME - use a try-finally block?
			return res;
		} 
		if (!(t instanceof ISexpr)) {
			throw new ParserException("Token is not an S-expression token: " + t.getClass(),t.pos());
		}
		return (ISexpr)t;
	}
	
	/** Parses and adds Sexpr to a list until parseSexpr returns null (indicating
	 * a RightParen has been seen or end of input or an error)
	 * @return a SExpr.Seq containing the sequence of SExpr seen
	 * @throws ParserException FIXME - no more of these?
	 */
	public Sexpr.Seq parseSeq(ILexToken lp) throws ParserException {
		Sexpr.Seq seq = new Sexpr.Seq(); // FIXME - use factory
		
		while (true) {
			ILexToken token = getToken();
			if (token.toString() == IPLexToken.RP) {
				seq.setPos(pos(lp.pos(),token.pos()));
				return seq;
			} else if (token.toString() == IPLexToken.EMPTY) {
				throw new IParser.ParserException("Unbalanced parentheses at end of input",pos(lp.pos(),lp.pos()));
			} else if (token.toString() == IPLexToken.LP) {
				ISexpr sexpr = parseSeq(token);
				seq.sexprs().add(sexpr);
			} else if (token instanceof ISexpr) {
				seq.sexprs().add((ISexpr)token);
			} else {
				// FIXME - invalid token
			}
		}
	}

	/** Parses a qualified identifier (either a symbol, a parameterized identifier, or an as identifier)
	 * from the token stream, returning null (with logged error messages) if there is not one.
	 */
	@Override
	public /*@Nullable*/IQualifiedIdentifier parseQualifiedIdentifier() throws ParserException {
		if (!isLP()) {
			return parseSymbol();
		} else {
			ILexToken lp = parseLP(); // will succeed since isLP() was true
			ISymbol head = parseSymbolOrReservedWord("Expected a symbol here, not a #");
			if (head == null) { 
				 
			} else if (head.toString().equals("as")) {
				return parseAsIdentifierRest(lp);
			} else if (head.toString().equals("_")) {
				return parseIdentifierRest(lp);
			} else {
				error("Invalid beginning of an identifer: expected either 'as' or '_' here",head.pos());
			}
			skipThruRP();
			return null; // Unsuccessful parsing
		}
	}
	
//	private <T extends IPos.IPosable> T setPos(T p, IPos pos) { p.setPos(pos); return p; }
	
	/** Parses an 'as' identifier, presuming the left-paren and the 'as' are already parsed,
	 * from the token stream, returning null (with logged error messages) if there is not one.
	 */
	private /*@Nullable*/ IAsIdentifier parseAsIdentifierRest(ILexToken lp) throws ParserException {
		IIdentifier name = parseIdentifier();
		if (name == null) return null;
		ISort sort = parseSort(null);
		if (sort == null) { skipThruRP(); return null; }
		ILexToken rp = parseRP();
		if (rp == null) { skipThruRP(); return null; }
		IPos pos = pos(lp.pos(),rp.pos());
		return setPos(smtConfig.exprFactory.id(name,sort),pos);
	}
	
	/** Parses an identifier (either symbol or parameterized identifier) from the token
	 * stream, returning null with logged error messages if there is not one.
	 */
	public /*@Nullable*/IIdentifier parseIdentifier() throws ParserException {
		if (!isLP()) {
			return parseSymbol();
		} else {
			ILexToken lp = parseLP();
			ISymbol head = parseSymbolOrReservedWord("Expected a symbol here, not a #");
			if (head == null) { 
				// continue 
			} else if (head.toString().equals("_")) {
				return parseIdentifierRest(lp);
			} else {
				error("Invalid beginning of an identifer: expected a '_' here",head.pos());
			}
			skipThruRP();
			return null; // Unsuccessful parsing
		}
	}
	
	/** Parses a parameterized identifier from the token stream, presuming the left
	 * parenthesis and the underscore character are already read, return null with 
	 * logged error messages if there is not one.
	 * @param lp the token for the left parenthesis that starts the identifier
	 * @return the token or null
	 * @throws ParserException if unrecoverable error occurs
	 */
	private IIdentifier parseIdentifierRest(ILexToken lp) throws ParserException {
		ISymbol name = parseSymbol();
		if (name == null) { skipThruRP();  return null; }
		List<INumeral> numerals = new LinkedList<INumeral>();
		do {
			if (isEOD()) { 
				error("Unexpected end of data while parsing a parameterized identifier",pos(lp.pos().charStart(),currentPos()));
				return null; 
			}
			INumeral num = parseNumeral();
			if (num == null)  { skipThruRP();  return null; }
			numerals.add(num);
		} while (!isRP());
		ILexToken rp = parseRP();
		if (rp == null)  { skipThruRP();  return null; }
		IPos pos = pos(lp.pos(),rp.pos());
		return setPos(smtConfig.exprFactory.id(name,numerals),pos);
	}
	
	/** Parses an expression, returning null with error messages if there is not a valid
	 * expression in the token stream.
	 */
	@Override
	public /*@Nullable*/IExpr parseExpr() throws ParserException {
		// Here we suffer a bit for using a hand-written top-down parser.
		// An IExpr can be
		//		literal
		//		symbol
		//		( _ symbol numeral+ )
		//		( as identifier sort )
		//		( ! ...
		//		( forall ...
		//		( exists ...
		//		( let ...
		//		( symbol ...
		//		( ( _ symbol ...
		//		( ( as ...
		if (!isLP()) {
			ILexToken token = getToken();
			if (token instanceof SMTExpr.Error) return null;
			if (token instanceof IExpr) return (IExpr)token; // FIXME - do we need to check that this is just a literal or symbol
			if (!(token instanceof SMTExpr.Error)) error("Expected an expression here",token.pos());
			return null;
		}
		ILexToken lp = getToken();
		IQualifiedIdentifier head;
		if (!isLP()) {
			head = parseSymbolOrReservedWord("Expected an identifier or reserved word here, not a #");
		} else {
			head = parseQualifiedIdentifier();
		}
		if (head == null) { skipThruRP(); return null; }
		if (head instanceof ISymbol) { // in particular we want reserved words here
			String s = ((ISymbol)head).value();
			if (Utils.FORALL.equals(s)) {
				List<IDeclaration> decls = parseDeclarations();
				IExpr expr = decls == null ? null : parseExpr();
				ILexToken rp = expr == null ? null : parseRP();
				if (rp == null) { skipThruRP(); return null ; }
				return setPos(smtConfig.exprFactory.forall(decls, expr), pos(lp.pos(), rp.pos()));
			} else if (Utils.EXISTS.equals(s)) {
				List<IDeclaration> decls = parseDeclarations();
				IExpr expr = decls == null ? null : parseExpr();
				ILexToken rp = expr == null ? null : parseRP();
				if (rp == null) { skipThruRP(); return null ; }
				return setPos(smtConfig.exprFactory.exists(decls, expr), pos(lp.pos(), rp.pos()));
			} else if (Utils.LET.equals(s)) {
				List<IBinding> decls = parseBindings();
				IExpr expr = decls == null ? null : parseExpr();
				ILexToken rp = expr == null ? null : parseRP();
				if (rp == null) { skipThruRP(); return null ; }
				return setPos(smtConfig.exprFactory.let(decls, expr), pos(lp.pos(), rp.pos()));
			} else if (Utils.AS.equals(s)) {
				return parseAsIdentifierRest(lp);
			} else if (Utils.UNDERSCORE.equals(s)) {
				return parseIdentifierRest(lp);
			} else if (Utils.NAMED_EXPR.equals(s)) {
				IExpr expr = parseExpr();
				if (expr instanceof IExpr.IError) expr = null;
				List<IAttribute<?>> list = parseAttributeSequence();
				if (list == null) { skipThruRP(); return null; }
				ILexToken rp = parseRP();
				if (rp == null) { skipThruRP(); return null; }
				return setPos(smtConfig.exprFactory.attributedExpr(expr,list),pos(lp.pos(), rp.pos()));
			}
		}
		List<IExpr> list = new LinkedList<IExpr>();
		boolean anyErrors = false;
		while (!isRP()) {
			if (isEOD()) {
				error("Unexpected end of data while parsing a sequence of expressions",pos(lp.pos().charStart(),currentPos()));
				return null; 
			}
			IExpr e = parseExpr();
			if (e != null) list.add(e);
			else anyErrors = true;
		}
		if (anyErrors) { skipThruRP(); return null; }
		ILexToken rp = parseRP();
		if (rp == null) { skipThruRP(); return null; }
		if (list.size() == 0) {
			error("A function expression must have at least one argument",pos(lp.pos(),rp.pos()));
			return null;
		}
		return setPos(smtConfig.exprFactory.fcn(head,list), pos(lp.pos(), rp.pos()));
	}
	
	/** Parses a parenthesized sequence of IDeclaration items, returning null with error messages if an error occurs */
	public /*@Nullable*/List<IDeclaration> parseDeclarations() throws ParserException {
		ILexToken lp = parseLP();
		if (lp == null) return null;
		Set<ISymbol> names = new HashSet<ISymbol>();
		List<IDeclaration> decls = new LinkedList<IDeclaration>();
		while (!isRP()) {
			if (isEOD()) {
				error("Unexpected end of data while parsing a sequence of declarations",pos(lp.pos().charStart(),currentPos()));
				return null; 
			}
			IDeclaration decl = parseDeclaration();
			if (decl == null) { skipThruRP(); return null; }
			decls.add(decl);
			if (!names.add(decl.parameter())) {
				error("Parameter list has a duplicate name: " + smtConfig.defaultPrinter.toString(decl.parameter()),decl.parameter().pos());
				return null;
			}
		}
		ILexToken rp = parseRP();
		if (rp == null) { skipThruRP(); return null; }
		return decls;
	}

	/** Parses a parenthesized sequence of let-bindings, returning null with error messages if an error occurs */
	public /*@Nullable*/List<IBinding> parseBindings() throws ParserException {
		ILexToken lp = parseLP();
		if (lp == null) return null;
		List<IBinding> decls = new LinkedList<IBinding>();
		Set<ISymbol> names = new HashSet<ISymbol>();
		while (!isRP()) {
			if (isEOD()) {
				error("Unexpected end of data while parsing a sequence of parameter bindings",pos(lp.pos().charStart(),currentPos()));
				return null; 
			}
			IBinding decl = parseBinding();
			if (decl == null) { skipThruRP(); return null; }
			decls.add(decl);
			if (!names.add(decl.parameter())) {
				error("Parameter list has a duplicate name: " + smtConfig.defaultPrinter.toString(decl.parameter()),decl.parameter().pos());
				return null;
			}
		}
		ILexToken rp = parseRP();
		if (rp == null) { skipThruRP(); return null; }
		return decls;
	}

	/** Parses a declaration "(id sort)", returning null with error messages if an error occurs */
	@Override
	public /*@Nullable*/IDeclaration parseDeclaration() throws ParserException {
		ILexToken lp = parseLP();
		ISymbol sym = lp == null ?  null : parseSymbol();
		ISort sort = sym == null ? null : parseSort(null);
		ILexToken rp = sort == null ? null : parseRP();
		if (rp == null) return null;
		//ISymbol.IParameter p = new Symbol.Parameter(sym); // FIXME - use a factory
		return setPos(smtConfig.exprFactory.declaration(sym,sort), pos(lp.pos(), rp.pos()));
	}

	/** Parses a binding "(id expression)", returning null with error messages if an error occurs */
	@Override
	public /*@Nullable*/IBinding parseBinding() throws ParserException {
		ILexToken lp = parseLP();
		ISymbol sym = lp == null ?  null : parseSymbol();
		IExpr expr = sym == null ? null : parseExpr();
		ILexToken rp = expr == null ? null : parseRP();
		if (rp == null) return null;
		//ISymbol.ILetParameter p = new Symbol.LetParameter(sym); // FIXME - use a factory
		return setPos(smtConfig.exprFactory.binding(sym,expr), pos(lp.pos(), rp.pos()));
	}

	/** Parses a symbol, returning null with messages and not advancing the parser if an error occurs */
	@Override
	public /*@Nullable*/Symbol parseSymbol() throws ParserException {
		return parseSymbol("Expected a symbol here, not a #");
	}

	/** Parses a symbol (but not a reserved word unless the configuration field 'relax' is true), 
	 * returning null with messages if an error occurs; the parser is advanced only if an actual symbol is parsed.  The error message
	 * is given by the argument; it may contain a '#' character that will be replaced by the
	 * kind() of the token actually observed; if the argument is null, no error message is
	 * emitted. */
	public /*@Nullable*/Symbol parseSymbol(/*@Nullable*/String msg) throws ParserException {
		ILexToken token = peekToken();
		if (token instanceof Symbol) {
			if (smtConfig.relax) {
				if (smtConfig.reservedWordsNotCommands.contains(token.toString())) {
					error("A reserved word may not be used as a symbol here: " + token.toString(),token.pos());
					return null;
				}
			} else {
				if (smtConfig.reservedWords.contains(token.toString())) {
					error("A reserved word may not be used as a symbol here: " + token.toString(),token.pos());
					return null;
				}
			}
			token = getToken();
			return (Symbol)token;
		}
		if (!(token instanceof SMTExpr.Error) && msg != null) error(msg.replace("#",token.kind()),token.pos());
		return null;
	}

	/** Parses a symbol or a reserved word, returning null with messages if an error occurs.  The error message
	 * is given by the argument; it may contain a '#' character that will be replaced by the
	 * kind() of the token actually observed. */
	public /*@Nullable*/Symbol parseSymbolOrReservedWord(String msg) throws ParserException {
		ILexToken token = getToken();
		if (token instanceof Symbol) return (Symbol)token;
		if (!(token instanceof SMTExpr.Error)) error(msg.replace("#",token.kind()),token.pos());
		return null;
	}

	/** Parses a literal, returning null with error messages if an error occurs. */
	@Override
	public /*@Nullable*/ILiteral parseLiteral() throws ParserException {
		ILexToken token = getToken();
		if (token instanceof ILiteral) return (ILiteral)token;
		if (!(token instanceof SMTExpr.Error)) error("Expected a literal here, instead of a " + token.kind(),token.pos());
		return null;
	}

	/** Parses a numeral, returning null with error messages if an error occurs; if
	 * the next token is not a numeral, the token is not consumed, */
	@Override
	public /*@Nullable*/INumeral parseNumeral() throws ParserException {
		ILexToken token = getToken(INumeral.class);
		if (token instanceof INumeral) return (INumeral)token;
		if (!(token instanceof SMTExpr.Error)) error("Expected a numeral here, instead of a " + token.kind(),token.pos());
		return null;
	}

	/** Parses a numeral, returning null with the given message if an error occurs; if
	 * the next token is not a numeral, the token is not consumed, */
	public /*@Nullable*/Numeral parseNumeral(String msg) throws ParserException {
		ILexToken token = getToken(INumeral.class);
		if (token instanceof Numeral) return (Numeral)token;
		if (!(token instanceof SMTExpr.Error)) error(msg,token);
		return null;
	}

	/** Parses a decimal, returning null with the given message if an error occurs; if
	 * the next token is not a decimal, the token is not consumed, */
	@Override
	public IDecimal parseDecimal() throws ParserException {
		ILexToken token = getToken(IDecimal.class);
		if (token instanceof IDecimal) return (IDecimal)token;
		if (!(token instanceof SMTExpr.Error)) error("Expected a decimal here, instead of a " + token.kind(),token.pos());
		return null;
	}

	/** Parses a binary literal, returning null with the given message if an error occurs; if
	 * the next token is not a binary literal, the token is not consumed, */
	@Override
	public IBinaryLiteral parseBinary() throws ParserException {
		ILexToken token = getToken(IBinaryLiteral.class);
		if (token instanceof IBinaryLiteral) return (IBinaryLiteral)token;
		if (!(token instanceof SMTExpr.Error)) error("Expected a binary literal here, instead of a " + token.kind(),token.pos());
		return null;
	}

	/** Parses a hex literal, returning null with the given message if an error occurs; if
	 * the next token is not a hex literal, the token is not consumed, */
	@Override
	public IHexLiteral parseHex() throws ParserException {
		ILexToken token = getToken(IHexLiteral.class);
		if (token instanceof IHexLiteral) return (IHexLiteral)token;
		if (!(token instanceof SMTExpr.Error)) error("Expected a hex literal here, instead of a " + token.kind(),token.pos());
		return null;
	}
	
	/** Parses a string literal, returning null with an error message if an error occurs; if
	 * the next token is not a string literal, the token is not consumed, */
	@Override
	public /*@Nullable*/StringLiteral parseStringLiteral() throws ParserException {
		ILexToken token = getToken(IStringLiteral.class);
		if (token instanceof StringLiteral) return (StringLiteral)token;
		if (!(token instanceof SMTExpr.Error)) error("Expected a string literal here, instead of a " + token.kind(),token.pos());
		return null;
	}

	/** Parses a keyword, returning null with an error message if an error occurs; if
	 * the next token is not a keyword, the token is not consumed. */
	@Override
	public /*@Nullable*/Keyword parseKeyword() throws ParserException {
		ILexToken token = getToken(Keyword.class);
		if (token instanceof Keyword) return (Keyword)token;
		if (!(token instanceof SMTExpr.Error)) error("Expected a keyword (beginning with a colon) here, instead of a " + token.kind(),token.pos());
		return null;
	}

	/** Parses a keyword, returning null with messages if an error occurs.  The error message
	 * is given by the argument; it may contain a '#' character that will be replaced by the
	 * kind() of the token actually observed; if
	 * the next token is not a keyword, the token is not consumed. */
	public /*@Nullable*/Keyword parseKeyword(String msg) throws ParserException {
		ILexToken token = getToken(Keyword.class);
		if (token instanceof Keyword) return (Keyword)token;
		if (!(token instanceof SMTExpr.Error)) error(msg.replace("#",token.kind()),token.pos());
		return null;
	}
	
	/** Parses a sort, returning null with error messages if a valid sort is not in the 
	 * next parser tokens.
	 */
	// Can be:
	//		id
	//		( id sort+ )
	// so 
	//		symbol
	//		( _ symbol numeral+ )
	//		( symbol sort+ )
	//		( ( _ symbol numeral+ ) sort+ )
	@Override
	public /*@Nullable*/Sort parseSort(List<ISort.IParameter> parameters) throws ParserException {
		if (!isLP()) {
			Symbol sym = parseSymbol();
			if (sym == null) { getToken(); return null; } // Make sure to make some forward progress
			if (parameters != null) {
				for (ISort.IParameter p: parameters) {
					if (p.identifier().equals(sym)) return (Sort)p;
				}
			}
			return setPos(new Sort.Application(sym),sym.pos());
		} else {
			ILexToken lp = parseLP();
			
			if (!isLP()) {
				ISymbol head = parseSymbolOrReservedWord("Expected a symbol or _ here, not a #");
				if (head == null) { 
					return null; 
				} else if (head.toString().equals("_")) {
					IIdentifier id = parseIdentifierRest(lp);
					if (id == null) { return null; }
					return setPos(new Sort.Application(id),id.pos());
				}
				// else some other symbol

				List<ISort> list = parseSortList(parameters);
				if (list == null) { skipThruRP(); return null; }
				ILexToken rp = parseRP();
				if (rp == null) { skipThruRP(); return null; }
				return setPos(new Sort.Application(head,list),pos(lp.pos(),rp.pos()));
			} else {
				IIdentifier id = parseIdentifier();
				if (id == null) { skipThruRP(); return null; }
				List<ISort> list = parseSortList(parameters);
				if (list == null) { skipThruRP(); return null; }
				ILexToken rp = parseRP();
				if (rp == null) { skipThruRP(); return null; }
				return setPos(new Sort.Application(id,list),pos(lp.pos(),rp.pos()));
			}
		}
	}
	
	/** Parses sequence of sorts up to a right-parenthesis, returning null with error messages
	 * if an error occurs.
	 */
	public /*@Nullable*/List<ISort> parseSortList(List<ISort.IParameter> parameters) throws ParserException {
		List<ISort> list = new LinkedList<ISort>();
		while (!isRP()) {
			if (isEOD()) {
				error("Unexpected end of data while parsing a sort",pos(currentPos()-1,currentPos()));
				return null;
			}
			ISort s = parseSort(parameters);
			if (s != null) list.add(s);
			else { skipThruRP(); return null; }
		}
		return list;
	}

	/** Parse an attribute (keyword with optional value), returning null with error messages
	 * if an error occurs.
	 */
	@Override
	public /*@Nullable*/IAttributeValue parseAttributeValue() throws ParserException {
		if (!isLP()) {
			if (isRP()) {
				smtConfig.log.logError(smtConfig.responseFactory.error("Expected an attribute value here, instead of a )",
						pos(currentPos()-1,currentPos())));
				return null;
			}
			ILexToken t = getToken();
			if (t.isError()) {
				// Already have an error message
				//smtConfig.log.logError(smtConfig.responseFactory.error("Expected an attribute value here, instead of a " + t.kind(),t.pos()));
				return null;
			}
			if (t instanceof IKeyword) {
				smtConfig.log.logError(smtConfig.responseFactory.error("Expected an attribute value here, instead of a " + t.kind(),t.pos()));
				return null;
			}
			if (t instanceof IAttributeValue) {
				IAttributeValue v = (IAttributeValue)t;
				return v;
			} else {
				smtConfig.log.logError(smtConfig.responseFactory.error("Expected an attribute value here, instead of a " + t.kind(),t.pos()));
				return null;
			}
		} else {
			ISexpr value = parseSexpr();
			if (value == null) return null;
			return value;
		}
	}
	
	/** Parse an attribute (keyword with optional value), returning null with error messages
	 * if an error occurs.
	 */
	@Override
	public /*@Nullable*/IExpr.IAttribute<?> parseAttribute() throws ParserException {
		IKeyword keyword = parseKeyword();
		if (keyword == null) return null;
		if (isRP() || isEOD()) {
			return setPos(smtConfig.exprFactory.attribute(keyword),keyword.pos());
		}
		ILexToken n = peekToken();
		if (n instanceof IKeyword) {
			return setPos(smtConfig.exprFactory.attribute(keyword),keyword.pos());
		} else {
			if (!isLP()) {
				ILexToken t = getToken();
				if (t instanceof IAttributeValue) {
					IAttributeValue v = (IAttributeValue)t;
					return setPos(smtConfig.exprFactory.attribute(keyword,v),pos(keyword.pos(),v.pos()));
				} else {
					smtConfig.log.logError(smtConfig.responseFactory.error("The value for the keyword " + 
							smtConfig.defaultPrinter.toString(keyword) + " is not a legal attribute value"));
					return null;
				}
//			} else if (keyword.toString().equals(":pattern")) {
//				parseLP();
//				IExpr value = parseExpr();
//				if (value == null) return null;
//				parseRP();
//				// FIXME - value should be a list of IExpr
//				return setPos(smtConfig.exprFactory.attribute(keyword,value),pos(keyword.pos(),value.pos()));
			} else {
				ISexpr value = parseSexpr();
				if (value == null) return null;
				return setPos(smtConfig.exprFactory.attribute(keyword,value),pos(keyword.pos(),value.pos()));
			}
		}
	}
	
	/** Parse a sequence of attributes (keyword with optional value) terminated by a right parenthesis, returning null with error messages
	 * if an error occurs.
	 */
	public /*@Nullable*/List<IExpr.IAttribute<?>> parseAttributeSequence() throws ParserException {
		List<IExpr.IAttribute<?>> list = new LinkedList<IExpr.IAttribute<?>>();
		while (!isRP()) {
			if (isEOD()) {
				smtConfig.responseFactory.error("Unexpected end of data while parsing attributes",
						pos(currentPos()-1,currentPos()));
				return null;
			}
			IExpr.IAttribute<?> attr = parseAttribute();
			if (attr == null) return null;
			list.add(attr);
		}
		return list;
	}
	
	/** Parses a logic definition (including beginning and ending parentheses, returning null
	 * with error messages if it fails; only part of the checking of the contents is
	 * performed in this call (the rest is done in loadLogic).
	 */
	@Override
	public /*@Nullable*/ ILogic parseLogic() throws ParserException {
		ILexToken lp = parseLP();
		if (lp == null) return null;
		ISymbol sym = parseSymbol();
		if (sym == null || !Utils.LOGIC.equals(sym.value())) {
			error("Faulty logic definition: should have the keyword '" + Utils.LOGIC + "' as the first token",
					sym == null ? pos(lp.pos(),lp.pos()) : sym.pos());
			skipThruRP(); 
			return null;
		}
		ISymbol name = parseSymbol();
		if (name == null) { skipThruRP(); return null; }
		List<IAttribute<?>> attributes = parseAttributeSequence();
		if (attributes == null) { skipThruRP(); return null; }
		ILexToken rp = parseRP();
		if (rp != null) {
			if (!isEOD()) error("Expected the end of file after the right parenthesis",
					pos(lp.pos().charStart(),currentPos()));
		}
		String clazzName = "org.smtlib.logic." + name;
		try {
                        @SuppressWarnings("unchecked")
			Class<? extends ILogic> clazz = (Class<? extends ILogic>)Class.forName(clazzName);
			Constructor<? extends ILogic> con = clazz.getConstructor(ISymbol.class,Collection.class);
			return con.newInstance(name,attributes);
		} catch (ClassNotFoundException e) {
			// OK - no extension class - no language restrictions
		} catch (NoSuchMethodException e) {
			// error - the class must have the right constructor
			error("The constructor for the class " + clazzName + " does not have a constructor with the correct argument types",
					pos(lp.pos().charStart(),currentPos()));
		} catch (IllegalAccessException e) {
			// error - could not create a new instance
			error("An exception occured when instantiating class " + clazzName + ": " + e,
					pos(lp.pos().charStart(),currentPos()));
		} catch (InstantiationException e) {
			// error - could not create a new instance
			error("An exception occured when instantiating class " + clazzName + ": " + e,
					pos(lp.pos().charStart(),currentPos()));
		} catch (InvocationTargetException e) {
			// error - could not create a new instance
			error("An exception occured when instantiating class " + clazzName + ": " + e,
					pos(lp.pos().charStart(),currentPos()));
		}
		return new SMTExpr.Logic(name,attributes);
	}
	
	/** Parses a theory definition (including beginning and ending parentheses, returning null
	 * with error messages if it fails; only part of the checking of the contents is
	 * performed in this call (the rest is done in loadTheory).
	 */
	@Override
	public /*@Nullable*/ ITheory parseTheory() throws ParserException {
		ILexToken lp = parseLP();
		if (lp == null) return null;
		ISymbol sym = parseSymbol();
		if (sym == null || !Utils.THEORY.equals(sym.value())) {
			error("Faulty theory definition: should have the keyword '" + Utils.THEORY + "' as the first token",
					sym == null ? pos(lp.pos(),lp.pos()) : sym.pos());
			skipThruRP(); 
			return null;
		}
		ISymbol name = parseSymbol();
		if (name == null) { skipThruRP(); return null; }
		List<IAttribute<?>> attributes = parseAttributeSequence();
		if (attributes == null) { skipThruRP(); return null; }
		ILexToken rp = parseRP();
		if (rp != null) {
			if (!isEOD()) error("Expected the end of file after the right parenthesis",
					pos(lp.pos().charStart(),currentPos()));
		}
		return new SMTExpr.Theory(name,attributes);
	}
	
	//@Override // FIXME - put this in the interface
	public /*@Nullable*/ IResponse parseResponse(String response) throws ParserException {
		IResponse.IFactory f = smtConfig.responseFactory;
		response = response.trim();
		if ("".equals(response)) return f.empty();
		if ("success".equals(response)) return f.success();
		if ("sat".equals(response)) return f.sat();
		if ("unsat".equals(response)) return f.unsat();
		if ("unknown".equals(response)) return f.unknown();
		if ("unsupported".equals(response)) return f.unsupported();
		if ("true".equals(response)) return smtConfig.exprFactory.symbol("true");
		if ("false".equals(response)) return smtConfig.exprFactory.symbol("false");
		// FIXME - more - iterate over a list?
		
		ISexpr sexpr = parseSexpr();
		if (sexpr instanceof ISexpr.ISeq) {
			List<ISexpr> list = ((ISexpr.ISeq)sexpr).sexprs();
			if (list.size() >= 2) {
				if (list.get(0).toString().equals("error") && list.get(1) instanceof IStringLiteral) {
					return f.error(((IStringLiteral)list.get(1)).value());
				}
				if (list.get(0) instanceof IKeyword) {
					IAttribute<?> attr = smtConfig.exprFactory.attribute((IKeyword)list.get(0),list.get(1));
					return f.get_info_response(attr);
				}
			}
		}
		return sexpr;
		//return f.error("Could not translate response: " + response);
	}
	
	/** Parses a left parenthesis, returning null and emitting an error message
	 *  if there isn't one (and the next token is not consumed)
	 */
	public /*@Nullable*/ILexToken parseLP() throws ParserException {
		ILexToken token = peekToken();
		if (token.kind() == LexToken.LP) return getToken();
		if (!(token instanceof SMTExpr.Error)) error("Expected a left parenthesis here, instead of a " + token.kind(),token.pos());
		return null;
	}
	
	/** Parses a right parenthesis, returning null and emitting an error message
	 *  if there isn't one (and the next token is not consumed)
	 */
	public /*@Nullable*/ILexToken parseRP() throws ParserException {
		ILexToken token = peekToken();
		if (token.kind() == LexToken.RP) return getToken();
		if (!(token instanceof SMTExpr.Error)) error("Expected a right parenthesis here, instead of a " + token.kind(),token.pos());
		return null;
	}
	
	/** Parses a right parenthesis, returning null and emitting an error message
	 *  if there isn't one (and the next token is not consumed); the error message
	 *  is the argument, with any '# character replaced by the kind() of the actual next
	 *  token.
	 */
	public /*@Nullable*/ILexToken parseRP(String msg) throws ParserException {
		ILexToken token = peekToken();
		if (token.kind() == LexToken.RP) return getToken();
		if (!(token instanceof SMTExpr.Error)) error(msg,token);
		return null;
	}
	
	/** Emits an error message consisting of the given message string and position. */
	public IResponse.IError error(String msg, /*@Nullable*//*@ReadOnly*/IPos pos) {
		return smtConfig.log.logError(smtConfig.responseFactory.error(msg,pos));
	}
	
	/** Emits an error message consisting of the given message string with any '#' 
	 * character in the string replaced by the kind() of the second argument; the position
	 * of the error is the position of the given token. */
	public void error(String msg, ILexToken token) {
		if (token.kind().equals("error")) return; // FIXME better comparison? document? no string constant?
		String description = token.kind();
		if (description == LexToken.LP) description = "sequence";
		smtConfig.log.logError(smtConfig.responseFactory.error(msg.replace("#",description),token.pos()));
	}

	
	
}
