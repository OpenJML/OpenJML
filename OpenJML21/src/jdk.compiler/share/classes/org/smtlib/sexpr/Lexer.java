/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.sexpr;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.smtlib.IParser.AbortParseException;
import org.smtlib.IParser.ParserException;
import org.smtlib.IParser.SyntaxException;
import org.smtlib.*;
import org.smtlib.IPos.IPosable;
import org.smtlib.impl.*;
import org.smtlib.impl.SMTExpr.BinaryLiteral;
import org.smtlib.impl.SMTExpr.Decimal;
import org.smtlib.impl.SMTExpr.HexLiteral;
import org.smtlib.impl.SMTExpr.Keyword;
import org.smtlib.impl.SMTExpr.Numeral;
import org.smtlib.impl.SMTExpr.StringLiteral;
import org.smtlib.impl.SMTExpr.Symbol;

/** Converts character sequences (from ISource) into tokens, presuming the standard SMT-LIBv2 concrete syntax.
 * It is intended to be used as a base class for a parser, but could also be used by inclusion. */
public class Lexer {

	/** An interface used for punctuation tokens that can be retrieved from the parser input.*/
	public static interface IPLexToken extends ILexToken {
		public final static String RP = ")".intern();
		public final static String LP = "(".intern();
		public final static String EMPTY = "".intern();
		@Override /*@ReadOnly*/ IPos pos();
		@Override String kind();
	}
	
	/** Skips the rest of the current line, resetting the matcher to point to the line termination character */
	public void abortLine() {
		int i = matcher.regionStart();
		char c;
		while ((c=csr.charAt(i))!= '\r' && c != '\n') ++i;
		matcher.region(i,csr.length());
	}
	
	/** Creates a Lexer using an SMT configuration object and a source for
	 * characters
	 */
	public Lexer(SMT.Configuration smtConfig, ISource src) {
		this.smtConfig = smtConfig;
		this.source = src;
		if (src != null) {
			this.csr = src.chars();
			this.matcher = combined.matcher(this.csr);
		} else {
			this.csr = null;
			this.matcher = null;
		}
	}

	/** A lexical token class for single punctuation characters. */
	protected class LexToken implements IPLexToken {
		private String chars;
		private IPos pos;
		@Override
		public IPos pos() { return pos; }
		public LexToken(String s, int cp) { // FIXME - factory? or Lexer.pos?
			chars = s.intern(); 
			pos = new Pos(cp,cp+1,source); 
		} 
		@Override
		public boolean isError() { return false; }
		@Override
		public String toString() { return chars; }
		@Override
		public String kind() { return chars; }
	}
	
	/** Creates a lexical token for a left parenthesis at the given position */
	public LexToken LP(int cpos) { return new LexToken(IPLexToken.LP,cpos); }
	/** Creates a lexical token for a right parenthesis at the given position */
	public LexToken RP(int cpos) { return new LexToken(IPLexToken.RP,cpos); }
	/** Creates a lexical token for a end-of-data at the given position */
	public LexToken EOD(int cpos) { return new EOD(cpos); }

	private static String EOD_KIND = "eod".intern();

	/** A class that represents a lexical token corresponding to the end of input */
	private class EOD extends LexToken implements IPLexToken {
		
		
		/** Creates an instance of an end-of-data token at the given character position */
		public EOD(int cpos) {
			super(EMPTY,cpos);
		}
		
		@Override
		public String kind() {
			return EOD_KIND;
		}
	}

	/** A handle to the parent SMTConfig object, in order to see command-line options
	 * etc. that are fields of smtConfig */
	final private SMT.Configuration smtConfig;

	/** The Matcher used to do lexical scanning */
	final protected Matcher matcher;
	
	/** Any comment text found before the current token */
	public String prefixCommentText;
	
	/** The source of input used in this lexer; typically a different
	 * lexer object will be used for each source (e.g. different file, string,
	 * port, etc.) of input data.
	 */
	final private ISource source;

	/** The source of input used in this lexer; typically a different
	 * lexer object will be used for each source (e.g. different file, string,
	 * port, etc.) of input data.
	 */
	final public ISource source() { return source; }
	
	/** The CharSequence corresponding to the source object */
	final protected CharSequence csr;
	
	// These are regular expressions (of the sort used by Pattern) for 
	// scanning the input text into the SMT-LIB concrete syntax tokens.
	// Note that backslashes are doubled because Java uses them as escape
	// characters; they are also used by Pattern as escape characters.
	
	// The implementation uses Pattern and Matcher as an easily implemented syntax scanner.
	// However, it may not be very efficient - for example, the regex for 
	// a string does a stack overflow for long strings.  That is why the 
	// implementation below is special for that case.

	/** Pattern regular expression for SMT-LIB whitespace */
	private final static String rgxWhiteSpace = "[\\p{Space}]+"; // includes line termination
	/** Pattern regular expression for SMT-LIB comment */
	private final static String rgxComment = ";.*";              // be sure dot does not include line termination
	/** Pattern regular expression for SMT-LIB numeral */
	private final static String rgxNumeral = "0|[1-9][0-9]*";
	/** Pattern regular expression for an invalid SMT-LIB numeral or decimal (that has leading zeros) */
	private final static String rgxLeadingZero = "0+(?:0|[1-9][0-9]*)(?:\\.[0-9]+)?";
	/** Pattern regular expression for SMT-LIB binary literal */
	private final static String rgxBinary = "#b([01]+)";
	/** Pattern regular expression for SMT-LIB hex literal */
	private final static String rgxHex = "#x([0-9a-fA-F]+)";
	/** Pattern regular expression for SMT-LIB string (except for the enclosing quotes) */
	// Not actually used now - instead we match the first " with the Matcher and then match the rest by hand
	private final static String rgxStringLiteral = "\"(?:[!#-\\[\\]-~ \t\r\n]|\\\\\\\\|\\\\\")*\"";
	/** Pattern regular expression for an invalid SMT-LIB string (presuming the valid string does not match) */
	// Unterminated or otherwise invalid strings are now found by the hand-coded string matcher
	private final static String rgxInvalidString = "(?:[!#-~ \t\r\n])*";
	/** Pattern regular expression for SMT-LIB decimal literal */
	private final static String rgxDecimal = "(?:0|[1-9][0-9]*)(?:\\.[0-9]+)?"; // the use of ( is non-capturing
	/** Pattern regular expression for SMT-LIB symbol (without bars) */
	private final static String rgxSymbol = "[a-zA-Z_~!@$%^&*+=<>.?/\\-][0-9a-zA-Z_~!@$%^&*+=<>.?/\\-]*";
	/** Pattern regular expression for SMT-LIB symbol enclosed in bars */
	private final static String rgxQuotedSymbol = "\\|[0-9a-zA-Z_~!@$%^&*+=<>.?/\"'(),:;{}#`\\[\\] \t\r\n\\-]*\\|";
	/** Pattern regular expression for invalid SMT-LIB unterminated bar-symbol */
	private final static String rgxNonTermQuotedSymbol = "\\|[0-9a-zA-Z_~!@$%^&*+=<>.?/\"'(),:;{}#`\\[\\] \t\r\n\\-]*";
	/** Pattern regular expression for SMT-LIB keyword (colon beginning) */
	private final static String rgxKeyword = ":[0-9a-zA-Z_~!@$%^&*+=<>.?/\\-]+";
	/** Pattern regular expression for SMT-LIB sequence of non-white space */
	private final static String rgxAnyNonWS = "[\\S&&[^;\\(\\)]][\\S&&[^;\\(\\)]]*"; // Any sequence of non-whitespace, not beginning with ( ) ;
	/** Pattern regular expression for detecting the end of input */
	private final static String rgxEndOfInput = "\\z|\\031|\\004"; // FIXME - use CharSequenceReader.endChar
	/** Pattern regular expression for checking that a sequence of digits is not followed by other non-white space, non-comment, non-parenthesis characters */
	private final static String trailer = "(?:[\\s\\(\\);]|$)";

	/** 
	 * This composite regular expression matches tokens in the SMTLIB input.  It first gobbles up any
	 * whitespace and comments, and then gets one instance of a token.  For the most part, the
	 * fact the + and * are greedy ensures that tokens are not prematurely ended.
	 * But, there are three items to note:
	 * 1) when scanning for Numerals and Decimals, the scanner has to be sure that the token
	 * is followed by whitespace, parentheses or a comment.  It is not allowed to have 
	 * other characters immediately after a numeral.  But the characters that follow are not part
	 * of the Numeral or Decimal and have to be rescanned.
	 * 2) It appears that in interpreting the regular expression, if two alternatives
	 * match, it is the textually earlier one in the regex that is reported as matching
	 * via matcher.group(int).  Thus we include a catch-all error token as the last element of
	 * the set of alternatives, so that there is always something that matches.
	 * 3) The regex for a SMT-LIB string literal is accurate, but causes stack overflow on 
	 * long (>~1000 characters) strings.  One would not think that there was a recursive call
	 * for each character, but it appears that there is.  It may be that a redesign of the regex 
	 * would help, but instead, I just changed the regex to match the opening quote - then we
	 * scan the string by hand and adjust the matcher position afterwards.
	 */
	public static Pattern combined = Pattern.compile(
			"((?:" + rgxWhiteSpace + "|" + rgxComment + ")*)((" // first skip all whitespace and comments
				+ "\\(" + ")|("        	// group 3: left parenthesis
				+ "\\)" + ")|("			// group 4: right parenthesis
				+ rgxNumeral + ")" + trailer + "|("	// group 5: numeral
			    + rgxSymbol  + ")|(" 	// group 6: symbol
			    //+ rgxStringLiteral + ")|(" 	// group 7: string literal
			    + "\""        + ")|(" 	// group 7: string  - just matches the opening character - see code below and comment above
			    + rgxQuotedSymbol + ")|("	// group 8: quoted symbol
			    + rgxKeyword + ")|("	// group 9: keyword
				+ rgxDecimal + ")" + trailer + "|("	// group 10: decimal
				+ rgxBinary  + ")" + trailer + "|("                 // group 11,12: binary literal
				+ rgxHex  + ")" + trailer + "|("                    // group 13,14: hex literal
				+ rgxEndOfInput + ")|("				// group 15: end of input
			    + rgxNonTermQuotedSymbol + ")|("	// group 16: error - non terminated quoted symbol
			    + rgxLeadingZero + ")" + trailer + "|"	// group 17: invalid leading zero
			    + "\"(" + rgxInvalidString + ")\"" + "|("		// group 18: invalid string // NO LONGER MATCHES SINCE CHANGING THE STRING MATCHING
			    + "\\030" + ")|("		// group 19: the control-X character to kill input
			    + rgxAnyNonWS + ")"		// group 20: error symbol
			    + "|([ \t\r\n]+)"				// group 21: stop-gap whitespace
		+   ")"  );
	
	/** A pattern to skip up to the end of the line */
	final public static Pattern skipThroughEndOfLine = Pattern.compile(".*");
	
	// We need lexical tokens that inherit from ILexToken so they can be returned uniformly from
	// getToken(); they also need to actually be the tokens used in the Parser (i.e. from org.smtlib.impl.*);
	// and they are S-expression tokens in this concrete syntax.  So we do this inheritance structure.
	// It works fine with one drawback: within the lexer we are directly allocating (with 'new') instances
	// of these tokens (as well as the punctuation tokens), rather than using a factory; we cannot readily
	// substitute a different set of Parser token classes.
	// TODO: Devise a new lexer factory for this purpose.
	
	private static class LexSymbol extends Symbol implements ILexToken, ISexpr.IToken<String> {
		public LexSymbol(String n) { super(n); }
	}

	private static class LexNumeral extends Numeral implements ILexToken, ISexpr.IToken<BigInteger> {
		public LexNumeral(BigInteger n) { super(n); }
	}

	private static class LexDecimal extends Decimal implements ILexToken, ISexpr.IToken<BigDecimal> {
		public LexDecimal(BigDecimal n) { super(n); }
	}

	private static class LexStringLiteral extends StringLiteral implements ILexToken, ISexpr.IToken<String> {
		public LexStringLiteral(String n, boolean quoted) { super(n,quoted); }
	}

	private static class LexBinaryLiteral extends BinaryLiteral implements ILexToken, ISexpr.IToken<String> {
		public LexBinaryLiteral(String n) { super(n); }
	}

	private static class LexHexLiteral extends HexLiteral implements ILexToken, ISexpr.IToken<String> {
		public LexHexLiteral(String n) { super(n); }
	}

	private static class LexKeyword extends Keyword implements ILexToken, ISexpr.IToken<String> {
		public LexKeyword(String n) { super(n); }

		@Override
		public boolean isOK() { return false; }

		@Override
		public boolean isError() { return false; }
	}

	private class LexError extends org.smtlib.impl.SMTExpr.Error implements ILexToken, ISexpr.IToken<String> {
		public LexError(String n) { super(n); }

		@Override
		public boolean isOK() { return false; }

		@Override
		public boolean isError() { return true; }
		
		/** For debugging only - not general printing */
		@Override
		public String toString() { return "Error: " + smtConfig.utils.quote(value()); }
	}

	/** A static helper method that sets the position of an AST node, but returns the same type */
	protected static <T extends IPosable> T setPos(T t, IPos pos) { t.setPos(pos); return t; }
	
	/** Holds the lookahead token - should only be read and written by peekToken/getToken;
	 * value is null if we have not gotten the next lexical token yet. */
	private /*@Nullable*/ ILexToken nextToken = null;
	
	/** Returns the next lexical token without consuming it;
	 * a subsequent call to getToken will return the same token.
	 * @throws ParserException if something bad or an intentional abort happens
	 */
	public ILexToken peekToken() throws ParserException {
		if (nextToken == null) nextToken = getToken();
		return nextToken;
	}
	
	/** Returns the next lexical token; if the token returned matches the given
	 * class (or is a subclass), then the scanner is advanced; if the token does
	 * not match, the scanner is not advanced.
	 * @throws ParserException if something bad or an intentional abort happens
	 */
	public ILexToken getToken(Class<?> clazz) throws ParserException {
		ILexToken token = peekToken();
		if (clazz.isAssignableFrom(token.getClass())) {
			return getToken();
		}
		return token;
	}
	
	/** Returns the position of the next character to be read */
	public int currentPos() {
		return matcher.regionStart();
	}
	
	/** Returns true if the next token is the end-of-data */
	public boolean isEOD() throws ParserException {
		return peekToken().kind() == EOD_KIND;
	}
	
	
	/** Reads and discards tokens until an unmatched right parenthesis or end-of-data is read
	 * @return the position of the right parenthesis or end-of-data
	 */
	public IPos skipThruRP() throws ParserException {
		int n = 1;
		ILexToken t;
		while (!isEOD()) {
			t = getToken();
			if (!(t instanceof LexToken)) continue;
			String s = ((LexToken)t).chars;
			if (s == IPLexToken.LP) ++n;
			if (s == IPLexToken.RP) { --n; if (n == 0) return t.pos(); }
		}
		return getToken().pos(); 
	}
	
	/** Returns true if the next token is a left parenthesis (without consuming it) */
	public boolean isLP() throws ParserException {
		ILexToken token = peekToken();
		return (token.kind() == LexToken.LP);
	}

	/** Returns true if the next token is a right parenthesis (without consuming it) */
	public boolean isRP() throws ParserException {
		ILexToken token = peekToken();
		return (token.kind() == LexToken.RP);
	}
	
	/** Creates an IPos object with the given start and end and the source for this Lexer */
	public IPos pos(int start, int end) {
		return new Pos(start,end,source);
	}
	
	/** Returns the first token found in the given text */
	public ILexToken getToken(String text)  throws ParserException {
		if (!text.isEmpty() && text.charAt(0) == '"') {
			return new LexStringLiteral(text,true);
		}
		Matcher matcher = combined.matcher(text);
		return getToken(matcher);
	}
	
	/** Returns the next lexical token, advancing the scanner.
	 * @throws ParserException if something bad or an intentional abort happens
	 */
	public ILexToken getToken() throws ParserException {
		ILexToken token = null;
		if (nextToken != null) {
			token = nextToken;
			nextToken = null;
			return token;
		}
		return getToken(matcher);
	}
	
	/** Returns the next token found in the given matcher, advancing the matcher */
	protected ILexToken getToken(Matcher matcher) throws ParserException {
		ILexToken token = null;
		if (matcher.lookingAt()) {
			prefixCommentText = null;
			if (matcher.groupCount() >= 1 && matcher.end(1) != matcher.start(1)) {
				prefixCommentText = matcher.group(1);
				if (prefixCommentText.startsWith("\n")) prefixCommentText = prefixCommentText.substring(1);
				else if (prefixCommentText.startsWith("\r\n")) prefixCommentText = prefixCommentText.substring(2);
			}
			int end = matcher.end(2);
			//			System.out.println("MATCHED RANGE " + matcher.start() + " " + matcher.end() + " !" + matcher.group() + "!");
			//			for (int i=3; i<=matcher.groupCount(); i++) {
			//				if (matcher.group(i) != null) { 
			//					System.out.println("MATCHED " + i + " RANGE " + matcher.start(i) + " " + matcher.end(i) + " !" + matcher.group(i) + "!" + (int)matcher.group(i).charAt(0));
			//				}
			//			}
			int k;
			IPos pos;
			String matched = null;
			if ((matched = matcher.group(k=3)) != null) {
				token = this.LP(matcher.start(k));
			} else if ((matched = matcher.group(k=4)) != null) {
				token = this.RP(matcher.start(k));
			} else if ((matched = matcher.group(k=5)) != null) { // numeral
				pos = pos(matcher.start(k),matcher.end(k));
				//token = factory.numeral(matched,pos);
				token = setPos(new LexNumeral(new BigInteger(matched)),pos);
				end = matcher.end(k);
			} else if ((matched = matcher.group(k=6)) != null) { // simple symbol
				pos = pos(matcher.start(k),matcher.end(k));
				//token = factory.symbol(matched,pos); 
				token = setPos(new LexSymbol(matched),pos);
			} else if ((matched = matcher.group(k=8)) != null) { // bar-quoted symbol
				pos = pos(matcher.start(k),matcher.end(k));
				//token = factory.symbol(matched,pos);
				token = setPos(new LexSymbol(matched),pos);
			} else if ((matched = matcher.group(k=7)) != null) { // string 
				// The match is just to the initial quote
				int begin = matcher.start(k); // position of the initial quote
				int p = begin;
				try {
					if (smtConfig.isVersion(SMT.Configuration.SMTLIB.V25)) { // Version 2.5ff
						while (true) {
							p++;
							char c = csr.charAt(p);
							if (c == '"') {
								if (p+1 < csr.length() && csr.charAt(p+1) == '"') {
									p++;
								} else {
									end = p+1;
									matched = csr.subSequence(begin,end).toString();
									pos = pos(begin,end);
									token = setPos(new LexStringLiteral(matched,true),pos);
									break;
								}
							} else {
								if (c >= ' ' && c <= '~') continue;
								if (c == '\t' || c == '\r' || c == '\n') continue;
								if (c >= 128) continue; // Version 2.5, but only within comments, string literals, quoted symbols
								if (c == 25) {
									end = p;
									matched = csr.subSequence(begin,end).toString();
									pos = pos(begin,end);
									smtConfig.log.logError(smtConfig.responseFactory.error("String literal is not terminated: " + matched,pos));
									token = setPos(new LexError(matched),pos);
									break; // End of data - no closing right paren
								}
								smtConfig.log.logError(smtConfig.responseFactory.error("Invalid character: ASCII(decimal) = " + (int)c,
										pos(p,p+1)));
								continue;
							}
						}
					} else if (SMT.Configuration.SMTLIB.V20.toString().equals(SMT.Configuration.smtlib)) { // Version 2.0
						while (true) {
							p++;
							char c = csr.charAt(p);
							if (c == '\\') {
								c = csr.charAt(++p);
								// \\ is translated to \ and \" to "
								// \x for anything else is just \x
								//								if (c == '\\' || c == '"') {
								//									continue;
								//								} else {
								//									smtConfig.log.logError(smtConfig.responseFactory.error("Invalid escape sequence " + (char)c + " (decimal ASCII = " + (int)c + ")",
								//											pos(p,p+1)));
								//								}
							} else if (c == '"') {
								end = p+1;
								matched = csr.subSequence(begin,end).toString();
								pos = pos(begin,end);
								token = setPos(new LexStringLiteral(matched,true),pos);
								break;
							} else {
								if (c >= ' ' && c <= '~') continue;
								if (c == '\t' || c == '\r' || c == '\n') continue;
								if (c == 25) {
									end = p;
									matched = csr.subSequence(begin,end).toString();
									pos = pos(begin,end);
									smtConfig.log.logError(smtConfig.responseFactory.error("String literal is not terminated: " + matched,pos));
									token = setPos(new LexError(matched),pos);
									break; // End of data - no closing right paren
								}
								smtConfig.log.logError(smtConfig.responseFactory.error("Invalid character: ASCII(decimal) = " + (int)c,
										pos(p,p+1)));
								continue;
							}
						}
					}
				} catch (IndexOutOfBoundsException e) {
					// If the CharSequence does not expand itself and does not terminate 
					// itself with an end of data character, and does not end with a
					// quote character, we get this exception
					end = p;
					matched = csr.subSequence(begin,end).toString();
					pos = pos(begin,end);
					token = setPos(new LexError(matched),pos);
					smtConfig.log.logError(smtConfig.responseFactory.error("String literal is not terminated: " + matched,token.pos()));
				}
			} else if ((matched = matcher.group(k=9)) != null) { // colon-initiated keyword
				pos = pos(matcher.start(k),matcher.end(k));
				//token = factory.keyword(matched,pos);
				token = setPos(new LexKeyword(matched),pos);
			} else if ((matched = matcher.group(k=10)) != null) { // decimal
				pos = pos(matcher.start(k),matcher.end(k));
				//token = factory.decimal(matched,pos);   // FIXME - use a factory everywhere?
				token = setPos(new LexDecimal(new BigDecimal(matched)),pos);
				end = matcher.end(k);
			} else if ((matched = matcher.group(k=11)) != null) {
				pos = pos(matcher.start(k),matcher.end(k));
				token = setPos(new LexBinaryLiteral(matcher.group(k+1)),pos);
				end = matcher.end(k);
			} else if ((matched = matcher.group(k=13)) != null) {
				pos = pos(matcher.start(k),matcher.end(k));
				token = setPos(new LexHexLiteral(matcher.group(k+1)),pos);
				end = matcher.end(k);
			} else if ((matched = matcher.group(k=15)) != null) {
				pos = pos(matcher.start(k),matcher.end(k));
				token = this.EOD(matcher.start(k));
			} else if ((matched = matcher.group(k=16)) != null) {
				pos = pos(matcher.start(k),matcher.end(k));
				//token = factory.error(matched,pos);
				token = setPos(new LexError("Bar(|)-enclosed symbol is not terminated: " + matched),pos);
				smtConfig.log.logError(smtConfig.responseFactory.error("Bar(|)-enclosed symbol is not terminated: " + matched,token.pos()));
//				matcher.region(end,csr.length());
//				throw new SyntaxException("Invalid token: " + matched,token.pos());
			} else if ((matched = matcher.group(k=17)) != null) {
				pos = pos(matcher.start(k),matcher.end(k));
				//token = factory.error(matched,pos);
				String msg = "Incorrect format for a number - no leading zeros allowed: ";
				token = setPos(new LexError(msg + matched),pos);
				smtConfig.log.logError(smtConfig.responseFactory.error(msg + matched,token.pos()));
				end = matcher.end(k);
//				matcher.region(end,csr.length());
//				throw new SyntaxException("Leading zeros are not allowed: " + matched,token.pos());
			} else if ((matched = matcher.group(k=18)) != null) {
				// This case no longer matches since we made a special case of string matching.
				pos = pos(matcher.start(k),matcher.end(k));
				//token = factory.error(matched,pos);
				token = setPos(new LexError(matched),pos);
				//smtConfig.log.logError(smtConfig.responseFactory.error("Invalid string: " + matched));
				matcher.region(end,csr.length());
				// FIXME - decide whether to throw exceptions or emit error messages and error tokens
				throw new SyntaxException(("Invalid string: " + matched),token.pos());
			} else if ((matched = matcher.group(k=19)) != null) {
				//System.out.println("Killed");
				matcher.region(end,csr.length());
				throw new AbortParseException();
			} else if ((matched = matcher.group(k=20)) != null) {
				pos = pos(matcher.start(k),matcher.end(k));
				//token = factory.error(matched,pos);
				if (matched.charAt(0) < ' ') matched = "(ASCII char " + (int)matched.charAt(0) + " (decimal))";
				token = setPos(new LexError("Invalid token: " + matched),pos);
				smtConfig.log.logError(smtConfig.responseFactory.error("Invalid token: " + matched,
						pos));
//				matcher.region(end,csr.length());
//				throw new SyntaxException("Invalid token: " + matched,token.pos());
				//SMT.out.println(smtConfig.responseFactory.error("Invalid token: " + matched));
			} else if ((matched = matcher.group(k=21)) != null) {
				// FIXME - This should never happen either - it is a stopgap hack, because
				// with whitespace at the very beginning of a file, the whitespace detector is not finding it
				matcher.region(end,csr.length());
				return getToken();
			} else {
				// Nothing matched - this should not have happened.
				// lookingAt should not have returned true if no group matched
				// Check that all alternatives are represented in the cases above
				int b = matcher.regionStart();
				int e = matcher.regionEnd();
				String s = csr.subSequence(b,e > b+100? b+100: e).toString();
				if (matcher.group(1) != null) end = matcher.end(1);
				else end = matcher.end();
				matcher.region(end > b? end: b+1,csr.length());
				//String group = matcher.group();
				throw new SMT.InternalException("Failed to report which regular expression matched: "
						+ " " + b + " " + e + " " + s);
			}
			if (csr != null) matcher.region(end,csr.length());
		} else {
			// FIXME - there is a problem if we have spaces at the very beginning of a file, prior to the LP
			// the matcher does not match???
			int b = matcher.regionStart();
			int e = matcher.regionEnd();
			matcher.region(b+1,e);
			return getToken();
			// Nothing matched - this should not have happened.
			// There is an error in the regular expression, since it is not even
			// reporting an error token.
//			int n = matcher.groupCount();
//			String gr = matcher.group(2);
//			gr = matcher.group(1);
//			gr = matcher.group(0);
//			String s = csr.subSequence(b,e>b+100?b+100:e).toString();
//			throw new SMT.InternalException("Failed to report any match: something is wrong with the regular expression used for parsing "
//					+ matcher.regionStart() + " " + matcher.regionEnd() + " " + s);
		}
		return token;
	}
	

}
