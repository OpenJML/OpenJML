/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.parser;

import java.nio.CharBuffer;
import java.util.Set;

import org.jmlspecs.openjml.Extensions;
import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlOptions;
import org.jmlspecs.openjml.ext.LineAnnotationClauses.ExceptionLineAnnotation;
import org.jmlspecs.openjml.ext.MethodSimpleClauseExtensions;
import org.jmlspecs.openjml.ext.MiscExtensions;
import org.jmlspecs.openjml.ext.Operators;
import org.jmlspecs.openjml.ext.SingletonExpressions;

import com.sun.tools.javac.parser.Tokens.Comment.CommentStyle;
import com.sun.tools.javac.resources.CompilerProperties.Errors;
import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.DiagnosticSource;
import com.sun.tools.javac.util.LayoutCharacters;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;

/* NOTE: (FIXME Review this now that Tokenizer has been refactored out) 
 * - oddities in the Scanner class
 It seems that if the first character of a token is unicode, then pos is
 set to be the last character of that initial unicode sequence.
 I don't think the endPos value is set correctly when a unicode is read;
 endPos appears to be the end of the character after the token characters,
 which is not correct if the succeeding token is a unicode character

 Recovery after an ERROR token that is a \ seems to consume extra characters

 I'm not sure the behavior of unicode with multiple backslashes is correct
 */

// FIXME - turn off jml when an exception happens?
/**
 * This class is an extension of the JDK scanner that scans JML constructs as
 * well. Note that it relies on some fields and methods of Scanner being
 * protected that are not declared protected in the current version of OpenJDK.
 * No other changes to Scanner are made, which does require a number of complicating
 * workarounds in this code. In retrospect, a much simpler JML scanner could have
 * been produced by being more surgical with JavaScanner; but given the goal to 
 * be minimally invasive, this is what we have.
 * 
 * @author David Cok
 */
public class JmlTokenizer extends JavadocTokenizer {

    /** The compilation context with which this instance was created */
    public Context         context;

    /** A temporary reference to the instance of the nowarn collector for the context. */
    /*@ non_null */ public Nowarns nowarns;
    
    /** Collects line annotations */
    public java.util.List<ExceptionLineAnnotation> lineAnnotations = new java.util.LinkedList<>();

    /**
     * A flag that, when true, causes all JML comments to be ignored; it is
     * set on construction according to a command-line option.
     */
    protected boolean       noJML      = false;

    /** Set to true internally while the scanner is within a JML comment */
    protected boolean       jml        = false;

    /** A mode of the scanner that determines whether end of jml comment tokens are returned */
    public boolean returnEndOfCommentTokens = true;
    
    /**
     * The style of comment, either CommentStyle.LINE or
     * CommentStyle.BLOCK, set prior to the scanner calling processComment()
     */
    /*@nullable*/ protected CommentStyle  jmlcommentstyle;

    /** Valid after nextToken() and contains token it read if it is a JML token
     * and null if the next token is a Java token */
    /*@nullable*/ public JmlTokenKind   jmlTokenKind;

    /** Valid after nextToken() and contains the token it read */
	/*@nullable*/ public IJmlClauseKind jmlTokenClauseKind;

    /**
     * Creates a new tokenizer, for JML and Java tokens.<P>

     * The last character in the input array may be overwritten with an EOI character; if you
     * control the size of the input array, make it at least one character larger than necessary, 
     * to avoid the overwriting or reallocating and copying the array.

     * @param fac The factory generating the scanner
     * @param input The character buffer to scan
     * @param inputLength The number of characters to scan
     */
    //@ requires inputLength <= input.length;
    protected JmlTokenizer(JmlScanner.JmlFactory fac, char[] input, int inputLength) {
        super(fac, input, inputLength);
        context = fac.context;
        nowarns = Nowarns.instance(context);
    }
    
    /**
     * Creates a new tokenizer, for JML tokens.<P>
     * 
     * @param fac The factory generating the scanner
     * @param buffer The character buffer to scan
     */
    // @ requires fac != null && buffer != null;
    protected JmlTokenizer(JmlScanner.JmlFactory fac, CharBuffer buffer) {
        super(fac, buffer);
        context = fac.context;
        nowarns = Nowarns.instance(context);
    }
    
    /** True if the tokenizer is in a JML comment, false otherwise */
    public boolean jml() {
        return jml;
    }
    
    /** The current set of conditional keys used by the tokenizer.
     */
    public Set<String> keys() {
        return JmlOptions.instance(context).commentKeys;
    }
    
    /** Internal use only -- when non-negative, tokens in Java code are skipped, and is the position of the beginning of the skip */
    protected int skippingTokens = -1;
    
    
    // This is called whenever the Java (superclass) scanner has scanned a whole
    // comment. We override it in order to handle JML comments specially. The
    // overridden method returns and proceeds immediately to scan for the 
    // next Java token after the comment.
    // Here if the comment is indeed a JML comment, we reset the scanner to the
    // beginning of the comment, set jml to true, and let the scanner proceed
    // to scan the contents of the comment.
    // The comment is the content of buffer[] from pos to endPos, exclusive. 
    // The comment includes the terminating */, but not the terminating newline.
    // endPos may be equal to buffer.length
    @Override
    protected Tokens.Comment processComment(int pos, int endPos, CommentStyle style) {
        //if (org.jmlspecs.openjml.Main.useJML) System.out.println("COMMENT " + pos + " " + endPos + String.valueOf(buffer,pos,endPos-pos));

        // The inclusive range pos to endPos-1 does include the opening and closing
        // comment characters.
        // It does not include line ending for line comments, so
        // an empty line comment can be just two characters.
        if (noJML || style == CommentStyle.JAVADOC || endPos-pos <= 2) {
            return super.processComment(pos,endPos,style);
        }
        
        
        
        // Skip the first two characters (the comment marker))
        int commentStart = pos;
        reset(pos);
        next();
        next();
        
        int ch = get(); // The @ or #, or a + or - if there are keys, or something else if it is not a JML comment
        int plusPosition = position();

        boolean someplus = false; // true when at least one + key has been read
        boolean foundplus = false; // true when a + key that is in the list of enabled keys has been read
        while ((ch=get()) != '@') { // On the first iteration, this is the same ch as above.
            if (ch != '+' && ch != '-') {
                // Not a valid JML comment (ch is not @ or + or -), so just return
                // Restart after the comment we are currently processing
                reset(endPos);
                return super.processComment(pos, endPos, style);
            }
            
            boolean isplus = ch == '+';

            ch = next();
            if (!Character.isLetter(ch)) {
               	if (ch == '@') {
                    Utils.instance(context).warning(plusPosition,"jml.message",
                    		"Annotation comments beginning with +@ or -@ are no longer supported; use keys instead");

            	}
            	reset(endPos);
                return super.processComment(pos, endPos, style);
            }
            if (ch == '@') {
                // Old -style //+@ or //-@ comments
                
                if (Options.instance(context).isSet("-Xlint:deprecation")) {
                    Utils.instance(context).warning(commentStart,plusPosition, position(),
                    		"jml.deprecated.conditional.annotation");
                }

                // To be backward compatible at the moment,
                // ignore for //-@, process the comment if //+@
                if (isplus) break;
                reset(endPos);
                return super.processComment(pos, endPos, style);
            }
            if (isplus) someplus = true;
            // We might call nextToken here and look for an identifier,
            // but that could be a recursive call of nextToken, which might
            // be dangerous, so we use scanIdent instead
            if (!Character.isJavaIdentifierStart(ch)) {
                // Not a valid JML comment - just return
                // Restart after the comment
                reset(endPos);
                return super.processComment(pos, endPos, style);
            }
            // Check for keys
            scanIdent(); // Only valid if ch is isJavaIdentifierStart; sets 'name'
            sb.setLength(0); // See the use of sb in JavaTokenizer - if sb is not reset, then the
                        // next identifier is appended to the key
            String key = name.toString(); // the identifier just scanned
            if (keys().contains(key)) {
                if (isplus) foundplus = true;
                else {
                    // negative key found - return - ignore JML comment
                    reset(endPos);
                    return super.processComment(pos, endPos, style);
                }
            }
        }
        if (!foundplus && someplus) {
            // There were plus keys but not the key we were looking for, so ignore JML comment
            // Restart after the comment
            cleanup(commentStart, endPos, style);
            return super.processComment(pos, endPos, style);
        }

        // Either there were no optional keys or we found the right ones, so continue to process the comment
        while (accept('@')) {} // Gobble up all leading @s
        int p = position();
        if (accept('#')) {
        	// Inlined Java code
        	// If the # is followed by -, then lines are skipped until another # comment
        	// If the # is followed by white space, the content is tokenized
            if (accept('-')) {
            	if (skippingTokens>=0) Utils.instance(context).warning(p,"jml.message","Already skipping tokens");
            	skippingTokens = p;
                reset(endPos);
                return null; // Ignore rest of line, keep tokenizing, but skip tokens 
            }
            if (isOneOf(' ','\t') || isOneOf('\n','\r')) {
                skippingTokens = -1; // Stop skipping tokens
                return null; // Tokenize rest of comment
            }
            // A non-JML comment
            reset(endPos);
            return super.processComment(pos, endPos, style);
        }
        if (!(isOneOf(' ','\t','{') || (style == CommentStyle.BLOCK && isOneOf('\n','\r','{')))
        		&& JmlOptions.instance(context).getBoolean(JmlOption.REQUIRE_WS.optionName())) {
        	if (isOneOf('+','-')) {
                Utils.instance(context).warning(position(),
                		"Annotation comments beginning with @+ or @- are no longer supported; use keys instead");

        	}
        	// Not a valid JML comment if there is not whitespace after the @.
        	// This is to avoid processing commented out Annotations, like //@Injected or //@line
        	reset(endPos);
            return super.processComment(pos, endPos, style);
        }
        
        if (jml) {
            // We are already in a JML comment - so we have an embedded comment.
            // The action is to just ignore the embedded comment start
            // characters that we just scanned.
            
            // do nothing
            
        } else {

            // We initialize state and proceed to process the comment as JML text
            jmlcommentstyle = style;
            jml = true;
        }
        return null; // Tell the caller to ignore the comment - that is, to not consider it a regular comment
    }

    /** Checks comment nesting and resets to position after the comment; only call this for
     * valid JML comments, whether processed or not */
    protected void cleanup(int commentStart, int endPos, CommentStyle style) {
        if (jml && jmlcommentstyle == CommentStyle.LINE && style == CommentStyle.BLOCK) {
            do {
                char cch = next();
                if (cch == '\r' || cch == '\n') {
                    log.error(commentStart, "jml.message", "Java block comment must terminate within the JML line comment");
                    break;
                }
            } while (position() < endPos);
        }
    	if (endPos != position()) reset(endPos); // Needed if we abort a comment before completing it
    }
    
    /**
     * Scans the next token in the character buffer; after this call, then
     * token() and jmlToken() provide the values of the scanned token. Also
     * pos() gives the beginning character position of the scanned token, and
     * endPos() gives (one past) the end character position of the scanned
     * token.
     * <P>
     * Both pos and endPos point to the end of a unicode sequence if the  // FIXME - validate this paragraph
     * relevant character is represented by a unicode sequence. The internal bp
     * pointer should be at endPos and the internal ch variable should contain
     * the following character.
     * <P>
     * Note that one of the following holds at return from this method:<BR>
     * a) token() != CUSTOM && token() != null && jmlToken() == null (a Java token)<BR>
     * b) token() == CUSTOM && jmlToken() != null (a JML token)<BR>
     * c) token() == IMPORT && jmlToken() == MODEL (the beginning of a model import)
     * <BR>
     */
    // NOTE: We do quite a bit of hackery here to avoid changes in the Scanner.
    // We did however have to change some permissions, so perhaps we should have
    // bitten the bullet and just combined all of this into a revised scanner. 
    // It would have not made possible our goal of keeping changes in the 
    // javac code minimal,
    // for easier maintenance, but it would have made for a simpler and more
    // understandable and better designed JML scanner.
    @Override
    public Token readToken() {
    	
        // JmlScanner enters with this relevant global state:
        //   jml - true if we are currently within a JML comment
        //   jmlcommentstyle - (if jml is true) the kind of comment block (LINE or BLOCK) we are in
        // Responds with updates to that state as well as to
        //   jmlToken, jmlTokenKind, bp, ch, endPos, tk, name
        boolean initialJml = jml;
        int pos, endPos;
        while (true) { // The loop is just so we can easily skip a token and sscan the next one with a 'continue' 
            jmlTokenKind = null;
            jmlTokenClauseKind = null;
            Token t = super.readToken(); // Sets tk, May modify jmlTokenKind
            pos = t.pos;
            endPos = t.endPos;
            // Note that the above may call processComment. If the comment is a JML comment, the
            // reader and tokenizer will be repointed to tokenize within the JML comment. This
            // may result in a CUSTOM Java token being produced with jmlTokenKind set, for example,
            // by calls down to methods such as scanOperator and scanIdent in this class.
            // So now we can produce a replacement token.

            // Possible situations at this point
            // a) jmlToken.kind != CUSTOM, jmlTokenKind == null (a Java token)
            // b) jmlToken.kind == CUSTOM, jmlTokenKind != null (a JML token)
            // c) jmlToken.kind == MONKEYS_AT, jmlTokenKind = ENDJMLCOMMENT, jml = false (leaving a JML comment)
            // jml may have changed (and will for case c), meaning that we have entered or are leaving a JML comment
            // No special token is issued for starting a JML comment.
            // There is a mode that determines whether ENDJMLCOMMENT tokens are returned.
            // The advantage of returning them is that then error recovery is better - bad JML can be caught by
            // unexpected end of comment; the disadvantage is that ENDJMLCOMMENT tokens can appear lots of places - 
            // the parser has to expect and swallow them. In official JML, clauses and expressions must be contained
            // in whole JML comments, so the locations where END tokens can occur are restricted.  Nevertheless, lots
            // of bugs have resulted from unexpected end of comment tokens.
            // An end token is never returned if the comment is empty or has only nowarn material in it.
            // nowarn information is scanned and stored,  but not returned as tokens
            // FIXME - review and fix use of ENDOFCOMMENT tokens in the parser; also unicode
            
            if (!jml) {
                if (jmlTokenClauseKind == Operators.endjmlcommentKind) {
                    JmlToken jmlToken = new JmlToken(jmlTokenKind, jmlTokenClauseKind, t);
                    // FIXME - source field?
                    // if initialJml == true and now the token is ENDJMLCOMMENT, then we had 
                    // an empty comment. We don't return a token in that case.
                    if (!returnEndOfCommentTokens || !initialJml) continue; // Go get next token
                    if (skippingTokens >= 0 && t.kind != TokenKind.EOF) continue;
                   return jmlToken;
                } else {
                    if (skippingTokens >= 0) {
                    	if (t.kind != TokenKind.EOF) continue; // skip the token
                    	Utils.instance(context).warning(skippingTokens, "jml.message", "//#- block is not closed at the end of file");
                    }
                    return t; // A Java token
                }
            }

            if (t.kind == TokenKind.IDENTIFIER && jml && !inLineAnnotation) {
                String id = t.name().toString();
                IJmlClauseKind lak = org.jmlspecs.openjml.Extensions.allKinds.get(id);
                if (lak instanceof IJmlClauseKind.LineAnnotationKind) {
                    scanLineAnnotation(position(), id, lak);
                    continue;
                }
            }

            if (tk == TokenKind.STAR && get() == '/'
                && jmlcommentstyle == CommentStyle.BLOCK) {
                // We're in a BLOCK comment and we scanned a * and the next
                // character is a / so we are at the end of the comment
                next(); // advance past the /
                jml = false;
                endPos = position();
                jmlTokenKind = JmlTokenKind.ENDJMLCOMMENT;
                jmlTokenClauseKind = Operators.endjmlcommentKind;
                if (!returnEndOfCommentTokens || !initialJml) continue;
            } else if (tk == TokenKind.MONKEYS_AT) {
                // This is just for the case that a terminating * / is preceded by one or more @s
                // JML allows this, but it just complicates scanning - I wish JML would deprecate that syntax
                int first = position();
                char ch = get();
                if (jmlcommentstyle == CommentStyle.BLOCK
                        && (ch == '*' || ch == '@')) {
                    // This may be the end of a BLOCK comment. We have seen a real @;
                    // there may be more @s and then the * and /
                    while (get() == '@') next();
                    if (get() != '*') {
                        Utils.instance(context).error(first, position(), "jml.unexpected.at.symbols");
                        return readToken(); // Ignore and get the next token (recursively)
                    } else {
                        next(); // consume *
                        if (get() != '/') {
                         	Utils.instance(context).error(first, position(), "jml.at.and.star.but.no.slash");
                            return readToken();
                        } else {
                            next(); // consume /
                        }
                    }
                    tk = TokenKind.CUSTOM;
                    jmlTokenKind = JmlTokenKind.ENDJMLCOMMENT;
                    jmlTokenClauseKind = Operators.endjmlcommentKind;
                    jml = false;
                    endPos = position();
                    if (!returnEndOfCommentTokens || !initialJml) continue;
                }
            } else if (tk == TokenKind.LPAREN && get() == '*') {
                int start = position();
                char ch;
                next(); // skip the *
                outer: do {
                    while ((ch=get()) != '*') {
                        if ((jmlcommentstyle == CommentStyle.LINE && (ch == '\n' || ch == '\r')) || ch == LayoutCharacters.EOI ) {
                            // Unclosed informal expression
                        	Utils.instance(context).error(start,position(),"jml.unclosed.informal.expression");
                            break outer;
                        }
                        put();
                        next();
                    }
                    int star = position();
                    ch = next(); // skip the *, return the following character
                    if ((jmlcommentstyle == CommentStyle.LINE && (ch == '\n' || ch == '\r')) ||  ch == LayoutCharacters.EOI ) {
                        // Unclosed informal expression
                    	Utils.instance(context).error(start,position(),"jml.unclosed.informal.expression");
                        break outer;
                        // FIXME - check that we switch out of JML mode
                    }
                    if (jmlcommentstyle == CommentStyle.BLOCK && ch == '/') {
                        // Unclosed informal expression
                    	Utils.instance(context).error(start,position(),"jml.unclosed.informal.expression");
                        reset(star); // backup and rescan to process end of comment
                        break outer;
                        // FIXME - check that we switch out of JML mode - can we do without the reset?
                    }
                } while (get() != ')');
                accept(')') ;
                endPos = position();
                tk = TokenKind.CUSTOM;
                jmlTokenKind = JmlTokenKind.INFORMAL_COMMENT;
                jmlTokenClauseKind = SingletonExpressions.informalCommentKind;
            } else if (tk == TokenKind.LBRACE && get() == '|') {
                tk = TokenKind.CUSTOM;
                jmlTokenKind = JmlTokenKind.SPEC_GROUP_START;
                jmlTokenClauseKind = MethodSimpleClauseExtensions.specGroupStartClause;
                next(); // skip the '|'
                endPos = position();
            } else if (tk == TokenKind.BAR && get() == '}') {
                tk = TokenKind.CUSTOM;
                jmlTokenKind = JmlTokenKind.SPEC_GROUP_END;
                jmlTokenClauseKind = MethodSimpleClauseExtensions.specGroupEndClause;
                next();
                endPos = position();
            } else if (tk == TokenKind.ERROR && sb.length() == 2 && sb.charAt(0) == '.' && sb.charAt(1) == '.') {
                jmlTokenKind = JmlTokenKind.DOT_DOT;
                jmlTokenClauseKind = Operators.dotdotKind;
                endPos = position();
            }
            if (skippingTokens >= 0 && t.kind != TokenKind.EOF) continue;
            return jmlTokenKind == null ? t : new JmlToken(jmlTokenKind, jmlTokenClauseKind, TokenKind.CUSTOM, pos, endPos);
            // FIXME - source field?
        }
    }
    
    /** Overrides the Java scanner in order to catch situations in which the
     * first part of a double literal is immediately followed by a dot,
     * e.g. 123.. ; within JML, this should be an int followed by a DOT_DOT token 
     */
    @Override
    public void scanFractionAndSuffix(int pos) {
        if (jml && get() == '.') {
            sb.setLength(sb.length()-1);;
            reset(position()-1); // FIXME - not unicode safe
            tk = TokenKind.INTLITERAL;
        } else {
            super.scanFractionAndSuffix(pos);
        }
    }
    
    private boolean inLineAnnotation = false;

    /** This method presumes the NOWARN token has been read and handles the names
     * within the nowarn, reading through the terminating semicolon or end of JML comment
     */
    public void scanLineAnnotation(int pos, String id, IJmlClauseKind ckind) {
        inLineAnnotation = true;
        ((IJmlClauseKind.LineAnnotationKind)ckind).scan(pos, id, ckind, this);
        inLineAnnotation = false;
    }

    /**
     * This method is called internally when a nowarn lexical pragma is scanned;
     * it is called once for each label in the pragma.
     * 
     * @param file The file being scanned
     * @param pos The 0-based character position of the label
     * @param label The label in the pragma
     */
    protected void handleNowarn(DiagnosticSource file, int pos, String label) {
        nowarns.addItem(file,pos,label);
    }

    /**
     * Overrides the superclass method in order to denote a backslash as
     * special. This lets scanOperator detect the JML backslash keywords.
     * Otherwise the backslash is reported as an illegal character. This does
     * not affect scanning literals or unicode conversion.
     */
    @Override
    protected boolean isSpecial(char ch) {
        if (jml && ch == '\\') return true;
        return super.isSpecial(ch);
    }

    /**
     * Called when the superclass scanner scans a line termination. We override
     * this method so that when jml is true, we can (a) if this is a LINE
     * comment, signal the end of the comment (b) if this is a BLOCK comment,
     * skip over leading @ symbols in the following line
     */
    @Override
    protected void processLineTerminator(int pos, int endPos) {
    	tk = null;
        if (jml) {
            if (jmlcommentstyle == CommentStyle.LINE) {
                jml = false;
                if (returnEndOfCommentTokens) {
                    tk = TokenKind.CUSTOM;
                    jmlTokenKind = JmlTokenKind.ENDJMLCOMMENT;
                    jmlTokenClauseKind = Operators.endjmlcommentKind;
                }
            } else {
                // skip any whitespace followed by @ symbols
                while (Character.isWhitespace(get()))
                    next();
                while (get() == '@')
                    next();
            }
        }
        super.processLineTerminator(pos, endPos);
    }

    /**
     * Called to find identifiers and keywords when a character that can start a
     * Java identifier has been scanned. We override so that when jml is true,
     * we can convert identifiers to JML keywords, including converting assert
     * to the JML assert keyword.
     * Sets tk, name, jmlTokenKind
     */
    @Override
    protected void scanIdent() {
        super.scanIdent(); // Sets tk and name
        jmlTokenKind = null;
        jmlTokenClauseKind = null;
        if (!jml) {
            return;
        }
        if (tk == TokenKind.IDENTIFIER) {
            String s = chars();
            // TODO - we are just ignoring the redundantly suffixes
            if (s.endsWith("_redundantly")) {
                s = s.substring(0, s.length() - "_redundantly".length());
                name = Names.instance(context).fromString(s);
            }
        } else if (tk == TokenKind.ASSERT) {
            tk = TokenKind.IDENTIFIER;
            name = Names.instance(context).fromString("assert");
        }
    }

    /**
     * Called to scan an operator. We override to detect JML operators as well.
     * And also backslash tokens.
     */
    @Override
    protected void scanOperator() {
    	tk = null;
    	super.scanOperator();
        if (!jml) return; // not in JML - so we scanned a regular Java operator
        if (tk == null && get() == '\\') {
            // backslash identifiers get redirected here since a \ itself is an
            // error in pure Java - isSpecial does the trick
            int ep = position();
            put(); // include the backslash
            char ch = next();
            if (Character.isLetter(ch)) {
                super.scanIdent();  // tk and name are set
                // assuming that token() is Token.IDENTIFIER
                String seq = name.toString();
                JmlTokenKind t = JmlTokenKind.backslashTokens.get(seq);
                if (t != null) {
                	// TODO - any backslash tokens remaining in JmlToken -- they should all be moved to ext
                    tk = TokenKind.CUSTOM;
                    jmlTokenKind = t;
                    jmlTokenClauseKind = Extensions.allKinds.get(seq);
                } else {
                    tk = TokenKind.IDENTIFIER;
                    jmlTokenKind = null;
                    jmlTokenClauseKind = Extensions.allKinds.get(seq);
                    if (jmlTokenClauseKind == null) {
                    	jmlError(ep, position(), "jml.bad.backslash.token", seq); // sets ERROR token
                    }
                }
            } else {
                jmlError(ep, position(), "jml.extraneous.backslash"); // sets ERROR token
            }
            return;
        }
        if (tk == null) {
            jmlError(position(), "jml.internal", "Internal preconditions violated when scanning for operators: " + get());
            // sets ERROR token
        	return;
        }
        // Now check if there is a longer JML operator
        TokenKind t = tk;
        if (tk == TokenKind.EQEQ) {
            if (accept('>')) {
                tk = TokenKind.CUSTOM;
                jmlTokenKind = JmlTokenKind.IMPLIES; // ==>
                jmlTokenClauseKind = Operators.impliesKind;
            }
        } else if (t == TokenKind.LTEQ) {
            int k = position();
            if (accept('=')) {
                // At the last = of <==
                if (accept('>')) {
                    tk = TokenKind.CUSTOM;
                    jmlTokenKind = JmlTokenKind.EQUIVALENCE; // <==>
                    jmlTokenClauseKind = Operators.equivalenceKind;
                } else {
                    tk = TokenKind.CUSTOM;
                    jmlTokenKind = JmlTokenKind.REVERSE_IMPLIES; // <==
                    jmlTokenClauseKind = Operators.reverseimpliesKind;
                }
            } else if (accept('!')) {
                if (accept('=')) {
                    if (accept('>')) {
                        tk = TokenKind.CUSTOM;
                        jmlTokenKind = JmlTokenKind.INEQUIVALENCE; // <=!=>
                        jmlTokenClauseKind = Operators.inequivalenceKind;
                    } else { // reset to the !
                        reset(k);
                    }
                } else { // reset to the !
                    reset(k);
                }
            }
        } else if (t == TokenKind.LT) {
            if (accept(':')) {
                tk = TokenKind.CUSTOM;
                jmlTokenKind = JmlTokenKind.SUBTYPE_OF; // <:
                jmlTokenClauseKind = Operators.subtypeofKind;
                if (accept('=')) {
                    tk = TokenKind.CUSTOM;
                    jmlTokenKind = JmlTokenKind.SUBTYPE_OF_EQ; // <:=
                    jmlTokenClauseKind = Operators.subtypeofeqKind;
                }
            } else if (accept('-')) {
                tk = TokenKind.CUSTOM;
                jmlTokenKind = JmlTokenKind.LEFT_ARROW; // <-
                jmlTokenClauseKind = Operators.leftarrowKind;
            } else if (accept('#')) {
                tk = TokenKind.CUSTOM;
                jmlTokenKind = JmlTokenKind.LOCK_LT; // <#
                jmlTokenClauseKind = Operators.lockltKind;
                if (accept('=')){
                    jmlTokenKind = JmlTokenKind.LOCK_LE; // <#=
                    jmlTokenClauseKind = Operators.lockleKind;
                }
            }
        } else if (t == TokenKind.LTLT) {
            if (accept('<')) {
                tk = TokenKind.CUSTOM;
                jmlTokenKind = JmlTokenKind.WF_LT; // <<<
                jmlTokenClauseKind = Operators.wfltKind;
                if (accept('=')){
                    tk = TokenKind.CUSTOM;
                    jmlTokenKind = JmlTokenKind.WF_LE; // <<<=
                    jmlTokenClauseKind = Operators.wfleKind;
                }
            }
        }
    }

    /**
     * Reads characters up to an EOI or up to and through the specified
     * character, which ever is first.
     * 
     * @param c the character to look for
     */
    public void skipThroughChar(char c) {
    	char ch = get();
        while (ch != c && ch != LayoutCharacters.EOI)
            ch = next();
        accept(c);
    }
    
    /** Overrides in order to catch the error message that results from seeing just
     * a .. instead of . or ...
     */
    @Override
    protected void lexError(int pos, com.sun.tools.javac.util.JCDiagnostic.Error key) {
    	if (key != Errors.IllegalDot) {
    		super.lexError(pos,  key);
    	} else {
    		tk = TokenKind.CUSTOM;
    		jmlTokenKind = JmlTokenKind.DOT_DOT;
    		jmlTokenClauseKind = Operators.dotdotKind;
    	}
    }


    /** Records a lexical error (no valid token) at a single character position,
     * the resulting token is an ERROR token. */
    protected void jmlError(int pos, String key, Object... args) {
        Utils.instance(context).error(pos, pos+1, key, args);
        tk = TokenKind.ERROR;
        jmlTokenKind = null;
        jmlTokenClauseKind = null;
        errPos(pos);
    }

    /** Logs an error; the character range of the error is from pos up to 
     * BUT NOT including endpos.
     */
    public void jmlError(int pos, int endpos, String key, Object... args) {
        Utils.instance(context).error(pos, endpos, key, args);
        tk = TokenKind.ERROR;
        errPos(pos);
    }
    
    public String chars() {
        return sb.toString();
    }

    // Index of current character
    public int pos() {
        return position();
    }
    
    /** Gets a segment of the input buffer as raw bytes (unescape or unicide interpretation) */
    public String getCharacters(int p, int e) {
    	return String.valueOf(getRawCharacters(p,e));
    }
    
}
