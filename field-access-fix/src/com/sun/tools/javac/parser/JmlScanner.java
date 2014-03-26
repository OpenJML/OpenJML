/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.parser;

import java.nio.CharBuffer;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.DiagnosticSource;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.LayoutCharacters;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Options;

/* NOTE: - oddities in the Scanner class
 It seems that if the first character of a token is unicode, then pos is
 set to be the last character of that initial unicode sequence.
 I don't think the endPos value is set correctly when a unicode is read;
 endPos appears to be the end of the character after the token characters,
 which is not correct if the succeeding token is a unicode character

 unicodeConversionBp does not seem to be useful for anything; does it stop
 two unicode conversions in a row?  Actually, when an initial backslash is
 in unicode, then that backslash is not the beginning of another unicode
 sequence - the check on unicodeConversionBp stops this.

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
public class JmlScanner extends DocCommentScanner {

    /**
     * This factory is used to generate instances of JmlScanner. There is
     * one factory per compilation context and a new instance of JmlScanner
     * for each new file parsed. The Context is used to
     * have a consistent set of information across all files parsed within a
     * compilation task.
     */
    public static class JmlFactory extends ScannerFactory {

        /** The unique compilation context with which this factory was created */
        public Context                 context;

        /**
         * Creates a new factory that creates instances of JmlScanner; a new scanner
         * is used for each file being parsed.
         * 
         * @param context The common context used for this whole compilation
         */
        protected JmlFactory(Context context) {
            super(context);
            this.context = context;
        }

        /**
         * Call this to register this factory as the factory to be used to
         * create scanners, which will be JML scanners instead of Java scanners,
         * within this compilation context.
         * 
         * @param context The common compilation context
         */
        public static void preRegister(final Context context) {
            context.put(scannerFactoryKey,
                    new Context.Factory<ScannerFactory>() {
                        public ScannerFactory make(Context context) {
                            return new JmlScanner.JmlFactory(context);
                        }
                    });
        }

        /** A convenience method to produce a new scanner on the given input,
         * set to parse JML and javadoc comments as well.
         * @param input the input to parse
         * @return the new scanner, initialized at the beginning of the input
         */
        public Scanner newScanner(CharSequence input) {
            return newScanner(input,true);
        }

        /*
         * (non-Javadoc)
         * 
         * @see com.sun.tools.javac.parser.Scanner.Factory#newScanner(char[],
         * int, boolean)
         */
        /** The last character in the input array may be overwritten with an 
         * EOI character; if you control the size of the input array, make it at
         * least one character larger than necessary, 
         * to avoid reallocating and copying the array.
         */
        @Override
        public JmlScanner newScanner(char[] input, int inputLength, boolean keepDocComments) {
            JmlScanner j = new JmlScanner(this, input, inputLength);
            init(j);
            return j;
        }

        /** Creates a new scanner that scans the given input */
        @Override
        public JmlScanner newScanner(CharSequence input, boolean keepDocComments) {
            JmlScanner j = new JmlScanner(this, CharBuffer.wrap(input));
            init(j);
            return j;
        }
        
        /** Does some initialization of just produced scanners - all in one method so that
         * the code does not have to be replicated across various newScanner methods.
         * @param j the JmlSCanner to initialize
         */
        protected void init(JmlScanner j) {
            j.noJML = !JmlOption.isOption(context, JmlOption.JML);
            j.keys = Utils.instance(context).commentKeys;
            j.nowarns = Nowarns.instance(context);
        }

    }
    
    /** The compilation context */
    protected Context context;
    
    /** A temporary reference to the instance of the nowarn collector for the context. */
    /*@NonNull*/ public Nowarns nowarns;

    /**
     * A flag that, when true, causes all JML constructs to be ignored; it is
     * set on construction according to a command-line option.
     */
    protected boolean       noJML      = false;

    /** Set to true internally while the scanner is within a JML comment */
    protected boolean       jml        = false;

    /** The set of keys for identifying optional comments */
    /*@NonNull*/ protected Set<String>     keys;
    
    /** A mode of the scanner that determines whether end of jml comment tokens are returned */
    public boolean returnEndOfCommentTokens = true;
    
    /**
     * When jml is true, then (non-backslash) JML keywords are recognized if
     * jmlkeyword is true and not if jmlkeyword is false; this is set by the
     * parser according to whether non-backslash JML tokens should be recognized
     * in the current parser state (e.g. such tokens are not recognized while
     * within expressions). jmlkeyword is always set to true at the beginning of
     * JML comments.
     */
    protected boolean       jmlkeyword = true;

    /**
     * Set by the scanner to the style of comment, either CommentStyle.LINE or
     * CommentStyle.BLOCK, prior to the scanner calling processComment()
     */
    protected CommentStyle  jmlcommentstyle;

    /** Valid after nextToken() and contains the next token if it is a JML token
     * and null if the next token is a Java token */
    //@ nullable
    protected JmlToken     jmlToken;

    /**
     * Creates a new scanner, but you should use JmlFactory.newScanner() to get
     * one, not this constructor.<P>

     * The last character in the input array may be overwritten with an EOI character; if you
     * control the size of the input array, make it at least one character larger than necessary, 
     * to avoid the overwriting or reallocating and copying the array.

     * @param fac The factory generating the scanner
     * @param input The character buffer to scan
     * @param inputLength The number of characters to scan from the buffer
     */
    // @ requires fac != null && input != null;
    // @ requires inputLength <= input.length;
    protected JmlScanner(JmlFactory fac, char[] input, int inputLength) {
        super(fac, input, inputLength);
        context = fac.context;
    }

    /**
     * Creates a new scanner, but you should use JmlFactory.newScanner() to get
     * one, not this constructor.
     * 
     * @param fac The factory generating the scanner
     * @param buffer The character buffer to scan
     */
    // @ requires fac != null && buffer != null;
    protected JmlScanner(JmlFactory fac, CharBuffer buffer) {
        super(fac, buffer);
        context = fac.context;
    }

    /**
     * Sets the jml mode - used for testing to be able to test constructs that
     * are within a JML comment.
     * 
     * @param j set the jml mode to this boolean value
     */
    public void setJml(boolean j) {
        jml = j;
    }

    /**
     * Sets the keyword mode
     * 
     * @param j
     *            the new value of the keyword mode
     */
    public void setJmlKeyword(boolean j) {
        jmlkeyword = j;
    }
    
    /** The current set of conditional keys used by the scanner.
     */
    public Set<String> keys() {
        return keys;
    }

    /**
     * Valid after nextToken()
     * 
     * @return the JML token for the most recent scan, null if the token is
     *         purely a Java token
     */
    //@ pure nullable
    public JmlToken jmlToken() {
        return jmlToken;
    }
    
    // This is called whenever the Java (superclass) scanner has scanned a whole
    // comment. We override it in order to handle JML comments specially. The
    // overridden
    // method returns and proceeds immediately to scan for the next Java token.
    // Here if the comment is indeed a JML comment, we reset the scanner to the
    // beginning of the comment, set jml to true, and let the scanner proceed.
    @Override
    protected void processComment(CommentStyle style) {
        // The range pos() to endPos() does include the opening and closing
        // comment characters.
        // It does not include line ending for line comments, so
        // an empty line comment can be just two characters.
        if (noJML || style == CommentStyle.JAVADOC) {
            super.processComment(style);
            return;
        }

        // Save the buffer positions in the super class
        // After a call of scanChar(), ch is the character at the bp
        // position in character buffer; if the buffer held a unicode
        // sequence, bp is at the end of the sequence and ch is the
        // translated character
        int bpend = bp; // The index of the character just after the comment
        char chend = ch; // The character just after the comment 

        // Note on scanChar - it is valid to call scanChar if
        // ch is not EOI; the last character of the input will be an EOI
        
        // rescan the input
        // pos() points to the first / of the comment sequence (or to the
        // last character of the unicode sequence for that /)
        bp = pos(); // OK for unicode
        int commentStart = bp;
        scanChar(); // the next / or *
        scanChar(); // The @, or a + or - if there are keys, or something else if it is not a JML comment
        int plusPosition = bp;

        // FIXME - do we need this line?
        //if (bp >= end) return; // This can happen if there is a // right at the end of the line
        boolean someplus = false; // true when at least one + key has been read
        boolean foundplus = false; // true when a + key that is in the list of enabled keys has been read
        while (ch != '@') {
            if (ch != '+' && ch != '-') {
                // Not a valid JML comment - just return
                // Restart after the comment
                bp = bpend;
                ch = chend;
                super.processComment(style);
                return;
            }
            
            boolean isplus = ch == '+';
            scanChar();
            if (ch == '@') {
                // Old -style //+@ or //-@ comments
                
                // Too many warnings to enable this message
                if (Options.instance(context).isSet("-Xlint:deprecation")) {
                    log.warning(new DiagnosticPositionSE(commentStart,plusPosition,bp),"jml.deprecated.conditional.annotation");
                }

                // To be backward compatible at the moment,
                // quit for //-@, process the comment if //+@
                // TODO: Change this behavior once the library specs have no more //+@ or /*+@ comments
                if (isplus) break;
                bp = bpend;
                ch = chend;
                super.processComment(style);
                return;
            }
            if (isplus) someplus = true;
            // We might call nextToken here and look for an identifier,
            // but that could be a recursive call of nextToken, which might
            // be dangerous, so we use scanIdent instead
            if (!Character.isJavaIdentifierStart(ch)) {
                // Not a valid JML comment - just return
                // Restart after the comment
                bp = bpend;
                ch = chend;
                super.processComment(style);
                return;
            }
            // Check for keys
            scanIdent(); // Only valid if ch is isJavaIdentifierStart
            sp = 0; // See the use of sp in Scanner - if sp is not reset, then the
                    // next identifier is appended to the key
            Name key = name(); // the identified just scanned
            if (keys.contains(key.toString())) {
                if (isplus) foundplus = true;
                else {
                    // negative key found - return
                    bp = bpend;
                    ch = chend;
                    super.processComment(style);
                    return;
                }
            }
        }
        if (!foundplus && someplus) {
            // There were pluses but not the plus we were looking for
            // Restart after the comment
            bp = bpend;
            ch = chend;
            super.processComment(style);
            return;
        }

        while (ch == '@') {
            scanChar();
        } // Gobble up all leading @s
        
        if (jml) {
            // We are already in a JML comment - so we have an embedded comment.
            // The action is to just ignore the embedded comment start
            // characters.
            // FIXME - what if the embedded comment has keys?
            return;
        }

        // We initialize state and proceed to process the comment as JML text
        jmlcommentstyle = style;
        jml = true;
        jmlkeyword = true;
        return;
    }

    /**
     * Scans the next token in the character buffer; after this call, then
     * token() and jmlToken() provide the values of the scanned token. Also
     * pos() gives the beginning character position of the scanned token, and
     * endPos() gives (one past) the end character position of the scanned
     * token.
     * <P>
     * Both pos and endPos point to the end of a unicode sequence if the
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
    public void nextToken() {
        // JmlScanner enters with this relevant global state:
        //   jml - true if we are currently within a JML annotation
        //   jmlcommentstyle - (if jml is true) the kind of comment block (LINE or BLOCK) we are in
        //   jmlkeyword - (if jml is true) whether to translate non-backslash 
        //                keywords as JML keywords or as Java identifiers
        // Responds with updates to that state as well as to
        //   token, jmlToken, bp, ch, _pos, endPos, docComment
        boolean initialJml = jml;
        while (true) {
            jmlToken = null;
            super.nextToken();
            String dc = docComment;
            // Possible situations at this point
            // a) token != CUSTOM, token != null, jmlToken == null (a Java token)
            // b) token == CUSTOM, jmlToken != null (a JML token)
            // c) token == MONKEYS_AT, jmlToken = ENDJMLCOMMENT, jml = false (leaving a JML comment)
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
                if (jmlToken == JmlToken.ENDJMLCOMMENT) {
                    token(Token.CUSTOM);
                    if (!returnEndOfCommentTokens || !initialJml) continue; // Go get next token
                    return;
                } else {
                    return; // A Java token
                }
            }

            if (jmlToken == JmlToken.NOWARN) {
                scanNowarn();
                continue;
            } else if (token() == Token.STAR && ch == '/'
                && jmlcommentstyle == CommentStyle.BLOCK) {
                // We're in a BLOCK comment and we scanned a * and the next
                // character is a / so we are at the end of the comment
                scanChar(); // advance past the /
                jml = false;
                token(Token.CUSTOM);
                endPos = bp;
                jmlToken = JmlToken.ENDJMLCOMMENT;
                docComment = dc;
                if (!returnEndOfCommentTokens || !initialJml) continue;
            } else if (token() == Token.MONKEYS_AT) {
                // This is just for the case that a terminating */ is preceded by one or more @s
                // JML allows this, but it just complicates scanning - I wish JML would deprecate that syntax
                int first = pos();
                if (jmlcommentstyle == CommentStyle.BLOCK
                        && (ch == '*' || ch == '@')) {
                    // This may be the end of a BLOCK comment. We have seen a real @;
                    // there may be more @s and then the * and /
                    while (ch == '@')
                        scanChar();
                    if (ch != '*') {
                        // TODO - should really report this as a legal series
                        // of AT tokens
                        jmlError(first, bp, "jml.unexpected.at.symbols");
                        nextToken(); // recursively try to find the next token
                        return;
                    } else {
                        scanChar(); // consume *
                        if (ch != '/') {
                            // TODO - should really report this as a legal
                            // series of AT tokens and a STAR
                            jmlError(first, bp, "jml.at.and.star.but.no.slash");
                            nextToken();
                            return;
                        } else {
                            scanChar(); // consume /
                        }
                    }
                    token(Token.CUSTOM);
                    jmlToken = JmlToken.ENDJMLCOMMENT;
                    jml = false;
                    endPos = bp;
                    docComment = dc;
                    if (!returnEndOfCommentTokens || !initialJml) continue;
                }
            } else if (token() == Token.LPAREN && ch == '*') {
                int start = bp;
                scanChar(); // skip the *
                outer: do {
                    while (ch != '*') {
                        if ((jmlcommentstyle == CommentStyle.LINE && (ch == '\n' || ch == '\r')) ||  ch == LayoutCharacters.EOI ) {
                            // Unclosed informal expression
                            jmlError(start,bp,"jml.unclosed.informal.expression");
                            break outer;
                        }
                        putChar(ch);
                        scanChar();
                    }
                    int star = bp;
                    scanChar(); // skip the *
                    if ((jmlcommentstyle == CommentStyle.LINE && (ch == '\n' || ch == '\r')) ||  ch == LayoutCharacters.EOI ) {
                        // Unclosed informal expression
                        jmlError(start,bp,"jml.unclosed.informal.expression");
                        break outer;
                    }
                    if (jmlcommentstyle == CommentStyle.BLOCK && ch == '/') {
                        // Unclosed informal expression
                        jmlError(start,bp,"jml.unclosed.informal.expression");
                        bp = star;
                        ch = '*';
                        break outer;
                    }
                } while (ch != ')');
                if (ch == ')') scanChar();
                endPos = bp;
                token(Token.CUSTOM);
                jmlToken = JmlToken.INFORMAL_COMMENT;
            } else if (jmlToken == JmlToken.MODEL) {
                char prevch = ch;
                int prevbp = bp;
                int prevpos = _pos;
                int prevendpos = endPos();
                super.nextToken();
                docComment = dc;
                if (jml && token() == Token.IMPORT) {
                    jmlToken = JmlToken.MODEL;
                } else {
                    // Need to backtrack
                    ch = prevch;
                    bp = prevbp;
                    _pos = prevpos;
                    endPos = prevendpos;
                    token(Token.CUSTOM);
                    jmlToken = JmlToken.MODEL;
                }
            } else if (token() == Token.LBRACE && ch == '|') {
                token(Token.CUSTOM);
                jmlToken = JmlToken.SPEC_GROUP_START;
                scanChar();
                endPos = bp;
            } else if (token() == Token.BAR && ch == '}') {
                token(Token.CUSTOM);
                jmlToken = JmlToken.SPEC_GROUP_END;
                scanChar();
                endPos = bp;
            }
            return;
        }
    }
    
    /** Overrides the Java scanner in order to catch situations in which the
     * first part of a double literal is immediately followed by a dot,
     * e.g. 123.. ; within JML, this should be an int followed by a DOT_DOT token 
     */
    @Override
    public void scanFractionAndSuffix() {
        if (jml && ch == '.') {
            sp--;
            bp--; // FIXME - not unicode safe
            token(Token.INTLITERAL);
        } else {
            super.scanFractionAndSuffix();
        }
    }

    /** This method presumes the NOWARN token has been read and handles the names
     * within the nowarn, reading through the terminating semicolon or end of JML comment
     */
    public void scanNowarn() {
        boolean prev = jmlkeyword;
        jmlkeyword = false;
        try {
            nextToken();
            if (token() == Token.SEMI || jmlToken == JmlToken.ENDJMLCOMMENT) {
                // No labels - so this means suppress everything
                // Indicate this with null
                handleNowarn(log.currentSource(), pos(), null);
            } else {
                while (token() != Token.SEMI && jmlToken != JmlToken.ENDJMLCOMMENT) {
                    if (token() != Token.IDENTIFIER){
                        // Bad statement or missing terminating semicolon
                        jmlError(pos(), endPos(), "jml.bad.nowarn");
                        // expected identifier
                        skipThroughChar(';');
                        return;
                    }
                    String label = stringVal();
                    handleNowarn(log.currentSource(), pos(), label);
                    nextToken();
                    if (token() == Token.COMMA){
                        nextToken();
                    }
                }
            }
            if (jmlToken == JmlToken.ENDJMLCOMMENT) { 
                log.warning(pos(), "jml.nowarn.with.no.semicolon");
                // FIXME Here we are swallowing the end of comment - we normally 
                // expect that token in the stream. However if there is just a 
                // nowarn, the Java scanner will not expect a standalone ENDJMLCOMMENT
            }
        } finally {
            jmlkeyword = prev;
        }
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
     * Scans the next character, doing any unicode conversion. The buffer
     * pointer is incremented BEFORE fetching the character. So except for
     * unicode and backslash issues, after this call, buf[bp] == ch; This does
     * not set pos() or endPos(). If the character scanned is unicode, then upon
     * return, bp points to the last character of the unicode sequence within
     * the character buffer (buf). Also, if the character just scanned is
     * unicode, then unicodeConversionBp == bp. This enables a check (via the
     * test unicodeConversionBp == bp) of whether the character just scanned is
     * unicode and hence not allowed to be the backslash that starts a new
     * unicode sequence.
     */
    @Override
    protected void scanChar() {
        super.scanChar();
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
    protected void processLineTerminator() {
        super.processLineTerminator();
        if (jml) {
            if (jmlcommentstyle == CommentStyle.LINE) {
                jml = false;
                jmlToken = JmlToken.ENDJMLCOMMENT;
                endPos = bp;
                if (returnEndOfCommentTokens) {
                    ch = '@'; // Signals the end of comment to nextToken()
                    bp--; // FIXME - not right for unicode
                }
            } else {
                // skip any whitespace followed by @ symbols
                while (Character.isWhitespace(ch))
                    scanChar();
                while (ch == '@')
                    scanChar();
            }
        }
    }

    /**
     * Called to find identifiers and keywords when a character that can start a
     * Java identifier has been scanned. We override so that when jml and
     * jmlkeyword are true,
     * we can convert identifiers to JML keywords, including converting assert
     * to the JML assert keyword.
     */
    @Override
    protected void scanIdent() {
        super.scanIdent();
        if (!jml || !jmlkeyword)
            return;
        Token t = token();
        if (t == Token.IDENTIFIER) {
            String s = stringVal();
            // TODO - we are just ignoring the redundantly suffixes
            if (s.endsWith("_redundantly")) {
                s = s.substring(0, s.length() - "_redundantly".length());
            }
            JmlToken tt = JmlToken.allTokens.get(s);
            if (tt != null) {
                token(Token.CUSTOM);
                jmlToken = tt;
                return; 
            }
            // FIXME - can we count on jmlToken to be null?
        } else if (t == Token.ASSERT) {
            token(Token.CUSTOM);
            jmlToken = JmlToken.ASSERT;
        }
    }

    /**
     * Called to scan an operator. We override to detect JML operators as well.
     * And also backslash tokens.
     */
    @Override
    protected void scanOperator() {
        if (jml && ch == '\\') {
            // backslash identifiers get redirected here since a \ itself is an
            // error in pure Java - isSpecial does the trick
            int ep = pos();
            putChar(ch); // include the backslash
            scanChar();
            if (Character.isLetter(ch)) {
                super.scanIdent();
                // assuming that token() is Token.IDENTIFIER
                String seq = stringVal();
                JmlToken t = JmlToken.backslashTokens.get(seq);
                if (t != null) {
                    token(Token.CUSTOM);
                    jmlToken = t;
                    endPos = bp;
                } else {
                    jmlError(ep, bp, "jml.bad.backslash.token", seq);
                    // token is set to ERROR
                }
            } else {
                jmlError(ep, bp, "jml.extraneous.backslash");
                // token is set to ERROR
            }
            return;
        }
        super.scanOperator();
        endPos = bp;
        if (!jml) return; // not in JML - so we scanned a regular Java operator
        
        Token t = token();
        if (t == Token.EQEQ) {
            if (ch == '>') {
                scanChar();
                endPos = bp;
                token(Token.EQ);
                jmlToken = JmlToken.IMPLIES; // ==>
            }
        } else if (t == Token.LTEQ) {
            if (ch == '=') {
                // At the last = of <==
                scanChar();
                if (ch == '>') {
                    token(Token.EQ);
                    jmlToken = JmlToken.EQUIVALENCE; // <==>
                    scanChar();
                    endPos = bp;
                } else {
                    token(Token.EQ);
                    jmlToken = JmlToken.REVERSE_IMPLIES; // <==
                    endPos = bp;
                }
            } else if (ch == '!') {
                int k = bp; // Last character of the !
                scanChar();
                if (ch == '=') {
                    scanChar();
                    if (ch == '>') {
                        token(Token.EQ);
                        jmlToken = JmlToken.INEQUIVALENCE; // <=!=>
                        scanChar();
                        endPos = bp;
                    } else { // reset to the !
                        bp = k;
                        ch = '!';
                    }
                } else {
                    bp = k;
                    ch = '!';
                }
            }
        } else if (t == Token.LT) {
            if (ch == ':') {
                token(Token.CUSTOM);
                jmlToken = JmlToken.SUBTYPE_OF; // <:
                scanChar();
                endPos = bp;
            } else if (ch == '-') {
                token(Token.CUSTOM);
                jmlToken = JmlToken.LEFT_ARROW; // <-
                scanChar();
                endPos = bp;
            } else if (ch == '#') {
                token(Token.CUSTOM);
                jmlToken = JmlToken.LOCK_LT; // <#
                scanChar();
                if (ch == '=') {
                    token(Token.CUSTOM);
                    jmlToken = JmlToken.LOCK_LE; // <#=
                    scanChar();
                }
                endPos = bp;
            }
        } else if (t == Token.SUB) {
            if (ch == '>') {
                token(Token.CUSTOM);
                jmlToken = JmlToken.RIGHT_ARROW; // ->
                scanChar();
                endPos = bp;
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
        while (ch != c && ch != LayoutCharacters.EOI)
            scanChar();
        if (ch == c)
            scanChar();
    }
    
    /** Records a lexical error (no valid token) at a single character position,
     * the resulting token is an ERROR token. */
    @Override
    protected void lexError(int pos, String key, Object... args) {
        jmlError(pos,key,args);
    }
    
    /** Overrides in order to catch the error message that results from seeing just
     * a .. instead of . or ...
     */
    @Override
    protected void lexError(String key, Object... args) {
        if ("malformed.fp.lit".equals(key) && sp == 2 && stringVal().equals(JmlToken.DOT_DOT.internedName())) {
            token(Token.CUSTOM);
            jmlToken = JmlToken.DOT_DOT;
        } else {
            super.lexError(key,args);
        }
    }


    /** Records a lexical error (no valid token) at a single character position,
     * the resulting token is an ERROR token. */
    protected void jmlError(int pos, String key, Object... args) {
        log.error(new DiagnosticPositionSE(pos,pos),key,args);
        token(com.sun.tools.javac.parser.Token.ERROR);
        jmlToken = null;
        errPos(pos);
    }

    /** Logs an error; the character range of the error is from pos up to 
     * BUT NOT including endpos.
     */
    protected void jmlError(int pos, int endpos, String key, Object... args) {
        // FIXME - the endPos -1 is not unicode friendly - and actually we'd like to adjust the
        // positions of pos and endpos to correspond to appropriate unicode boundaries, here and in
        // the other jmlError method
        log.error(new DiagnosticPositionSE(pos,endpos-1),key,args);
        token(com.sun.tools.javac.parser.Token.ERROR);
        errPos(pos);
    }
    
    /** A derived class of DiagnosticPosition that allows for straightforward setting of the
     * various positions associated with an error message.
     */
    static public class DiagnosticPositionSE implements DiagnosticPosition {
        protected int begin;
        protected int preferred;
        protected int end; // The end character, NOT ONE CHARACTER BEYOND
        
        public DiagnosticPositionSE(int begin, int end) {
            this.begin = begin;
            this.preferred = begin;
            this.end = end;
        }
        
        public DiagnosticPositionSE(int begin, int preferred, int end) {
            this.begin = begin;
            this.preferred = preferred;
            this.end = end;
        }
        
        @Override
        public JCTree getTree() {
            return null;
        }

        @Override
        public int getStartPosition() {
            return begin;
        }

        @Override
        public int getPreferredPosition() {
            return preferred;
        }

        @Override
        public int getEndPosition(Map<JCTree, Integer> endPosTable) {
            return end;
        }
        
    }


}
