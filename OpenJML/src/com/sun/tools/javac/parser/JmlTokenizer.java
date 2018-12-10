/*
 * This file is part of the OpenJML project.
 * Author: David R. Cok
 */
package com.sun.tools.javac.parser;

import com.sun.tools.javac.parser.Tokens.Comment.CommentStyle;
import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.EndPosTable;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.DiagnosticSource;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.LayoutCharacters;
import com.sun.tools.javac.util.Options;
import org.eclipse.jdt.annotation.Nullable;
import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.DefaultJmlTokenKind;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Utils;

import java.nio.CharBuffer;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

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
public class JmlTokenizer extends JavadocTokenizer { // FIXME - or should this be JavaTokenizer?

    /**
     * Registered Tokens
     **/
    public final Map<String, JmlTokenKind> allTokens = new HashMap<>();
    /**
     * The compilation context with which this instance was created
     */
    public Context context;
    /**
     * A temporary reference to the instance of the nowarn collector for the context.
     */
    /*@ non_null */ public Nowarns nowarns;
    /**
     * A mode of the scanner that determines whether end of jml comment tokens are returned
     */
    public boolean returnEndOfCommentTokens = true;
    /**
     * A flag that, when true, causes all JML constructs to be ignored; it is
     * set on construction according to a command-line option.
     */
    protected boolean noJML = false;
    /**
     * Set to true internally while the scanner is within a JML comment
     */
    protected boolean jml = false;
    /**
     * The set of defined keys for identifying optional comments
     */
    /*@ NonNull */ protected Set<String> keys = new HashSet<>();
    /**
     * When jml is true, then (non-backslash) JML keywords are recognized if
     * jmlkeyword is true and are considered identifiers if jmlkeyword is false; this is set by the
     * parser according to whether non-backslash JML tokens should be recognized
     * in the current parser state (e.g. such tokens are not recognized while
     * within expressions). jmlkeyword is always set to true at the beginning of
     * JML comments.
     */
    protected boolean jmlkeyword = true;

    /**
     * The style of comment, either CommentStyle.LINE or
     * CommentStyle.BLOCK, set prior to the scanner calling processComment()
     */
    @Nullable
    protected CommentStyle jmlcommentstyle;

    /**
     * Valid after nextToken() and contains the next token if it is a JML token
     * and null if the next token is a Java token
     */
    @Nullable
    protected JmlTokenKind jmlTokenKind;
    protected int saved_bp;
    protected char saved_ch;
    private JmlToken jmlToken; // FIXME - does this need to be a field?

    /**
     * Creates a new tokenizer, for JML and Java tokens.<P>
     * <p>
     * The last character in the input array may be overwritten with an EOI character; if you
     * control the size of the input array, make it at least one character larger than necessary,
     * to avoid the overwriting or reallocating and copying the array.
     *
     * @param fac         The factory generating the scanner
     * @param input       The character buffer to scan
     * @param inputLength The number of characters to scan
     */
    //@ requires inputLength <= input.length;
    protected JmlTokenizer(JmlScanner.JmlFactory fac, char[] input, int inputLength) {
        super(fac, input, inputLength);
        context = fac.context;
        getKeys();
        registerDefaultJmlTokens();
    }

    /**
     * Creates a new tokenizer, for JML tokens.<P>
     *
     * @param fac    The factory generating the scanner
     * @param buffer The character buffer to scan
     */
    // @ requires fac != null && buffer != null;
    protected JmlTokenizer(JmlScanner.JmlFactory fac, CharBuffer buffer) {
        super(fac, buffer);
        context = fac.context;
        getKeys();
        registerDefaultJmlTokens();
    }

    protected void registerDefaultJmlTokens() {
        allTokens.putAll(DefaultJmlTokenKind.allTokens);
    }

    /**
     * Registers the given {@link com.sun.tools.javac.parser.Tokens.ITokenKind} for the given terminal symbol.
     *
     * @param terminal non-null terminal symbol
     * @param kind     a non-null  token kind
     * @return the old token kind of the terminal symbol
     */
    public Tokens.ITokenKind registerToken(@NonNull String terminal, @NonNull JmlTokenKind kind) {
        return allTokens.put(terminal, kind);
    }

    /**
     * Sets the set of optional comment keys from the command-lkine options
     */
    protected void getKeys() {
        keys.addAll(Utils.instance(context).commentKeys);
    }

    /**
     * Sets the jml mode, returning the old value -
     * used for testing to be able to test constructs that
     * are within a JML comment.
     *
     * @param j set the jml mode to this boolean value
     */
    public boolean setJml(boolean j) {
        boolean t = jml;
        jml = j;
        return t;
    }

    /**
     * Sets the keyword mode, returning the old value
     *
     * @param j the new value of the keyword mode
     */
    public boolean setJmlKeyword(boolean j) {
        boolean t = jmlkeyword;
        jmlkeyword = j;
        return t;
    }

    /**
     * The current set of conditional keys used by the tokenizer.
     */
    public Set<String> keys() {
        return keys;
    }

    public void saveReaderState() {
        saved_bp = reader.bp;
        saved_ch = reader.ch;
    }

    public void restoreReaderState() {
        reader.bp = saved_bp;
        reader.ch = saved_ch;
    }

    public void setReaderState(int bp) {
        reader.bp = bp;
        reader.ch = reader.buf[bp]; // FIXME - this is not unicode correct
    }

    public void setReaderState(int bp, char ch) {
        reader.bp = bp;
        reader.ch = ch;
    }


    // This is called whenever the Java (superclass) scanner has scanned a whole
    // comment. We override it in order to handle JML comments specially. The
    // overridden method returns and proceeds immediately to scan for the 
    // next Java token after the comment.
    // Here if the comment is indeed a JML comment, we reset the scanner to the
    // beginning of the comment, set jml to true, and let the scanner proceed
    // to scan the contents of the comment.
    @Override
    protected Tokens.Comment processComment(int pos, int endPos, CommentStyle style) {
        // endPos is one beyond the last character of the comment

        // The inclusive range pos to endPos-1 does include the opening and closing
        // comment characters.
        // It does not include line ending for line comments, so
        // an empty line comment can be just two characters.
        if (noJML || style == CommentStyle.JAVADOC) {
            return super.processComment(pos, endPos, style);
        }

        // Save the buffer positions in the super class
        // After a call of scanChar(), ch is the character at the bp
        // position in character buffer; if the buffer held a unicode
        // sequence, bp is at the end of the sequence and ch is the
        // translated character
        saveReaderState(); // This is the state after having read the comment that we are now processing

        // Note on scanChar - it is valid to call scanChar if
        // ch is not EOI; the last character of the input will be an EOI

        // Set the scanner to the beginning of the comment being processed
        // pos() points to the first / of the comment sequence (or to the
        // last character of the unicode sequence for that /)
        setReaderState(pos);

        int commentStart = pos;
        scanChar(); // the next / or *
        int ch = scanChar(); // The @, or a + or - if there are keys, or something else if it is not a JML comment
        int plusPosition = reader.bp;

        boolean someplus = false; // true when at least one + key has been read
        boolean foundplus = false; // true when a + key that is in the list of enabled keys has been read
        while ((ch = reader.ch) != '@') { // On the first iteration, this is the same ch as above.
            if (ch != '+' && ch != '-') {
                // Not a valid JML comment (ch is not @ or + or -), so just return
                // Restart after the comment we are currently processing
                restoreReaderState();
                return super.processComment(pos, endPos, style);
            }

            boolean isplus = ch == '+';
            ch = scanChar();
            if (ch == '@') {
                // Old -style //+@ or //-@ comments

                if (Options.instance(context).isSet("-Xlint:deprecation")) {
                    log.warning(new DiagnosticPositionSE(commentStart, plusPosition, reader.bp), "jml.deprecated.conditional.annotation");
                }

                // To be backward compatible at the moment,
                // quit for //-@, process the comment if //+@
                if (isplus) break;
                restoreReaderState();
                return super.processComment(pos, endPos, style);
            }
            if (isplus) someplus = true;
            // We might call nextToken here and look for an identifier,
            // but that could be a recursive call of nextToken, which might
            // be dangerous, so we use scanIdent instead
            if (!Character.isJavaIdentifierStart(ch)) {
                // Not a valid JML comment - just return
                // Restart after the comment
                restoreReaderState();
                return super.processComment(pos, endPos, style);
            }
            // Check for keys
            scanIdent(); // Only valid if ch is isJavaIdentifierStart; sets 'name'
            reader.sp = 0; // See the use of sp in UnicodeReader - if sp is not reset, then the
            // next identifier is appended to the key
            String key = name.toString(); // the identifier just scanned
            if (keys.contains(key)) {
                if (isplus) foundplus = true;
                else {
                    // negative key found - return - ignore comment for JML
                    restoreReaderState();
                    return super.processComment(pos, endPos, style);
                }
            }
        }
        if (!foundplus && someplus) {
            // There were plus keys but not the key we were looking for, so ignore JML comment
            // Restart after the comment
            restoreReaderState();
            return super.processComment(pos, endPos, style);
        }

        // Either there were no optional keys or we fiound the right ones, so continue to process the comment

        while (reader.ch == '@') {
            reader.scanChar();
        } // Gobble up all leading @s

        if (jml) {
            // We are already in a JML comment - so we have an embedded comment.
            // The action is to just ignore the embedded comment start
            // characters that we just scanned.

            // do nothing

        } else {

            // We initialize state and proceed to process the comment as JML text
            jmlcommentstyle = style;
            jml = true;
            jmlkeyword = true;
        }
        return null; // Tell the caller to ignore the comment - that is, to not consider it a regular comment
    }

    /**
     * Scans the next token in the character buffer; after this call, then
     * token() and jmlToken() provide the values of the scanned token. Also
     * pos() gives the beginning character position of the scanned token, and
     * endPos() gives (one past) the end character position of the scanned
     * token.
     * <p>
     * Both pos and endPos point to the end of a unicode sequence if the  // FIXME - validate this paragraph
     * relevant character is represented by a unicode sequence. The internal bp
     * pointer should be at endPos and the internal ch variable should contain
     * the following character.
     * <p>
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
        //   jmlkeyword - (if jml is true) whether to translate non-backslash 
        //                keywords as JML keywords or as Java identifiers
        // Responds with updates to that state as well as to
        //   jmlToken, jmlTokenKind, bp, ch, endPos, tk, name
        boolean initialJml = jml;
        int pos, endPos;
        while (true) { // The loop is just so we can easily restart with a 'continue' 
            jmlTokenKind = null;
            Token t = super.readToken(); // Sets tk, May modify jmlTokenKind
            pos = t.pos;
            endPos = t.endPos;
            // Note that the above may call processComment. If the comment is a JML comment, the
            // reader and tokenizer will be repointed to tokenize within the JML comment. This
            // may result in a CUSTOM Java token being produced with jmlTokenKind set, for example,
            // by calls down to methods such as scanOperator and scanIdent in this class.
            // So now we can produce a replacement token.

            // FIXME - what about doc comments in general?

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
                if (jmlTokenKind == DefaultJmlTokenKind.ENDJMLCOMMENT) {
                    jmlToken = new JmlToken(jmlTokenKind, t);
                    if (!returnEndOfCommentTokens || !initialJml) continue; // Go get next token
                    return jmlToken;
                } else {
                    return t; // A Java token
                }
            }

            if (jmlTokenKind == DefaultJmlTokenKind.NOWARN) {
                scanNowarn(reader.bp);  // FIXME - I doubt this is working after the Java 8 merge
                continue;
//            } else if (jmlTokenKind == DefaultJmlTokenKind.PRIMITIVE_TYPE) {
//                // finish and exit
            } else if (tk == TokenKind.STAR && reader.ch == '/'
                    && jmlcommentstyle == CommentStyle.BLOCK) {
                // We're in a BLOCK comment and we scanned a * and the next
                // character is a / so we are at the end of the comment
                scanChar(); // advance past the /
                jml = false;
                endPos = reader.bp;
                jmlTokenKind = DefaultJmlTokenKind.ENDJMLCOMMENT;
                if (!returnEndOfCommentTokens || !initialJml) continue;
            } else if (tk == TokenKind.MONKEYS_AT) {
                // This is just for the case that a terminating */ is preceded by one or more @s
                // JML allows this, but it just complicates scanning - I wish JML would deprecate that syntax
                int first = reader.bp;
                if (jmlcommentstyle == CommentStyle.BLOCK
                        && (reader.ch == '*' || reader.ch == '@')) {
                    // This may be the end of a BLOCK comment. We have seen a real @;
                    // there may be more @s and then the * and /
                    while (reader.ch == '@')
                        reader.scanChar(); // advances bp, ch is the character at bp; bp is end of unicode sequence
                    if (reader.ch != '*') {
                        // TODO - should really report this as a legal series
                        // of AT tokens
                        jmlError(first, reader.bp, "jml.unexpected.at.symbols");
                        return readToken();
                    } else {
                        reader.scanChar(); // consume *
                        if (reader.ch != '/') {
                            // TODO - should really report this as a legal
                            // series of AT tokens and a STAR
                            jmlError(first, reader.bp, "jml.at.and.star.but.no.slash");
                            return readToken();
                        } else {
                            reader.scanChar(); // consume /
                        }
                    }
                    tk = TokenKind.CUSTOM;
                    jmlTokenKind = DefaultJmlTokenKind.ENDJMLCOMMENT;
                    jml = false;
                    endPos = reader.bp;
                    if (!returnEndOfCommentTokens || !initialJml) continue;
                }
            } else if (tk == TokenKind.LPAREN && reader.ch == '*') {
                int start = reader.bp;
                reader.scanChar(); // skip the *
                outer:
                do {
                    while (reader.ch != '*') {
                        if ((jmlcommentstyle == CommentStyle.LINE && (reader.ch == '\n' || reader.ch == '\r')) || reader.ch == LayoutCharacters.EOI) {
                            // Unclosed informal expression
                            jmlError(start, reader.bp, "jml.unclosed.informal.expression");
                            break outer;
                        }
                        reader.putChar(reader.ch);
                        scanChar();
                    }
                    int star = reader.bp;
                    char ch = scanChar(); // skip the *
                    if ((jmlcommentstyle == CommentStyle.LINE && (ch == '\n' || ch == '\r')) || ch == LayoutCharacters.EOI) {
                        // Unclosed informal expression
                        jmlError(start, reader.bp, "jml.unclosed.informal.expression");
                        break outer;
                    }
                    if (jmlcommentstyle == CommentStyle.BLOCK && ch == '/') {
                        // Unclosed informal expression
                        jmlError(start, reader.bp, "jml.unclosed.informal.expression");
                        setReaderState(star, '*');
                        break outer;
                    }
                } while (reader.ch != ')');
                if (reader.ch == ')') scanChar();
                endPos = reader.bp;
                tk = TokenKind.CUSTOM;
                jmlTokenKind = DefaultJmlTokenKind.INFORMAL_COMMENT;
//            } else if (jmlTokenKind == DefaultJmlTokenKind.MODEL) {
//                int prevbp = reader.bp; // FIXME _ this is probably not working; check endPos
//                Token tt = super.readToken();
//                //docComment = dc;
//                if (jml && tt.kind == TokenKind.IMPORT) {
//                    jmlTokenKind = DefaultJmlTokenKind.MODEL;
//                } else {
//                    // Need to backtrack
//                    setReaderState(prevbp);
//                    tk = TokenKind.CUSTOM;
//                    jmlTokenKind = DefaultJmlTokenKind.MODEL;
//                }
            } else if (tk == TokenKind.LBRACE && reader.ch == '|') {
                tk = TokenKind.CUSTOM;
                jmlTokenKind = DefaultJmlTokenKind.SPEC_GROUP_START;
                scanChar();
                endPos = reader.bp;
            } else if (tk == TokenKind.BAR && reader.ch == '}') {
                tk = TokenKind.CUSTOM;
                jmlTokenKind = DefaultJmlTokenKind.SPEC_GROUP_END;
                reader.scanChar();
                endPos = reader.bp;
            } else if (tk == TokenKind.ERROR && reader.sp == 2 && reader.sbuf[0] == '.' && reader.sbuf[1] == '.') {
                jmlTokenKind = DefaultJmlTokenKind.DOT_DOT;
                endPos = reader.bp;
            }
            return jmlTokenKind == null ? t : new JmlToken(jmlTokenKind, TokenKind.CUSTOM, pos, endPos);
        }
    }

    /**
     * Overrides the Java scanner in order to catch situations in which the
     * first part of a double literal is immediately followed by a dot,
     * e.g. 123.. ; within JML, this should be an int followed by a DOT_DOT token
     */
    @Override
    public void scanFractionAndSuffix(int pos) {
        if (jml && reader.ch == '.') {
            reader.sp--;
            reader.bp--; // FIXME - not unicode safe // FIXME - adjust pos?
            tk = TokenKind.INTLITERAL;
        } else {
            super.scanFractionAndSuffix(pos);
        }
    }

    /**
     * This method presumes the NOWARN token has been read and handles the names
     * within the nowarn, reading through the terminating semicolon or end of JML comment
     */
    public void scanNowarn(int pos) {
        boolean prev = jmlkeyword;
        jmlkeyword = false;
        try {
            Token t = readToken();
            if (t.kind == TokenKind.SEMI || t.ikind == DefaultJmlTokenKind.ENDJMLCOMMENT) {
                // No labels - so this means suppress everything
                // Indicate this with null
                handleNowarn(log.currentSource(), pos, null);
            } else {
                while (t.kind != TokenKind.SEMI && t.ikind != DefaultJmlTokenKind.ENDJMLCOMMENT) {
                    if (t.kind != TokenKind.IDENTIFIER) {
                        // Bad statement or missing terminating semicolon
                        jmlError(t.pos, reader.bp, "jml.bad.nowarn");
                        // expected identifier
                        skipThroughChar(';');
                        return;
                    }
                    String label = reader.chars();
                    handleNowarn(log.currentSource(), reader.bp, label);
                    t = readToken();
                    if (t.kind == TokenKind.COMMA) {
                        t = readToken();
                    }
                }
            }
            if (jmlTokenKind == DefaultJmlTokenKind.ENDJMLCOMMENT) {
                log.warning(t.pos, "jml.nowarn.with.no.semicolon");
                // Here we are swallowing the end of comment - we normally 
                // expect that token in the stream. However if there is just a 
                // nowarn, the Java scanner will not expect a standalone ENDJMLCOMMENT
                // FIXME - check the case of //@ some JML stuff ; nowarn xx 
                // or with /*@  -- does this parse OK
            }
        } finally {
            jmlkeyword = prev;
        }
    }

    /**
     * This method is called internally when a nowarn lexical pragma is scanned;
     * it is called once for each label in the pragma.
     *
     * @param file  The file being scanned
     * @param pos   The 0-based character position of the label
     * @param label The label in the pragma
     */
    protected void handleNowarn(DiagnosticSource file, int pos, String label) {
        nowarns.addItem(file, pos, label);
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
    protected char scanChar() {
        reader.scanChar();
        return reader.ch;
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
        super.processLineTerminator(pos, endPos);
        if (jml) {
            if (jmlcommentstyle == CommentStyle.LINE) {
                jml = false;
                jmlTokenKind = DefaultJmlTokenKind.ENDJMLCOMMENT;
                if (returnEndOfCommentTokens) {
                    reader.ch = '@'; // Signals the end of comment to nextToken()
                    reader.bp--; // FIXME - not right for unicode
                }
            } else {
                // skip any whitespace followed by @ symbols
                while (Character.isWhitespace(reader.ch))
                    reader.scanChar();
                while (reader.ch == '@')
                    reader.scanChar();
            }
        }
    }

    /**
     * Called to find identifiers and keywords when a character that can start a
     * Java identifier has been scanned. We override so that when jml and
     * jmlkeyword are true,
     * we can convert identifiers to JML keywords, including converting assert
     * to the JML assert keyword.
     * Sets tk, name, jmlTokenKind
     */
    @Override
    protected void scanIdent() {
        super.scanIdent(); // Sets tk and name
        if (!jml || !jmlkeyword)  // FIXME _ in this case jmlTokenKind should be set to null?
            return;
        if (tk == TokenKind.IDENTIFIER) {
            String s = reader.chars();
            // TODO - we are just ignoring the redundantly suffixes
            if (s.endsWith("_redundantly")) {
                s = s.substring(0, s.length() - "_redundantly".length());
            }
            JmlTokenKind tt = allTokens.get(s);
            if (tt != null) {
                jmlTokenKind = tt;
                return;
            }
            // FIXME - can we count on jmlTokenKind to be null?
        } else if (tk == TokenKind.ASSERT) {
            jmlTokenKind = DefaultJmlTokenKind.ASSERT;
        }
    }

    /**
     * Called to scan an operator. We override to detect JML operators as well.
     * And also backslash tokens.
     */
    @Override
    protected void scanOperator() {
        if (jml && reader.ch == '\\') {
            // backslash identifiers get redirected here since a \ itself is an
            // error in pure Java - isSpecial does the trick
            int ep = reader.bp;
            reader.putChar(reader.ch); // include the backslash
            reader.scanChar();
            if (Character.isLetter(reader.ch)) {
                super.scanIdent();  // tk and name are set
                // assuming that token() is Token.IDENTIFIER
                String seq = reader.chars();
                JmlTokenKind t = DefaultJmlTokenKind.backslashTokens.get(seq);
                if (t != null) {
                    tk = TokenKind.CUSTOM;
                    jmlTokenKind = t;
                } else {
                    jmlError(ep, reader.bp, "jml.bad.backslash.token", seq);
                    // token is set to ERROR
                }
            } else {
                jmlError(ep, reader.bp, "jml.extraneous.backslash");
                // token is set to ERROR
            }
            return;
        }
        super.scanOperator();
        if (!jml) return; // not in JML - so we scanned a regular Java operator

        int endPos = reader.bp;
        TokenKind t = tk;
        if (tk == TokenKind.EQEQ) {
            if (reader.ch == '>') {
                reader.scanChar();
                endPos = reader.bp;
                tk = TokenKind.CUSTOM;
                jmlTokenKind = DefaultJmlTokenKind.IMPLIES; // ==>
            }
        } else if (t == TokenKind.LTEQ) {
            if (reader.ch == '=') {
                // At the last = of <==
                reader.scanChar();
                if (reader.ch == '>') {
                    tk = TokenKind.CUSTOM;
                    jmlTokenKind = DefaultJmlTokenKind.EQUIVALENCE; // <==>
                    reader.scanChar();
                    endPos = reader.bp;
                } else {
                    tk = TokenKind.CUSTOM;
                    jmlTokenKind = DefaultJmlTokenKind.REVERSE_IMPLIES; // <==
                    endPos = reader.bp;
                }
            } else if (reader.ch == '!') {
                int k = reader.bp; // Last character of the !
                reader.scanChar();
                if (reader.ch == '=') {
                    scanChar();
                    if (reader.ch == '>') {
                        tk = TokenKind.CUSTOM;
                        jmlTokenKind = DefaultJmlTokenKind.INEQUIVALENCE; // <=!=>
                        reader.scanChar();
                        endPos = reader.bp;
                    } else { // reset to the !
                        setReaderState(k, '!');
                    }
                } else {
                    setReaderState(k, '!');
                }
            }
        } else if (t == TokenKind.LT) {
            if (reader.ch == ':') {
                tk = TokenKind.CUSTOM;
                jmlTokenKind = DefaultJmlTokenKind.SUBTYPE_OF; // <:
                reader.scanChar();
                endPos = reader.bp;
            } else if (reader.ch == '-') {
                tk = TokenKind.CUSTOM;
                jmlTokenKind = DefaultJmlTokenKind.LEFT_ARROW; // <-
                reader.scanChar();
                endPos = reader.bp;
            } else if (reader.ch == '#') {
                tk = TokenKind.CUSTOM;
                jmlTokenKind = DefaultJmlTokenKind.LOCK_LT; // <#
                reader.scanChar();
                if (reader.ch == '=') {
                    jmlTokenKind = DefaultJmlTokenKind.LOCK_LE; // <#=
                    reader.scanChar();
                }
                endPos = reader.bp;
            }
//        } else if (tk == TokenKind.ARROW) {
//            // Java 8 has a token called ARROW - which was not present in Java 7
//            // FIXME - we will need to combine the two uses
//            jmlTokenKind = DefaultJmlTokenKind.RIGHT_ARROW;
//        } else if (tk == TokenKind.SUB) {
//            if (reader.ch == '>') {
//                tk = TokenKind.CUSTOM;
//                jmlTokenKind = DefaultJmlTokenKind.RIGHT_ARROW; // ->
//                reader.scanChar();
//                endPos = reader.bp;
//            }
        }
    }

    /**
     * Reads characters up to an EOI or up to and through the specified
     * character, which ever is first.
     *
     * @param c the character to look for
     */
    public void skipThroughChar(char c) {
        while (reader.ch != c && reader.ch != LayoutCharacters.EOI)
            reader.scanChar();
        if (reader.ch == c)
            reader.scanChar();
    }

    /**
     * Overrides in order to catch the error message that results from seeing just
     * a .. instead of . or ...
     */
    @Override
    protected void lexError(int pos, String key, Object... args) {
        if (reader.sp == 2 && "illegal.dot".equals(key) && reader.sbuf[0] == '.' && reader.sbuf[1] == '.') {
            tk = TokenKind.CUSTOM;
            jmlTokenKind = DefaultJmlTokenKind.DOT_DOT;
        } else {
            jmlError(pos, key, args);
        }
    }


    /**
     * Records a lexical error (no valid token) at a single character position,
     * the resulting token is an ERROR token.
     */
    protected void jmlError(int pos, String key, Object... args) {
        log.error(new DiagnosticPositionSE(pos, pos), key, args);
        tk = TokenKind.ERROR;
        jmlToken = null;
        jmlTokenKind = null;
        errPos(pos);
    }

    /**
     * Logs an error; the character range of the error is from pos up to
     * BUT NOT including endpos.
     */
    protected void jmlError(int pos, int endpos, String key, Object... args) {
        // FIXME - the endPos -1 is not unicode friendly - and actually we'd like to adjust the
        // positions of pos and endpos to correspond to appropriate unicode boundaries, here and in
        // the other jmlError method
        log.error(new DiagnosticPositionSE(pos, endpos - 1), key, args);
        tk = TokenKind.ERROR;
        jmlToken = null;
        errPos(pos);
    }

    /**
     * A derived class of DiagnosticPosition that allows for straightforward setting of the
     * various positions associated with an error message.
     */
    // FIXME - comment on relationship to unicode characters
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
        public int getEndPosition(EndPosTable endPosTable) {
            return end;// FIXME
        }

    }

//    public BasicComment<UnicodeReader> makeJavaComment(int pos, int endPos, CommentStyle style) {
//        char[] buf = reader.getRawCharacters(pos, endPos);
//        return new BasicComment<UnicodeReader>(new UnicodeReader(fac, buf, buf.length), style);
//    }


}
