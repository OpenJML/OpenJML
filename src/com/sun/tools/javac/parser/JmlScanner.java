// Copyright 2007-2011 by David R. Cok
package com.sun.tools.javac.parser;

import static com.sun.tools.javac.parser.Token.ERROR;

import java.nio.CharBuffer;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlOptionName;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.parser.Scanner.CommentStyle;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.JavacMessages;
import com.sun.tools.javac.util.LayoutCharacters;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Position;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.JCDiagnostic.SimpleDiagnosticPosition;

/* FIXME - oddities in the Scanner class
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
// FIXME - does not find JML annotations in Javadoc
/**
 * This class is an extension of the JDK scanner that scans JML constructs as
 * well. Note that it relies on some fields and methods of Scanner being
 * protected that are not declared protected in the current version of OpenJDK.
 * No other changes to Scanner are made, which does require a few complicating
 * workarounds in this code (and probably ought to be redesigned to be simpler
 * to understand and maintain).
 * 
 * @author David Cok
 */
public class JmlScanner extends DocCommentScanner {

    /**
     * This factory is used to generate instances of JmlScanner. There is
     * typically a new instance for each new file parsed. The Context is used to
     * have a consistent set of information across all files parsed within a
     * compilation task.
     */
    public static class JmlFactory extends ScannerFactory {

        /**
         * Not yet used - we'd like to use a different message factory for JML
         * messages than for Java messages.
         */
        protected JCDiagnostic.Factory jmlMessageFactory;

        /** The unique compilation context with which this factory was created */
        public Context                 context;

        /**
         * Creates a new factory that creates instances of JmlScanner
         * 
         * @param context
         *            The common context used for this whole compilation
         */
        protected JmlFactory(Context context) {
            super(context);
            this.context = context;
            jmlMessageFactory = new JCDiagnostic.Factory(JavacMessages
                    .instance(context), "jml");
        }

        /**
         * Call this to register this factory as the factory to be used for
         * scanners within this compilation context.
         * 
         * @param context
         *            The common compilation context
         */
        public static void preRegister(final Context context) {
            context.put(scannerFactoryKey,
                    new Context.Factory<ScannerFactory>() {
                        public ScannerFactory make() {
                            return new JmlScanner.JmlFactory(context);
                        }
                    });
        }

        /*
         * (non-Javadoc)
         * 
         * @seecom.sun.tools.javac.parser.Scanner.Factory#newScanner(java.lang.
         * CharSequence)
         */
        
        public Scanner newScanner(CharSequence input) {
            JmlScanner sc;
            if (input instanceof CharBuffer) {
                sc = new JmlScanner(this, (CharBuffer) input);
            } else {
                char[] array = input.toString().toCharArray();
                sc = (JmlScanner)newScanner(array, array.length, true);
            }
            sc.keys = Utils.instance(context).commentKeys;
            
            return sc;
        }

        /*
         * (non-Javadoc)
         * 
         * @see com.sun.tools.javac.parser.Scanner.Factory#newScanner(char[],
         * int, boolean)
         */
        @Override
        public Scanner newScanner(char[] input, int inputLength, boolean keepDocComments) {
            JmlScanner j = new JmlScanner(this, input, inputLength);
            j.noJML = JmlOptionName.isOption(context, JmlOptionName.NOJML);
            return j;
        }

        @Override
        public Scanner newScanner(CharSequence input, boolean keepDocComments) {
            JmlScanner j = new JmlScanner(this, CharBuffer.wrap(input));
            j.noJML = JmlOptionName.isOption(context, JmlOptionName.NOJML);
            return j;
        }

    }

    /**
     * A flag that, when true, causes all JML constructs to be ignored; it is
     * set on construction according to a command-line option.
     */
    public boolean          noJML      = false;

    /** Set to true internally while the scanner is within a JML comment */
    protected boolean       jml        = false;

    /** The set of keys for identifying optional comments */
    protected Set<Name>     keys;
    
    /**
     * When jml is true, then (non-backslash) JML keywords are recognized if
     * jmlkeyword is true and not if jmlkeyword is false; this is set by the
     * parser according to whether non-backslash JML tokens should be recognized
     * in the current parser state (e.g. such tokens are not recognized while
     * within expressions).
     */
    protected boolean       jmlkeyword = true;

    /**
     * Set by the scanner to the style of comment, either CommentStyle.LINE or
     * CommentStyle.BLOCK, prior to the scanner calling processComment()
     */
    protected CommentStyle  jmlcommentstyle;

    /** Valid after nextToken() and contains the next token if it is a JML token
     * and null if it is a Java token */
    //@ nullable
    protected JmlToken     jmlToken;

    /**
     * Creates a new scanner, but you should use JmlFactory.newScanner() to get
     * one, not this constructor.
     * 
     * @param fac
     *            The factory generating the scanner
     * @param input
     *            The character buffer to scan
     * @param inputLength
     *            The number of characters to scan from the buffer
     */
    // @ requires fac != null && input != null;
    // @ requires inputLength <= input.length;
    protected JmlScanner(ScannerFactory fac, char[] input, int inputLength) {
        super(fac, input, inputLength);
    }

    /**
     * Creates a new scanner, but you should use JmlFactory.newScanner() to get
     * one, not this constructor.
     * 
     * @param fac
     *            The factory generating the scanner
     * @param buffer
     *            The character buffer to scan
     */
    // @ requires fac != null && buffer != null;
    protected JmlScanner(ScannerFactory fac, CharBuffer buffer) {
        super(fac, buffer);
    }

    /**
     * Sets the jml mode - used for testing to be able to test constructs that
     * are within a JML comment.
     * 
     * @param j
     *            set the jml mode to this boolean value
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
    // method returns and proceeds immediately to scan for the next token. Thus
    // we have to trick it into seeing a token that is mapped into the
    // STARTJMLCOMMENT token - we use an @ token along with jml=true to signal
    // the start of the JML comment.
    @Override
    protected void processComment(CommentStyle style) {
        // The range pos() to endPos() does include the opening and closing
        // comment characters.
        // It does not include line ending for line comments, so
        // an empty line comment can be just two characters.
        if (noJML || style == CommentStyle.JAVADOC) {
            super.processComment(style);
            // log.noticeWriter.println("Processed " + docComment);
            return;
        }

        // Save the buffer positions in the super class
        int end = endPos();
        int bpend = bp;
        char chend = ch;

        // rescan the input
        bp = pos() - 1; // OK for unicode
        scanChar(); // the /
        scanChar(); // the next / or *
        if (bp >= end)
            return; // This can happen if there is a // right at the end of the line

        int k = bp;
        scanChar();
        if (ch == '+' || ch == '-') {   // FIXME - fix the following block to be robust against premature end-of-comment
            // Also accept //+@ as the beginning of a JML
            // annotation
            boolean someplus = ch == '+';
            boolean someminus = ch == '-';
            boolean foundplus = false;
            scanChar();
            if (ch == '@') {
                // no keys
                if (someminus) { // FIXME - use someplus in conjunction with a parsePlus option?
                    bp = bpend;
                    ch = chend;
                    super.processComment(style);
                    return;
                }
            }
            while (ch != '@') {
                if (!Character.isJavaIdentifierStart(ch)) {
                    // Not a valid JML comment - just return
                    // Restart at the end
                    bp = bpend;
                    ch = chend;
                    super.processComment(style);
                    return;
                }
                // Check for keys
                scanIdent();
                Name key = name();
                if (keys.contains(key)) {
                    if (ch == '+') foundplus = true;
                    else {
                        // negative key found - return
                        bp = bpend;
                        ch = chend;
                        super.processComment(style);
                        return;
                    }
                }
                if (ch != '+' && ch != '-') {
                    // Not a valid JML comment - just return
                    // Restart at the end
                    bp = bpend;
                    ch = chend;
                    super.processComment(style);
                    return;
                }
                if (ch == '+') someplus = true;
                else if (ch == '-') someminus = true;
                scanChar();
            }
            if (!foundplus && someplus && someminus) {
                // Restart at the end
                bp = bpend;
                ch = chend;
                super.processComment(style);
                return;
            }
        }

        // If there is not an '@' next, there is no JML comment
        if (ch != '@') {
            // Restart at the end
            bp = bpend;
            ch = chend;
            super.processComment(style);
            return;
        }

        while (ch == '@') {
            k = bp;
            scanChar();
        } // Gobble up all leading @s
        if (bp >= end) {
            bp = bpend;
            ch = chend;
            return; // Empty JML line comment - ignore
        }

        if (jml) {
            // We are already in a JML comment - so we have an embedded comment.
            // The action is to just ignore the embedded comment start
            // characters.
            
            // FIXME - make sure this is the desired behavior - test it
            return;
        }

        jmlcommentstyle = style;
        bp = k; // Backup one character, so we show an @ to signal the beginning
        // of the JML comment
        ch = '@';
        jml = true;
        return;
    }

    /**
     * Scans the next token in the character buffer; after this call, then
     * token() and jmlToken() provide the values of the scanned token. Also
     * pos() gives the beginning character position of the scanned token, and
     * endPos() gives (one past) the end character position of the scanned
     * token.
     * <P>
     * Note that one of the following holds at return from this method:<BR>
     * a) token() != CUSTOM && jmlToken() == null (a Java token)<BR>
     * b) token() == CUSTOM && jmlToken() != null (a JML token)<BR>
     * c) token() == IMPORT && jmlToken() == MODEL (the beginning of a model
     * import)<BR>
     */
    // TODO: We do quite a bit of hackery here to avoid changes in the Scanner.
    // We did however have to change some permissions, so perhaps we should have
    // bitten
    // the bullet and just combined all of this into a revised scanner. It would
    // have not made possible our goal of keeping changes in the javac code
    // minimal,
    // for maintenance reasons, but it would have made for a simpler and more
    // understandable and better designed JML scanner.
    @Override
    public void nextToken() {
        jmlToken = null;
        if (!jml) {
            // We're starting in Java land
            super.nextToken();
            String dc = docComment;
            // Possible situations at this point
            // a) token != CUSTOM, token != null, jmlToken == null, jml == false
            // (a Java token)
            // b) token == MONKEYS_AT, jml == true (STARTJMLTOKEN) - from
            // processComment
            // In case (b) we check whether
            // the next tokens are MODEL IMPORT - then set token=IMPORT
            // jmlToken=MODEL (and read the two tokens)

            // If jml has changed to true and the character scanned is an @
            // then we have just seen the beginning of a JML comment.
            if (jml && token() == Token.MONKEYS_AT) {
                token(Token.CUSTOM);
                jmlToken = JmlToken.STARTJMLCOMMENT;
                char prevch = ch;
                int prevbp = bp;
                int prevpos = _pos;
                int prevendpos = endPos();
                int first = bp;
                super.nextToken();
                while (jmlToken == JmlToken.NOWARN) {
                    scanNowarn();
                    // The scanner is just past the terminating semicolon
                    prevch = ch;
                    prevbp = bp;
                    prevpos = _pos;
                    prevendpos = endPos();
                    jmlToken = null;
                    super.nextToken();
                }
                docComment = dc;
                // TODO - do we need to check the commentstyle here?
                if (token() == Token.STAR && ch == '/') {
                    // We just saw a JML comment start, and now we
                    // are seeing a comment end. We will just ignore
                    // both of them. Note that we may have read a
                    // nowarn in between.
                    scanChar(); // read the slash
                    jml = false;
                    nextToken();
                    return;
//                } else if (jmlToken == JmlToken.REFINES) {
//                    token(Token.IMPORT); // A real hack to trick
//                    // importDeclaration into parsing
//                    // this
                } else if (jmlToken == JmlToken.MODEL) {
                    super.nextToken();
                    docComment = dc;
                    if (!jml) {
                        // TODO - what if it is a model variable or method or
                        // class that is not in a JML comment
                        // error - the entire model import statement must be in
                        // the JML comment
                        jmlError(_pos, "jml.illformed.model.import"); // TODO - end position
                        skipThroughChar(';');
                    } else if (token() == Token.IMPORT) {
                        jmlToken = JmlToken.MODEL;
                    } else {
                        // Need to backtrack
                        ch = prevch;
                        bp = prevbp;
                        _pos = prevpos;
                        endPos = prevendpos;
                        token(Token.CUSTOM);
                        jmlToken = JmlToken.STARTJMLCOMMENT;
                    }
                } else if (!jml && token() == Token.MONKEYS_AT) {
                    // We are possibly seeing the end of the comment. If so,
                    // it was an empty comment (except for possible nowarns).
                    // We ignore both the start and end and advance to the
                    // next token.
                    if (!jml && jmlcommentstyle == CommentStyle.LINE) {
                        // This is the end of a LINE comment
                        // jml is already false and we are seeing an @ character
                        // because processLineTermination did that to signal
                        // this
                        // code here. The @ symbol is not really in the input
                        // stream.
                        jml = false;
                        nextToken();
                    } else if (jmlcommentstyle == CommentStyle.BLOCK
                            && (ch == '*' || ch == '@')) {
                        // This is the end of a BLOCK comment. We have seen a
                        // real @; there may be more @s and then the * and /
                        while (ch == '@')
                            scanChar();
                        if (ch != '*') {
                            // FIXME - should really report this as a legal
                            // series of AT tokens
                            jmlError(first, bp - 1, "jml.unexpected.at.symbols");
                            nextToken(); // recursively try to find the next token
                            return;
                        } else {
                            scanChar();
                            if (ch != '/') {
                                // FIXME - should really report this as a legal
                                // series of AT tokens and a STAR
                                jmlError(first, bp - 1, "jml.at.and.star.but.no.slash");
                                nextToken();
                                return;
                            } else {
                                scanChar();
                            }
                        }
                        jml = false;
                        nextToken();
                    }
                } else if (token() == Token.ERROR) {
                    // Don't backtrack over the error token
                    // so leave ch and bp unchanged - they are the error
                    _pos = prevpos;
                    endPos = prevendpos;
                    jmlToken = JmlToken.STARTJMLCOMMENT;
                    token(Token.CUSTOM);
                } else {
                    ch = prevch;
                    bp = prevbp;
                    _pos = prevpos;
                    endPos = prevendpos;
                    jmlToken = JmlToken.STARTJMLCOMMENT;
                    token(Token.CUSTOM);
                }
            }
        } else {
            // We're starting in JML land
            super.nextToken();
            String dc = docComment;
            // We scanned a Java token. Here are the possible situations:
            // 1) jml==true, token!=null,CUSTOM, jmlToken==null -- a Java token
            // but the Java token might be the initial part of a Jml token
            // 2) jml==true, token==CUSTOM, jmlToken!=null -- a JmlToken
            // 3) jml==false, token=='@', jmlcommentstyle==LINE -- just ended a
            // line comment, need to
            // convert it to a ENDJMLCOMMENT
            // 4) jmlcommentstyle==BLOCK, ch=='*' -- possibly at the end of the
            // comment
            // 5) jmlcommentstyle==BLOCK, ch=='@', backslashseen=false --
            // possibly at the end of the comment
            // 6) token==DOT, jmlToken==DOT_DOT -- really saw a DOT_DOT
            // 7) jmlToken==MODEL, jml==true and next token is IMPORT - need to
            // report as a IMPORT with MODEL modifier
            //
            // Possible conversions of Java tokens to JML:
            // LPAREN STAR becomes INFORMAL_COMMENT
            // LBRACE BAR becomes SPEC_GROUP_START
            // BAR RBRACE becomes SPEC_GROUP_END
            // Operators - but this happens in scanOperator
            // EQEQ GT becomes IMPLIES
            // LTEQ EQ becomes REVERSE_IMPLIES
            // LT COLON becomes SUBTYPE_OF
            // LTEQ BAREQ GT becomes INEQUIVALENCE
            // LTEQ EQGT becomes EQUIVALENCE
            // LT SUB becomes LEFT_ARROW
            // SUB GT becomes RIGHT_ARROW
            //      
            // But we have to make some adjustments
            // for (a) JML operators that are continuations of Java operators,
            // (b) the end of a comment, and (c) JML backslash tokens
            while (jmlToken == JmlToken.NOWARN) {
                scanNowarn();
                jmlToken = null;
                super.nextToken();
            }
            if (token() == Token.STAR && ch == '/'
                    && jmlcommentstyle == CommentStyle.BLOCK) {
                // We're in a BLOCK comment and we scanned a * and the next
                // character is a / so we are at the end of the comment
                scanChar(); // advance past the /
                jml = false;
                token(Token.CUSTOM);
                jmlToken = JmlToken.ENDJMLCOMMENT;
                docComment = dc;
            } else if (token() == Token.MONKEYS_AT) {
            	int first = pos();
                if (!jml && jmlcommentstyle == CommentStyle.LINE) {
                    // This is the end of a LINE comment
                    // jml is already false and we are seeing an @ character
                    // because processLineTermination did that to signal this
                    // code here. The @ symbol is not really in the input
                    // stream.
                    token(Token.CUSTOM);
                    jmlToken = JmlToken.ENDJMLCOMMENT;
                    jml = false;
                    docComment = dc;
                } else if (jmlcommentstyle == CommentStyle.BLOCK
                        && (ch == '*' || ch == '@')) {
                    // This is the end of a BLOCK comment. We have seen a real
                    // @;
                    // there may be more @s and then the * and /
                    while (ch == '@')
                        scanChar();
                    if (ch != '*') {
                        // FIXME - should really report this as a legal series
                        // of AT tokens
                        jmlError(first, bp - 1, "jml.unexpected.at.symbols");
                        // TODO - bp-1 is not unicode safe
                        nextToken(); // recursively try to find the next
                        // token
                        return;
                    } else {
                        scanChar();
                        if (ch != '/') {
                            // FIXME - should really report this as a legal
                            // series of AT tokens and a STAR
                            jmlError(first, bp - 1, "jml.at.and.star.but.no.slash");
                            // TODO - bp-1 is not unicode safe
                            nextToken();
                            return;
                        } else {
                            scanChar();
                        }
                    }
                    token(Token.CUSTOM);
                    jmlToken = JmlToken.ENDJMLCOMMENT;
                    jml = false;
                    docComment = dc;
                }
            } else if (token() == Token.LPAREN && ch == '*') {
                // FIXME - improve this to handle unclosed comments before an
                // EOF or ENDJMLCOMMENT or line termination
                scanChar(); // skip the *
                do {
                    while (ch != '*') {
                        putChar(ch);
                        scanChar();
                    }
                    scanChar(); // skip the *
                } while (ch != ')');
                endPos = bp + 1; // OK for unicode
                scanChar();
                token(Token.CUSTOM);
                jmlToken = JmlToken.INFORMAL_COMMENT;
            } else if (jmlToken == JmlToken.MODEL) {
                char prevch = ch;
                int prevbp = bp;
                int prevpos = _pos;
                int prevendpos = endPos();
                super.nextToken();
                docComment = dc;
                if (!jml) {
                    jmlError(_pos, "jml.illformed.model.import"); // TODO - end position
                    skipThroughChar(';');
                    // FIXME - is this only true for model import statements?
                    // error - the entire model import statement must be in the
                    // JML comment
                } else if (token() == Token.IMPORT) {
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
            } else if (token() == Token.DOT && jmlToken == JmlToken.DOT_DOT) {
                _pos = _pos - 1; // NOT OK FOR UNICODE
                token(Token.CUSTOM);
            } else if (token() == Token.LBRACE && ch == '|') {
                endPos = bp + 1; // OK for unicode
                token(Token.CUSTOM);
                jmlToken = JmlToken.SPEC_GROUP_START;
                scanChar();
            } else if (token() == Token.BAR && ch == '}') {
                endPos = bp + 1; // OK for unicode
                token(Token.CUSTOM);
                jmlToken = JmlToken.SPEC_GROUP_END;
                scanChar();
            }
        }

        // if (Utils.jmldebug)
        // log.noticeWriter.println("NEXT TOKEN " + token() + " " +
        // (token()!=Token.CUSTOM?"":jmlToken) + " " + pos() + " " + endPos());
    }

    public void scanNowarn() {
        // int nowarnPos = pos();
        JavaFileObject file = log.currentSourceFile();
        while (ch == ' ' || ch == '\t' || ch == LayoutCharacters.FF)
            scanChar(); // skip spaces
        while (Character.isLetter(ch)) {
            int p = bp;
            do {
                scanChar();
            } while (Character.isLetter(ch));
            String label = String.valueOf(buf, p, bp - p); // TODO Check this
                                                           // for unicode
            handleNowarn(file, p, label);

            while (ch == ' ' || ch == '\t' || ch == LayoutCharacters.FF
                    || ch == ',')
                scanChar(); // skip spaces
            // The above allows 0, 1, or more commas. JML technically allows
            // exactly one.
            if ((jmlcommentstyle == CommentStyle.BLOCK && ch == '*' && buf[bp + 1] == '/')
                    || (jmlcommentstyle == CommentStyle.LINE && (ch == '\n' || ch == '\r'))) {
                log.warning(pos(), "jml.nowarn.with.no.semicolon");
                // End of comment - though not for unicode or for @*/
                // termination
                // but there is really supposed to be a semicolon anyway, so
                // this
                // is just for helpfulness
                return;
            }
        }
        if (ch != ';') {
            // Bad statement or missing terminating semicolon
            log.error(bp, "jml.bad.nowarn");
            // skip through a semicolon
            while (ch != ';' && ch != LayoutCharacters.EOI && ch != '\n'
                    && ch != '\r')
                scanChar();
        } else {
            scanChar();
        }
    }

    /**
     * This method is called internally when a nowarn lexical pragma is scanned;
     * it is called once for each label in the pragma. Implement it to do
     * something useful eventually. Now it is a noop.
     * 
     * @param file
     *            The file being scanned
     * @param pos
     *            The 0-based character position of the label
     * @param label
     *            The label in the pragma
     */
    protected void handleNowarn(JavaFileObject file, int pos, String label) {
        // log.noticeWriter.println("NOWARN " + nowarnPos + " " + label);
        // TODO - eventually do something here
    }

    /*
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

    /*
     * Overrides the superclass method in order to denote a backslash as
     * special. This lets scanOperator detect the JML backslash keywords.
     * Otherwise the backslash is reported as an illegal character. This does
     * not affect scanning literals or unicode conversion.
     */
    @Override
    protected boolean isSpecial(char ch) {
        if (ch == '\\')
            return true;
        return super.isSpecial(ch);
    }

    /*
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
                ch = '@'; // Signals the end of comment to nextToken()
                bp--; // FIXME - not right for unicode
            } else {
                // skip any whitespace followed by @ symbols
                while (Character.isWhitespace(ch))
                    scanChar();
                while (ch == '@')
                    scanChar();
                checkForDotDot();
            }
        }
    }

    @Override
    protected void processWhiteSpace() {
        super.processWhiteSpace();
        if (jml)
            checkForDotDot();
    }

    /**
     * The superclass scanner calls .. illegal. Ideally it would report two
     * separate DOT tokens, but since .. cannot occur in a Java program, we get
     * an error message. .. is legal JML, in the right context, so we have to do
     * some special stuff to preclude the super class from flagging this.
     */
    public void checkForDotDot() {
        if (ch == '.' && buf[bp + 1] == '.' && buf[bp + 2] != '.') {
            // FIXME - what if we are at the end of the input buffer
            // We have to do this before scanning a token, because the Java
            // scanner issues an error about ..
            _pos = bp;
            scanChar();
            jmlToken = JmlToken.DOT_DOT;
        }
    }

    /*
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
            Name n = name();
            String s = n.toString();
            // TODO - we are just ignoring the redundantly suffixes
            if (s.endsWith("_redundantly")) {
                s = s.substring(0, s.length() - "_redundantly".length());
            }
            s = s.intern();
            JmlToken tt = JmlToken.allTokens.get(s);
            if (tt != null) {
                token(Token.CUSTOM);
                jmlToken = tt;
                return;
            }

        } else if (t == Token.ASSERT) {
            token(Token.CUSTOM);
            jmlToken = JmlToken.ASSERT;
        }
    }

    /*
     * Called to scan an operator. We override to detect JML operators as well.
     * And also backslash tokens.
     */
    @Override
    protected void scanOperator() {
        if (jml && ch == '\\') {
            // backslash identifiers get redirected here since a \ itself is an
            // error in pure Java
            int ep = pos();
            scanChar();
            if (Character.isLetter(ch)) {
                super.scanIdent();
                // assuming that token() is Token.IDENTIFIER
                String s = ("\\" + name().toString()).intern();
                JmlToken t = JmlToken.backslashTokens.get(s);
                if (t != null) {
                    token(Token.CUSTOM);
                    jmlToken = t;
                    endPos = bp; // FIXME - not OK for unicode
                } else {
                    jmlError(ep, bp-1, "jml.bad.backslash.token", name().toString());
                    // TODO - bp-1 is not unicode safe
                    // token is set to ERROR
                }
            } else {
                jmlError(ep, bp-1, "jml.extraneous.backslash");
                // TODO - bp-1 is not unicode safe
                // token is set to ERROR
            }
            return;
        }
        super.scanOperator();
        endPos = bp; // FIXME - not OK for unicode
        if (!jml) return; // not in JML - so we scanned a regular Java operator
        
        Token t = token();
        if (t == Token.EQEQ) {
            if (ch == '>') {
                endPos = bp + 1; // OK for unicode
                scanChar();
                token(Token.EQ);
                jmlToken = JmlToken.IMPLIES; // ==>
            }
        } else if (t == Token.LTEQ) {
            if (ch == '=') {
                int kk = bp; // At the last = of <==
                scanChar();
                if (ch == '>') {
                    kk = bp; // At the last of >
                    token(Token.EQ);
                    jmlToken = JmlToken.EQUIVALENCE; // <==>
                    endPos = kk + 1; // OK for unicode
                    scanChar();
                } else {
                    token(Token.EQ);
                    jmlToken = JmlToken.REVERSE_IMPLIES; // <==
                    endPos = kk + 1; // OK for unicode
                }
            } else if (ch == '!') {
                int k = bp; // Last character of the !
                scanChar();
                if (ch == '=') {
                    scanChar();
                    if (ch == '>') {
                        int kk = bp;
                        token(Token.EQ);
                        jmlToken = JmlToken.INEQUIVALENCE; // <=!=>
                        endPos = kk + 1; // OK for unicode
                        scanChar();
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
                endPos = bp + 1;
                token(Token.CUSTOM);
                jmlToken = JmlToken.SUBTYPE_OF; // <:
                scanChar();
            } else if (ch == '-') {
                endPos = bp + 1;
                token(Token.CUSTOM);
                jmlToken = JmlToken.LEFT_ARROW; // <-
                scanChar();
            } else if (ch == '#') {
                endPos = bp + 1;
                token(Token.CUSTOM);
                jmlToken = JmlToken.LOCK_LT; // <#
                scanChar();
                if (ch == '=') {
                    endPos = bp + 1;
                    token(Token.CUSTOM);
                    jmlToken = JmlToken.LOCK_LE; // <#=
                    scanChar();
                }
            }
        } else if (t == Token.SUB) {
            if (ch == '>') {
                endPos = bp + 1;
                token(Token.CUSTOM);
                jmlToken = JmlToken.RIGHT_ARROW; // ->
                scanChar();
            }
        }
    }

    /**
     * Reads characters up to an EOI or up to and through the specified
     * character, which ever is first.
     * 
     * @param c
     *            the character to look for
     */
    public void skipThroughChar(char c) {
        while (ch != c && ch != LayoutCharacters.EOI)
            scanChar();
        if (ch == c)
            scanChar();
    }
    
    protected void lexError(int pos, String key, Object... args) {// DRC - changed from private to protected
        log.error(new DiagnosticPositionSE(pos,pos),key,args);
        token(com.sun.tools.javac.parser.Token.ERROR);
        errPos(pos);
    }


    // FIXME - would like to have errors
    // tagged as jml errors
    protected void jmlError(int pos, String key, Object... args) {
        //lexError(pos, key, args);
        
        log.error(new DiagnosticPositionSE(pos,pos+1),key,args);
        token(com.sun.tools.javac.parser.Token.ERROR);
        errPos(pos);
        
        // log.report(fac.jmlMessageFactory.error(log.source, log.wrap(pos),
        // key, args));
        // token(ERROR);
        // errPos(pos);
    }

    protected void jmlError(int pos, int endpos, String key, Object... args) {
        //lexError(pos, key, args);
        
        log.error(new DiagnosticPositionSE(pos,endpos),key,args);
        
        // log.report(fac.jmlMessageFactory.error(log.source, log.wrap(pos),
        // key, args));
        token(com.sun.tools.javac.parser.Token.ERROR);
        errPos(pos);
    }

    // Copied from com.sun.tools.javac.util.AbstractLog
    protected DiagnosticPosition wrap(int pos) {
        return (pos == Position.NOPOS ? null : new SimpleDiagnosticPosition(pos));
    }
    
    static public class DiagnosticPositionSE implements DiagnosticPosition {
        protected int begin;
        protected int preferred;
        protected int end;
        
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
            // TODO Auto-generated method stub
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
