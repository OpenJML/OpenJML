/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.parser;

import java.nio.CharBuffer;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.parser.Tokens.Comment.CommentStyle;
import com.sun.tools.javac.parser.Tokens.NamedToken;
import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.DiagnosticSource;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.LayoutCharacters;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
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

// FIXME - check the discussion above now that the Tokenizer has been refactored out?
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
public class JmlScanner extends Scanner {

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
         * keepDocComments is ignored (it is effectively always true)
         */
        @Override
        public JmlScanner newScanner(char[] input, int inputLength, boolean keepDocComments) {
            JmlScanner j = new JmlScanner(this, input, inputLength);
            init(j);
            return j;
        }

        /** Creates a new scanner that scans the given input;
         * keepDocComments is ignored - it is effectively always true */
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
            j.jmltokenizer.nowarns = Nowarns.instance(context);
        }

    }
    
    /** The compilation context */
    protected Context context;
    
    /** A reference to the tokenizer being used */
    protected JmlTokenizer jmltokenizer;
    
    /**
     * A flag that, when true, causes all JML constructs to be ignored; it is
     * set on construction according to a command-line option.
     */
    protected boolean       noJML      = false;

    /** The set of keys for identifying optional comments */
    /*@NonNull*/ protected Set<String>     keys;
    
    /** A mode of the scanner that determines whether end of jml comment tokens are returned */
    public boolean returnEndOfCommentTokens = true;
    
    /** Set to true internally while the scanner is within a JML comment */
    public boolean       jml() {
        return jmltokenizer.jml;
    }
    
    /**
     * Sets the jml mode - used for testing to be able to test constructs that
     * are within a JML comment.
     * 
     * @param j set the jml mode to this boolean value
     */
    public void setJml(boolean j) {
        jmltokenizer.setJml(j);
    }

    
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
        super(fac, new JmlTokenizer(fac, input, inputLength));
        context = fac.context;
        jmltokenizer = (JmlTokenizer)tokenizer;
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
        super(fac, new JmlTokenizer(fac, buffer));
        context = fac.context;
        jmltokenizer = (JmlTokenizer)tokenizer;
    }

    
    /** The current set of conditional keys used by the scanner.
     */
    public Set<String> keys() {
        return jmltokenizer.keys();
    }

    /**
     * Valid after nextToken()
     * 
     * @return the JML token for the most recent scan, null if the token is
     *         purely a Java token
     */
    //@ pure nullable
    public JmlToken jmlToken() {
        Token t = token();
        return t instanceof JmlToken ? (JmlToken)t : null;
    }
    
//    JmlToken DUMMY = new JmlToken(null,TokenKind.ERROR,0,0);
    
    public Token rescan() {
        if (!jml()) return token;
        int i = token.pos;
        jmltokenizer.setReaderState(i);
        savedTokens.clear();
        nextToken();
        return token;
    }
    
    public void setToken(Token token) {
        this.token = token;
    }
    
    public String chars() {
        return jmltokenizer.reader.chars();
    }
    
    public int currentPos() {
        return jmltokenizer.reader.bp; // FIXME - do we need to add an offset for where the annotation comment starts?
    }
    
}
