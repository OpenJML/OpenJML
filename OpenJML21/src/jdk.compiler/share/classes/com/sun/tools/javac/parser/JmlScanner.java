/*
 * This file is part of the OpenJML project.
 * Author: David R. Cok
 */
package com.sun.tools.javac.parser;

import java.nio.CharBuffer;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.ext.LineAnnotationClauses.ExceptionLineAnnotation;
import org.jmlspecs.openjml.ext.Operators;

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
    public static class JmlScannerFactory extends ScannerFactory {

        /** The unique compilation context with which this factory was created */
        public Context                 context;

        /**
         * Creates a new factory that creates instances of JmlScanner; a new scanner
         * is used for each file being parsed.
         *
         * @param context The common context used for this whole compilation
         */
        public JmlScannerFactory(Context context) {
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
        			return new JmlScanner.JmlScannerFactory(context);
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
            return new JmlScanner(this, input, inputLength);
        }

        /** Creates a new scanner that scans the given input;
         * keepDocComments is ignored - it is effectively always true */
        @Override
        public JmlScanner newScanner(CharSequence input, boolean keepDocComments) {
            return new JmlScanner(this, CharBuffer.wrap(input));
        }
    }

    /** The compilation context */
    public Context context;

    /** A reference to the tokenizer being used */
    public JmlTokenizer jmltokenizer;

    /** Set to true internally while the scanner is within a JML comment */
    public boolean       jml() {
        return jmlForCurrentToken;
    }

    /**
     * Sets the jml mode - used for testing to be able to test constructs that
     * are within a JML comment.
     *
     * @param j set the jml mode to this boolean value
     */
    public void setJml(boolean j) {
        jmltokenizer.jml = j;
    }
    
    protected java.util.List<Boolean> savedJml = new java.util.LinkedList<Boolean>();
    
    protected boolean jmlForCurrentToken;
    
    /** Collects line annotations */
    public java.util.List<ExceptionLineAnnotation> lineAnnotations = new java.util.LinkedList<>();

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
    protected JmlScanner(JmlScannerFactory fac, char[] input, int inputLength) {
        super(fac, new JmlTokenizer(fac, input, inputLength, com.sun.tools.javac.main.JmlCompiler.instance(fac.context).noJML));
        context = fac.context;
        jmltokenizer = (JmlTokenizer)super.tokenizer;
    }

    /**
     * Creates a new scanner, but you should use JmlFactory.newScanner() to get
     * one, not this constructor.
     *
     * @param fac The factory generating the scanner
     * @param buffer The character buffer to scan
     */
    // @ requires fac != null && buffer != null;
    protected JmlScanner(JmlScannerFactory fac, CharBuffer buffer) {
        super(fac, new JmlTokenizer(fac, buffer, com.sun.tools.javac.main.JmlCompiler.instance(fac.context).noJML));
        context = fac.context;
        jmltokenizer = (JmlTokenizer)super.tokenizer;
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
    
    // A built-in debugging tool is to define the Env Var SCANNER, in which case all tokens are 
    // printed out as scanned. The fact that SCANNER is defined is cached here so it is not looked up
    // in the system properties map on every token. If you like both the declaration of scannerDebug
    // and the override of nextToken my be deleted for production code.
    public boolean scannerDebug = org.jmlspecs.openjml.Utils.debug("scanner");
    {
    	JavaTokenizer.scannerDebug = scannerDebug;
    }
    
    public Token advance() {
    	super.nextToken(); 
    	if (!savedJml.isEmpty()) {
            jmlForCurrentToken = savedJml.remove(0);
        } else {
        	jmlForCurrentToken = ((JmlTokenizer)tokenizer).jml();
        }
    	return token(0);
    }
    
    public static boolean isStartJml(Token t) {
        return (t instanceof JmlToken jt) && jt.jmlclausekind == Operators.startjmlcommentKind;
    }
    
    public boolean isEndJml() {
        return (token instanceof JmlToken jt) && jt.jmlclausekind == Operators.endjmlcommentKind;
    }
    
    @Override
    public void nextToken() {
    	outer: while(true) {
    		advance();
    		while (true) {
    			// The following logic concatenates consecutive JML annotations, if there is only ignorable material between them
    			while (jmlToken() != null && isEndJml()) {
    				var saved = prevToken();
    				var t0 = token(0);
    				var t1 = token(1);
    				if (scannerDebug) System.out.println("TOKEN AFTER ENDJML " + t0.toStringDetail() + " :: " + savedJml.get(0) + " " + t1.toStringDetail());
                    if (scannerDebug) System.out.println("LOOKAHEADS-Z " + t0.toStringDetail() + " :: " + savedTokens.size() + " " + savedJml.size() + " " + jmlForCurrentToken);
    				if (!savedJml.get(0)) break;
    				if (isStartJml(t1)) {
    					if (scannerDebug) System.out.println("SKIPPING START JML");
    					advance(); // gets the start token
    					advance(); // gets the next token, skipping the end and start combination
    					setPrevToken(saved); // But keep the previous token as if the end-start combination did not exist
    					continue;
    				}
    				break;
    			}
    			if (jmlForCurrentToken && isStartJml(token) && token(1).kind == TokenKind.IDENTIFIER 
    					&& org.jmlspecs.openjml.Extensions.allKinds.get(token(1).name().toString()) instanceof IJmlClauseKind.LineAnnotationKind) {
    				if (scannerDebug) System.out.println("See the beginning of a line annotation");
    				continue outer;
    			}
    			if (jmlForCurrentToken && token.kind == TokenKind.IDENTIFIER) { 
    				String id = token.name().toString();
    				IJmlClauseKind clk = org.jmlspecs.openjml.Extensions.allKinds.get(id);
                    if (scannerDebug) System.out.println("JMLSCAN " + id + " # " + clk + " " + token.toStringDetail());
    				if (clk instanceof IJmlClauseKind.LineAnnotationKind lak) {
    					lak.scan(token.pos, id, lak, this);
    					if (scannerDebug) System.out.println("Scanned a line annotation");
    	                if (jml() && !isEndJml()) continue; 
    					continue outer;
    				}
    			}
        		break outer;
    		}
    	}
    	if (scannerDebug) {
    		System.out.println("TOKEN " + Utils.isJML() + " " + jmlForCurrentToken + " " + token.toStringDetail());
    	}
    }

    public Token token(int lookahead) {
        if (lookahead == 0) {
            return super.token(0);
        } else {
            for (int i = savedTokens.size() ; i < lookahead ; i ++) {
                savedTokens.add(tokenizer.readToken());
                savedJml.add(((JmlTokenizer)tokenizer).jml());
                if (scannerDebug) System.out.println("LOOKAHEAD " + savedTokens.size() + " " + savedTokens.get(savedTokens.size()-1).toStringDetail() + " " + savedJml.size() + " " + savedJml.get(savedJml.size()-1));
            }
            return savedTokens.get(lookahead - 1);
        }
    }

//    // FIXME - is this still needed? is it correct?
//    public Token rescan() {
//        if (!jml()) return token;
//        int i = token.pos;
//        jmltokenizer.reset(i);
//        savedTokens.clear();
//        savedJml.clear();
//        nextToken();
//        return token;
//    }

    public String chars() {
        return jmltokenizer.chars();
    }

    public int currentPos() {
        return jmltokenizer.position();
    }

}
