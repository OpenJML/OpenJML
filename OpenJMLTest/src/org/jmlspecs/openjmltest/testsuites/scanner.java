package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.JmlTestSuite;

import static com.sun.tools.javac.parser.Tokens.*;
import static com.sun.tools.javac.parser.Tokens.TokenKind.*;
import static org.jmlspecs.openjml.ext.Operators.*;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;
import static org.jmlspecs.openjml.ext.AssignableClauseExtension.*;
import static org.jmlspecs.openjml.ext.SingletonExpressions.*;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlOptions;
import org.openjml.MockJavaFileObject;

import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.JmlToken;
import com.sun.tools.javac.parser.ParserFactory;
import com.sun.tools.javac.parser.Scanner;
import com.sun.tools.javac.parser.ScannerFactory;
import com.sun.tools.javac.parser.Tokens;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;

import static org.junit.Assert.*;
import org.junit.*;

import java.util.Locale;

import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;

// TODO - should test unicode, especially with multiple backslashes
// TODO - should test errPos for error tokens (is endPos set?)

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class scanner extends JmlTestSuite {

    final static IJmlClauseKind EJML = endjmlcommentKind;
    final static IJmlClauseKind SJML = startjmlcommentKind;
    final static IJmlClauseKind INFORMAL_COMMENT = informalCommentKind;
    
    ScannerFactory fac;
    
    String[] keys;
    
    boolean skip;
    boolean failHarness;
    
    // TODO - do we need to collect and compare System.out,err
    
    /** Initializes a fresh scanner factory for each test */
    @Override @org.junit.Before
    public void setUp() throws Exception {
        super.setUp(); // Sets up a main program, diagnostic collector
    	addOptions("--no-require-white-space");
        org.jmlspecs.openjml.Extensions.register(context);
        fac = ScannerFactory.instance(context);
        keys = null;
        print = false;
        skip = false;
        failHarness = false;
    }
    
    @Override @org.junit.After
    public void tearDown() throws Exception {
        super.tearDown();
        assertTrue("Test failed to check for diagnostic messages", checkedMessages);
    }

    /** This field and associated check are to cause an error if a test case does not call checkMessages() */
    public boolean checkedMessages = false;

    /** Checks that all of the collected messages match the data supplied
     * in the arguments.
     * @param a a sequence of expected values, alternating between error message and column numbers
     */
    public void checkMessages(/* nonnullelements */Object ... a) {
        checkedMessages = true;
        if (a.length == 0) {
            if (print || (!noExtraPrinting && 0 != 2*collector.getDiagnostics().size())) printDiagnostics();
            assertEquals("Saw wrong number of messages ",0,collector.getDiagnostics().size());
        } else {
            checkDiagnostics(a);
        }
    }

    /** This is a helper routine to check tests that are supposed to issue
     * JUnit test failures.
     * 
     * @param failureMessage The expected JUnit failure message
     * @param s The string to parse
     * @param list The tokens expected
     * @param positions The expected start and end positions for each token
     * @param numErrors The expected number of scanning errors
     */
    //@ requires positions != null && list != null ==> positions.length == list.length*2;
    public void helpFailure(String failureMessage, String s, Object[] list, /*@nullable*/ int[] positions, int numErrors) {
        boolean failed = false;
        try {
            if (skip) return;
            helpScanner(s,list,positions,numErrors);
        } catch (AssertionError a) {
            failed = true;
            assertEquals("Failure report wrong",failureMessage,a.getMessage()); // FIXME - is this really resolved incorrectly?
        } finally {
            checkedMessages = true; // to avoid the error from not checking
        }
        assertTrue("Test harness failed to report an error", failed);
    }


    /** This scans the input string and checks whether the tokens obtained
     * match those in the 'expected' array and whether the positions found
     * match those in the positions array and whether the number of
     * errors found is 0.  The positions array contains a start and end position
     * for each token.
     * <p>
     * THe 'expected' array contains either TokenKind or IJmlClauseKind
     */
    public void helpScanner(String s, Object[] expected, int[] positions) {
        helpScanner(s,expected,positions,0);
    }
    
    /** This scans the input string and checks whether the tokens obtained
     * match those in the list array and whether the positions found
     * match those in the positions array and whether the number of
     * errors found is the last argument.  The positions array contains a start and end position
     * for each token.
     */
    public void helpScanner(String s, Object[] expected, int[] positions, int numErrors) {
        try {
            if (failHarness) throw new IllegalArgumentException();
            Log.instance(context).useSource(new MockJavaFileObject(s) );
            JmlScanner sc = (JmlScanner)fac.newScanner(s, true);
            if (keys != null) {
                for (String k: keys) { JmlOptions.instance(context).commentKeys.add(k); }
            }
            int i = 0;
            while (i<expected.length) {
                sc.nextToken();
                if (print) out.println(sc.token() + " " + sc.jmlToken());
                Token e = sc.token();
                Object o = e.kind;
                if (e instanceof JmlToken jmlt) o = jmlt.jmlclausekind;
                try {
                    assertTrue("Unexpected token at position " + i + " expected: " + expected[i] + " actual: " + o 
                                + (" " + e.pos + " " + e.endPos), o == expected[i]); // Not using assertEquals because we want more information in the error report
                    if (positions != null && 2*i+1 < positions.length) {
                        assertEquals("pos for token " + i, positions[2*i], e.pos);
                        assertEquals("endpos for token " + i, positions[2*i+1], e.endPos);
                    }
                } catch (AssertionError ex) {
                    if (!noExtraPrinting) do {
                        sc.nextToken();
                        e = sc.token();
                        out.println((++i) + " : " + e.kind + (" " + e.pos + " " + e.endPos));
                    } while (e.kind != EOF);
                    throw ex;
                }
                i++;
            }
            sc.nextToken();
                // The test harness only reads scanner tokens while there are matches in 'expected'.
                // If the 'expected' list is too short, then the following assert fails.
            assertEquals("Scanner not at EOF (read " + i + " tokens):", TokenKind.EOF, sc.token().kind);
            if (collector.getDiagnostics().size() != numErrors && !noExtraPrinting) printDiagnostics();
            assertEquals("Saw wrong number of errors", numErrors, collector.getDiagnostics().size());
            if (positions != null) {
                assertEquals("Number of start/end locations should be double the number of tokens:", 2*i, positions.length);
            }
        } catch (Exception e) {
            // This is not expected to ever fail -- only if the scanner itself has an internal bug that causes an exception
            e.printStackTrace(out);
            fail("Exception thrown while processing test: " + e); // NOCOV: Does not show as covered because it always throws an error
        }
    }
    ////////////////////////////////////////////////////////////////////////
    ///

    /** This test is solely to add coverages of some otherwise untaken execution paths */
    @Test public void testHarnessA() {
        skip = true;
        testHarness12();
        testHarness13();
    }
    
    @Test public void testHarnessB() {
        for (int i = 0; i < 2; i++) {
            failHarness = i == 0; // Expecting a stack trace to be printed
            try {
                helpScanner("",new Object[]{},null);
            } catch (AssertionError ex) {
                assertEquals("Exception thrown while processing test: java.lang.IllegalArgumentException", ex.getMessage());
            }
        }
        checkMessages();
    }
    
    /** This tests that the test harness records if not enough tokens are listed */
    @Test public void testHarness1() {
        helpFailure("Scanner not at EOF (read 1 tokens): expected:<token.end-of-input> but was:<token.identifier>",
                "A A",new Object[]{IDENTIFIER},null,0);
    }
    
    /** This tests that the test harness records if too many tokens are listed */
    @Test public void testHarness2() {
        noExtraPrinting = true;
        helpFailure("Unexpected token at position 1 expected: token.identifier actual: token.end-of-input 1 1",
                "A",new Object[]{IDENTIFIER,IDENTIFIER},null,0);
    }
    
    /** This tests that the test harness records if too many tokens are listed */
    @Test public void testHarness2a() {
        print = true;
        var savedout = this.out;
        this.out = tempout; // FIXME - why do we use tempout in these tests
        try {
            helpFailure("Unexpected token at position 1 expected: token.identifier actual: token.end-of-input 1 1",
                "A",new Object[]{IDENTIFIER,IDENTIFIER},null,0);
        } finally {
            this.out = savedout;
        }
    }
    
    /** This tests that the test harness records if too many tokens are listed */
    @Test public void testHarness2b() {
        print = true;
        var savedout = this.out;
        this.out = tempout;
        try {
            helpFailure("Unexpected token at position 1 expected: token.identifier actual: token.end-of-input 1 1",
                "A",new Object[]{IDENTIFIER,IDENTIFIER,IDENTIFIER},null,0);
        } finally {
            this.out = savedout;
        }
    }
    
    /** This tests that the test harness records if a wrong token is listed */
    @Test public void testHarness3() {
        noExtraPrinting = true;
        helpFailure("Unexpected token at position 0 expected: public actual: token.identifier 0 1",
                "A",new Object[]{PUBLIC},null,0);
    }

    /** This tests that the test harness records if too many tokens are listed */
    @Test public void testHarness4() {
        noExtraPrinting = true;
        helpFailure("Unexpected token at position 2 expected: token.identifier actual: token.end-of-input 1 1",
                "A",new Object[]{IDENTIFIER,EOF,IDENTIFIER},null,0);
    }
    
    /** This tests that the test harness records if wrong start position is given */
    @Test public void testHarness5() {
        noExtraPrinting = true;
        helpFailure("pos for token 0 expected:<1> but was:<0>",
                "A",new Object[]{IDENTIFIER,EOF},new int[]{1,2,3,4},0);
    }
    
    /** This tests that the test harness fails if wrong end position is given */
    @Test public void testHarness6() {
        noExtraPrinting = true;
        helpFailure("endpos for token 0 expected:<2> but was:<1>",
                "A",new Object[]{IDENTIFIER,EOF},new int[]{0,2,3,4},0);
    }
    
    /** This tests that the test harness fails if wrong number of errors is given */
    @Test public void testHarness7() {
        noExtraPrinting = true;
        helpFailure("Saw wrong number of errors expected:<1> but was:<0>",
                "A",new Object[]{IDENTIFIER,EOF},new int[]{0,1,1,1},1);
    }
    
    /** This tests that the test harness fails if wrong number of errors is given */
    @Test public void testHarness7b() {
        noExtraPrinting = false;
        var savedout = this.out;
        this.out = tempout;
        try {
            helpFailure("endpos for token 0 expected:<2> but was:<1>",
                    "A B C",new Object[]{IDENTIFIER},new int[]{0,2},1);
        } finally {
            this.out = savedout;
        }
    }
    
    /** This tests that the test harness fails if wrong number of errors is given */
    @Test public void testHarness7a() {
        noExtraPrinting = false;
        var savedout = this.out;
        this.out = tempout;
        try {
            helpFailure("Saw wrong number of errors expected:<1> but was:<0>",
                    "A",new Object[]{IDENTIFIER,EOF},new int[]{0,1,1,1},1);
        } finally {
            this.out = savedout;
        }
    }
    
    /** This tests that the test harness fails if too few positions are given */
    @Test public void testHarness8() {
        helpFailure("Number of start/end locations should be double the number of tokens: expected:<4> but was:<1>",
                "A",new Object[]{IDENTIFIER,EOF},new int[]{0},0);
    }
    
    /** This tests that the test harness fails if too few positions are given */
    @Test public void testHarness9() {
        helpFailure("Number of start/end locations should be double the number of tokens: expected:<4> but was:<2>",
                "A",new Object[]{IDENTIFIER,EOF},new int[]{0,1},0);
    }
    
    /** This tests that the test harness fails if too few positions are given */
    @Test public void testHarness10() {
        helpFailure("Number of start/end locations should be double the number of tokens: expected:<4> but was:<0>",
                "A",new Object[]{IDENTIFIER,EOF},new int[]{},0);
    }
    
    /** This tests that the test harness fails if too many positions are given */
    @Test public void testHarness11() {
        helpFailure("Number of start/end locations should be double the number of tokens: expected:<4> but was:<7>",
                "A",new Object[]{IDENTIFIER,EOF},new int[]{0,1,1,1,4,5,6},0);
    }
    
    /** This tests that the test harness objects if given the wrong error message */
    @Test public void testHarness12() {
        noExtraPrinting = true;
        try {
            helpFailure("ZZZ",
                "A",new Object[]{ERROR},new int[]{0,1},0);
        } catch (AssertionError a) {
            assertEquals("Test Failure", 
                    "Failure report wrong expected:<[ZZZ]> but was:<[Unexpected token at position 0 expected: token.bad-symbol actual: token.identifier 0 1]>",
                    a.getMessage());
        }
    }
    
    /** This tests failure harness objects if no failulre occurs */
    @Test public void testHarness13() {
        try {
            helpFailure("Number of start/end locations (7) should be double the number of tokens (2)",
                "A",new Object[]{IDENTIFIER},new int[]{0,1},0);
        } catch (AssertionError a) {
            assertEquals("Test Failure", "Test harness failed to report an error", a.getMessage());
        }
    }
    
    //////////////////////////////////////////////////////////////////////

    /** Test scanning something very simple */
    @Test public void testSomeJava() {
        helpScanner("",new Object[]{},null);
        helpScanner("A",new Object[]{IDENTIFIER},new int[]{0,1});
        checkMessages();
    }
    
    /** Test some unicode */
    @Test public void testSomeUnicode() {
        helpScanner("\\u0041\\u0020\\u0041",  // A space A
                new Object[]{IDENTIFIER,IDENTIFIER},
                new int[]{0,6,12,18});
        checkMessages();
    }
    
    /** Test some unicode  - multiple u*/
    @Test public void testSomeUnicode2() {
        helpScanner("\\uuuu0041 A",
                new Object[]{IDENTIFIER,IDENTIFIER},
                null);  
        checkMessages();
    }

    /** Test some unicode  - first backslash is an error */
    @Test public void testSomeUnicode3() {
        helpScanner(
                " \\\\\\u0041 A",
                new Object[]{ERROR,ERROR,IDENTIFIER,IDENTIFIER},
                new int[]{1,2,2,3,3,9,10,11},
                2);
        checkMessages("/TEST.java:1: error: illegal character: '\\'",2
                ,"/TEST.java:1: error: illegal character: '\\'",3);  
    }
    
    /** Test some unicode  - first backslash is an error */
    @Test public void testSomeUnicode4() {
        helpScanner(
                " \\\\u0041 A",
                new Object[]{ERROR,ERROR,IDENTIFIER,IDENTIFIER},
                new int[]{1,2,2,3,3,8,9,10},
                2);
        checkMessages("/TEST.java:1: error: illegal character: '\\'",2
                ,"/TEST.java:1: error: illegal character: '\\'",3);  
    }
    
    /** Test some unicode  - first backslash is an error */
    @Test public void testSomeUnicode5() {
        helpScanner(
                "\\\\\\u0041 A",
                new Object[]{ERROR,ERROR,IDENTIFIER,IDENTIFIER},
                new int[]{0,1,1,2,2,8,9,10},
                2);
        checkMessages("/TEST.java:1: error: illegal character: '\\'",1
                ,"/TEST.java:1: error: illegal character: '\\'",2);  
    }
    
    /** Test some unicode  - first backslash is an error */
    @Test public void testSomeUnicode6() {
        helpScanner(
                "\\\\u0041 A",
                new Object[]{ERROR,ERROR,IDENTIFIER,IDENTIFIER},
                new int[]{0,1,1,2,2,7,8,9},
                2);
        checkMessages("/TEST.java:1: error: illegal character: '\\'",1
                ,"/TEST.java:1: error: illegal character: '\\'",2);  
    }
    
    /** Test some unicode  - first backslash is an error */
    @Test public void testSomeUnicode7() {
        helpScanner(
                "\\u0041 A",
                new Object[]{IDENTIFIER,IDENTIFIER},
                new int[]{0,6,7,8},
                0);
        checkMessages();
    }
    
    // This test gives test coverage for the situation in which a unicode character prematurely ends right at end of file
    // Note that illegal unicode characters in Strings and comments cause the containing file (e.g. this scanner.java file) to
    // fail to compile.  Instead use an array of chars as in the following test.
    @Test public void testUnicodeEndOfFile() {
        var chars = new char[] {'\\', 'u', '0' };
        var jfo = new MockJavaFileObject("A.java", String.valueOf(chars));
        Log.instance(main.context()).useSource(jfo); // So there is a source against which to issue the error message
        var scan = fac.newScanner(chars, 3, false);
        scan.nextToken();
        checkMessages("/A.java:1: error: illegal unicode escape", 4,3,3,3);
    }
    

    /** Tests that JML keywords are not found in Java */
    @Test public void testJmlKeywordsNotInJml() {
        helpScanner("requires ensures pure",
                new Object[]{IDENTIFIER,IDENTIFIER,IDENTIFIER,},
                new int[]{0,8,9,16,17,21});
        checkMessages();
    }
    
    /** Tests JML operators */
    @Test public void testOperators() {
        helpScanner("/*@ ==> <== <: <==> <=!=> <- */",
                new Object[]{SJML,impliesKind,reverseimpliesKind,subtypeofKind,equivalenceKind,inequivalenceKind,leftarrowKind,EJML},
                new int[]{0,3,4,7, 8,11, 12,14, 15,19, 20,25, 26,28, 29,31});
        checkMessages();
    }
    
    /** Tests the Java operators related to JML operators */
    @Test public void testOperators1() {
        helpScanner("/*@ ==  <=  <  */",
                new Object[]{SJML,EQEQ,LTEQ,LT,EJML},
                new int[]{0,3,4,6,8,10,12,13,15,17});
        checkMessages();
    }
    
    /** Tests JML operators when in Java land */
    @Test public void testOperators2() {
        helpScanner("    ==> <== <: <==> <=!=> ",
                new Object[]{EQEQ,GT, LTEQ,EQ, LT,COLON, LTEQ,EQ,GT, LTEQ,BANGEQ,GT},
                new int[]{4,6,6,7, 8,10,10,11, 12,13,13,14, 15,17,17,18,18,19, 20,22,22,24,24,25});
        checkMessages();
    }
    
    @Test public void testOperators3() {
        helpScanner("/*@ <<< <<<= <: <:= @ */",
                new Object[]{SJML,wfltKind,wfleKind,subtypeofKind,subtypeofeqKind, MONKEYS_AT,EJML},
                new int[]{0,3,4,7, 8,12, 13,15, 16,19, 20,21, 22,24});
        checkMessages();
    }
    @Test public void testBadOperator() {
        helpScanner("/*@ <=! + */",
                new Object[]{SJML,LTEQ,BANG,PLUS,EJML},
                new int[]{0,3,4,6,6,7,8,9,10,12});
        checkMessages();
    }

    @Test public void testBadOperator2() {
        helpScanner("/*@ <=!= + */",
                new Object[]{SJML,LTEQ,BANGEQ,PLUS,EJML},
                new int[]{0,3,4,6,6,8,9,10,11,13});
        checkMessages();
    }

    @Test public void testArrow() {  // Now a Java operator, but in JML context
        helpScanner("/*@ -> */",
                new Object[]{SJML,ARROW,EJML},
                new int[]{0,3,4,6,7,9});
        checkMessages();
    }

    @Test public void testArrow2() {  // Now a Java operator, in Java context
        helpScanner("    ->   ",
                new Object[]{ARROW},
                new int[]{4,6});
        checkMessages();
    }

    // NOTE: Using a text block to avoid having to escape characters    
    /** Test that a backslash token is found */
    @Test public void testBackslash() {
        helpScanner("/*@ \\result */",
                new Object[]{SJML,resultKind,EJML},
                null);
        checkMessages();
    }
    
    /** Test that two immediately consecutive backslash tokens are found */
    @Test public void testBackslash1() {
        helpScanner("/*@ \\result\\result */",
                new Object[]{SJML,resultKind,resultKind,EJML},
                null);
        checkMessages();
    }
    
    /** Test that backslash tokens are found immediately after a line termination */
    @Test public void testBackslash2() {
        helpScanner("/*@ \\result\n\\result*///",
                new Object[]{SJML,resultKind,resultKind,EJML},
                null);
        checkMessages();
    }
    
    /** Test that a backslash token without the backslash is a regular identifier */
    @Test public void testBackslash3() {
        helpScanner("/*@ \\result result*/",
                new Object[]{SJML,resultKind,IDENTIFIER,EJML},
                null);
        checkMessages();
    }
    
    /** Test for an invalid backslash identifier */
    @Test public void testBackslash5() {
        helpScanner("/*@ \\xyz result*/",
                new Object[]{SJML,ERROR,IDENTIFIER,EJML},
                null,
                1);
        checkMessages("/TEST.java:1: error: This backslash token is unknown: \\xyz",5);
    }

    /** Test for a JML backslash with no identifier */
    @Test public void testBackslash6() {
        helpScanner("/*@ \\ \\result*/",
                new Object[]{SJML,ERROR,resultKind,EJML},
                null,
                1);
        checkMessages("/TEST.java:1: error: A backslash in a JML comment expects to be followed by a valid identifier",5);
    }
    
    /** Test for empty character literal */
    @Test public void testEmptyCharLiteral() {
        helpScanner("''",
                new Object[]{ERROR,EOF},
                new int[] {0,2,2,2},
                1);
        checkMessages("/TEST.java:1: error: empty character literal",1);
    }
    

    /** Test for unclosed character literal */
    @Test public void testUnclosedCharLiteral() {
        helpScanner("'",
                new Object[]{ERROR,EOF},
                new int[] {0,1,1,1},
                1);
        checkMessages("/TEST.java:1: error: unclosed character literal",1);
    }

    /** Test for unclosed character literal */
    @Test public void testUnclosedCharLiteral2() {
        helpScanner("'\n",
                new Object[]{ERROR,EOF},
                new int[] {0,2,2,2},
                2);
        checkMessages("/TEST.java:1: error: illegal line end in character literal",1,
                "/TEST.java:1: error: unclosed character literal",1);
    }
    
    /** Test for unclosed character literal */
    @Test public void testIllegalOctal() {
        helpScanner("0_x",
                new Object[]{INTLITERAL,IDENTIFIER,EOF},
                new int[] {0,2,2,3,3,3},
                2);
        checkMessages("/TEST.java:1: error: illegal underscore",2,
                "/TEST.java:1: error: illegal underscore",2);
    }
    
    /** Test for underscores in literals */
    @Test public void testLegalUnderscore() {
        helpScanner("0_5",
                new Object[]{INTLITERAL,EOF},
                new int[] {0,3,3,3},
                0);
        checkMessages();
    }
    
    /** Test for underscores in literals */
    @Test public void testLegalUnderscore2() {
        helpScanner("0__5",
                new Object[]{INTLITERAL,EOF},
                new int[] {0,4,4,4},
                0);
        checkMessages();
    }
    
    // Intended to trigger JavaTokenizerL617 -- put that line is never executed because
    // illegal leading underscores are caught elsewhere before calling scanDigits
    @Test public void testIllegalLeadingUnderscore() {
        helpScanner("0x_05",
                new Object[]{INTLITERAL,EOF},
                new int[] {0,5, 5,5},
                1);
        checkMessages("/TEST.java:1: error: illegal underscore",3);
    }
    
    @Test public void testIllegalTrailingUnderscore() {
        helpScanner("0x05_",
                new Object[]{INTLITERAL,EOF},
                new int[] {0,5, 5,5},
                1);
        checkMessages("/TEST.java:1: error: illegal underscore",5);
    }
    

    /** Test an empty Java line comment */
    @Test public void testEmptyJavaComment() {
        helpScanner("//",
                new Object[]{},
                new int[]{});
        checkMessages();
    }

    /** Test a mismatched comment ending */
    @Test public void testMisMatchedJMLComment() {
        helpScanner("//@*/ requires",
                new Object[]{SJML,STAR,SLASH,IDENTIFIER,EOF},
                null);
        checkMessages();
    }

    /** Test an empty line comment */
    @Test public void testEmptyComment() {
        helpScanner("//\n//@requires",
                new Object[]{SJML,IDENTIFIER,EOF},
                null);
        checkMessages();
    }

    @Test public void testEmptyComment2() {
        helpScanner("/**/",
                new Object[]{EOF},
                new int[] {4,4},
                0);
        checkMessages();
    }
    
    @Test public void testEmptyJavdocComment() { // FIXME - why does this not execute line 1556 in JavaTokenizer
        helpScanner("/***********/",
                new Object[]{EOF},
                new int[] {13,13},
                0);
        checkMessages();
    }
    
    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment() {
        helpScanner("//@requires //@ requires",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,EOF},
                null);
        checkMessages();
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment3() {
        helpScanner("/*@requires /*@ requires */ public   */ public",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,EJML,PUBLIC,STAR,SLASH,PUBLIC,EOF},
                new int[] {0,3,3,11,16,24,25,27,28,34,37,38,38,39,40,46,46,46},
                1);
        checkMessages("/TEST.java:1: error: Block comments may not be embedded inside JML block comments",13);
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment4() {
        helpScanner("/*@requires //@ requires  \n requires */ public",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,IDENTIFIER,EJML,PUBLIC,EOF},
                new int[] {0,3,3,11,16,24,28,36,37,39,40,46,46,46});
        checkMessages();
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment2() {
        helpScanner("/*@requires //@ requires */ public",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,EJML,PUBLIC,EOF},
                null);
        checkMessages();
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment5() {
        helpScanner("//@requires /*@ requires\n public    */ public ",
                new Object[]{SJML,IDENTIFIER,EJML,PUBLIC,STAR, SLASH,PUBLIC,EOF},
                new int[] {0,3,3,11,24,25,26,32,36,37,37,38,39,45,46,46},
                1);
        checkMessages("/TEST.java:1: error: Embedded block comment must terminate within the JML line comment",13);
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment5R() {
        helpScanner("//@requires /*@ requires\r public    */ public ",
                new Object[]{SJML,IDENTIFIER,EJML,PUBLIC,STAR, SLASH,PUBLIC,EOF},
                new int[] {0,3,3,11,24,25,26,32,36,37,37,38,39,45,46,46},
                1);
        checkMessages("/TEST.java:1: error: Embedded block comment must terminate within the JML line comment",13);
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment5RN() {
        helpScanner("//@requires /*@ requires\r\npublic    */ public ",
                new Object[]{SJML,IDENTIFIER,EJML,PUBLIC,STAR, SLASH,PUBLIC,EOF},
                new int[] {0,3, 3,11, 24,26, 26,32, 36,37, 37,38, 39,45, 46,46},
                1);
        checkMessages("/TEST.java:1: error: Embedded block comment must terminate within the JML line comment",13);
    }

    /** Test an embedded Java comment */
    @Test public void testEmbeddedJavaComment() {
        helpScanner("//@requires // requires",
                new Object[]{SJML,IDENTIFIER,EOF},
                null);
        checkMessages();
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJavaComment2() {
        helpScanner("//@requires /* requires */ ensures ",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,EOF},
                new int[] {0,3,3,11,27,34,35,35});
        checkMessages();
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJavaComment3() { 
        helpScanner("//@requires /* ensures \n signals */ modifies ",
                new Object[]{SJML,IDENTIFIER,EJML,IDENTIFIER,STAR,SLASH,IDENTIFIER,EOF},
                new int[]{0,3,3,11,23,24,25,32,33,34,34,35,36,44,45,45},
                1);
        checkMessages("/TEST.java:1: error: Embedded block comment must terminate within the JML line comment",13);
    }

    /** Test an embedded Java comment */
    @Test public void testEmbeddedJavaComment4() {
        helpScanner("/*@requires // modifies \n ensures */ signals ",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,EJML,IDENTIFIER,EOF},
                new int[]{0,3,3,11,26,33,34,36,37,44,45,45});
        checkMessages();
    }

    /** Test an embedded Java comment (which ends a JML block comment) */
    @Test public void testEmbeddedJavaComment6() {
        helpScanner("/*@requires /* modifies \n ensures */ ensures */ signals ",
                new Object[]{SJML,IDENTIFIER,EJML,IDENTIFIER,STAR,SLASH,IDENTIFIER,EOF},
                new int[]{0,3,3,11,34,36,37,44,45,46,46,47,48,55,56,56},
                1);
        checkMessages("/TEST.java:1: error: Block comments may not be embedded inside JML block comments",13);
    }

    @Test public void testLineComment1() {
        helpScanner("//@ requires",new Object[]{SJML,IDENTIFIER,EOF},null);
        checkMessages();
    }

    // NOTE: The scanner absorbs ending whitespace into the EOF.
    @Test public void testLineComment2() {
        helpScanner("//@ requires\n",new Object[]{SJML,IDENTIFIER,EJML},null);
        checkMessages();
    }

    /** Test that a line comment ends with a NL character */
    @Test public void testLineComment3() {
        helpScanner("//@ requires\n ",
                new Object[]{SJML,IDENTIFIER,EJML},
                new int[]{0,3,4,12,12,13});
        checkMessages();
    }

    /** Test that a line comment ends with a CR character */
    @Test public void testLineComment4() {
        helpScanner("//@ requires\r ",
                new Object[]{SJML,IDENTIFIER,EJML},
                null);
        checkMessages();
    }

    /** Test that a line comment ends with a CR NL combination */
    @Test public void testLineComment5() {
        helpScanner("//@ requires\r\n",
                new Object[]{SJML,IDENTIFIER,EJML},
                null);
        checkMessages();
    }

    /** Test that JML identifiers are not found after a JML line comment ends*/
    @Test public void testLineComment6() {
        helpScanner("//@ requires\nrequires",
                new Object[]{SJML,IDENTIFIER,EJML,IDENTIFIER},
                null);
        checkMessages();
    }
    
    /** Test that an @ at the end of a line comment is found */
    @Test public void testLineComment7() {
        helpScanner("//@ requires @\n ",
                new Object[]{SJML,IDENTIFIER,MONKEYS_AT,EJML},
                null);
        checkMessages();
    }
    
    /** Test an empty line comment */
    @Test public void testLineComment8() {
        helpScanner("//\nrequires ",
                new Object[]{IDENTIFIER},
                null);
        checkMessages();
    }
    
    /** Test an empty JML line comment */
    @Test public void testLineComment9() {
        helpScanner("//@\nrequires ",
                new Object[]{SJML,EJML,IDENTIFIER},
                null);
        checkMessages();
    }
    
    /** Test an empty JML line comment */
    @Test public void testLineComment10() {
        helpScanner("//@@@@@\nrequires ",
                new Object[]{SJML,EJML,IDENTIFIER},
                new int[] {0,7,7,8,8,16});
        checkMessages();
    }
    
    /** Test a bad backslash */
    @Test public void testLineComment11() {
        helpScanner("//@@x\\@@@\nrequires ",
                new Object[]{SJML,IDENTIFIER,ERROR,MONKEYS_AT,MONKEYS_AT,MONKEYS_AT,EJML,IDENTIFIER},
                null,1);
        checkMessages("/TEST.java:1: error: A backslash in a JML comment expects to be followed by a valid identifier",6);
    }
    
    /** Test a bad backslash */
    @Test public void testLineComment11a() {
        helpScanner("//@@\\@x@@\nrequires ",
                new Object[]{SJML,ERROR,MONKEYS_AT,IDENTIFIER,MONKEYS_AT,MONKEYS_AT,EJML,IDENTIFIER},
                null,1);
        checkMessages("/TEST.java:1: error: A backslash in a JML comment expects to be followed by a valid identifier",5);
    }
    
    @Test public void testMultiLine() {
        helpScanner("/*@ requires\nrequires@*/",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,EJML},
                null);
        checkMessages();
    }

    @Test public void testMultiLine1() {
        helpScanner("/*@ requires\n  requires@*/",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,EJML},
                null);
        checkMessages();
    }

    @Test public void testMultiLine2() {
        helpScanner("/*@ requires\n@requires@*/",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,EJML},
                null);
        checkMessages();
    }

    @Test public void testMultiLine3() {
        helpScanner("/*@ requires\n@@@requires@*/",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,EJML},
                null);
        checkMessages();
    }

    @Test public void testMultiLine4() {
        helpScanner("/*@ requires\n @requires@*/",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,EJML},
                null);
        checkMessages();
    }

    @Test public void testMultiLine5() {
        helpScanner("/*@ requires\n  @@@requires@*/",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,EJML},
                null);
        checkMessages();
    }

    @Test public void testMultiLineError() {
        helpScanner("/*@ \\result\n  @@@\\xyz@*/",
                new Object[]{SJML,resultKind,ERROR,EJML,EOF},
                new int[]{0,3,4,11,17,21,21,24,24,24},
                1);
        checkMessages("/TEST.java:2: error: This backslash token is unknown: \\xyz",6);
    }

    @Test public void testInformalComment() {
        helpScanner("/*@ \\result(* requires *)*/",
                new Object[]{SJML,resultKind,INFORMAL_COMMENT,EJML},
                new int[]{0,3,4,11,11,25,25,27},
                0);
        checkMessages();
    }
    @Test public void testInformalComment2() {
        helpScanner("/*@ \\result(* requires *****)*/",
                new Object[]{SJML,resultKind,INFORMAL_COMMENT,EJML},
                new int[]{0,3,4,11,11,29,29,31},
                0);
        checkMessages();
    }
    
    @Test public void testInformalComment3() {
        helpScanner("/*@ \\result(* requires **** *)*/",
                new Object[]{SJML,resultKind,INFORMAL_COMMENT,EJML},
                new int[]{0,3,4,11,11,30,30,32},
                0);
        checkMessages();
    }
    

    // Testing an unclosed informal comment in a BLOCK comment
    @Test public void testInformalComment4() {
        helpScanner("/*@ \\result(* requires **** */",
                new Object[]{SJML,resultKind,INFORMAL_COMMENT,EJML},
                new int[]{0,3,4,11,11,28,28,30},
                1);
        checkMessages("/TEST.java:1: error: The informal expression is not closed",13);
    }
    
    // Testing an unclosed informal comment in a BLOCK comment
    @Test public void testInformalComment4a() {
        helpScanner("/*@ \\result(* requires *\n*** */",
                new Object[]{SJML,resultKind,INFORMAL_COMMENT,EJML},
                new int[]{0,3,4,11,11,29,29,31},
                1);
        checkMessages("/TEST.java:1: error: The informal expression is not closed",13);
    }
    
    // Testing an unclosed informal comment in an unclosed BLOCK comment
    @Test public void testInformalComment4b() {
        helpScanner("/*@ \\result(* requires *\n***  ",
                new Object[]{ERROR,EOF},
                new int[]{0,30,30,30},
                1);
        checkMessages("/TEST.java:1: error: unclosed comment",1);
    }
    
    // Testing an unclosed informal comment in a LINE comment
    @Test public void testInformalComment5() {
        helpScanner("//@ \\result(* requires **** \n public",
                new Object[]{SJML,resultKind,INFORMAL_COMMENT,EJML,PUBLIC,EOF},
                new int[]{0,3,4,11,11,28,28,29,30,36,36,36},
                1);
        checkMessages("/TEST.java:1: error: The informal expression is not closed",13);
    }
    
    // Testing an unclosed informal comment in a LINE comment
    @Test public void testInformalComment5a() {
        helpScanner("//@ \\result(* requires *****",
                new Object[]{SJML,resultKind,INFORMAL_COMMENT,EOF},
                new int[]{0,3,4,11,11,28,28,28},
                1);
        checkMessages("/TEST.java:1: error: The informal expression is not closed",13);
    }
    
    // Testing an unclosed informal comment in a LINE comment
    @Test public void testInformalComment6() {
        helpScanner("//@ \\result(* requires ***\"*) \" requires\n",
                new Object[]{SJML,resultKind,INFORMAL_COMMENT,ERROR,EJML},
                new int[]{0,3,4,11,11,29,30,40,40,41},
                1);
        checkMessages("/TEST.java:1: error: unclosed string literal",31);
    }
    
    // The following few tests have a different format because we want to test the
    // content of the literals -- which other tests do not do.
    // FIXME - add more tests of literals
    
    @Test public void testStringLiteral() {
        Scanner sc = fac.newScanner("\"\\tA\\\\B\"", true);
        sc.nextToken();
        assertEquals(STRINGLITERAL,sc.token().kind);
        assertEquals("\tA\\B",sc.token().stringVal());
        checkMessages();
    }
    
    @Test public void testCharLiteral() {
        Scanner sc = fac.newScanner("\'\\t\'", true);
        sc.nextToken();
        assertEquals(CHARLITERAL,sc.token().kind);
        assertEquals("\t",sc.token().stringVal());
        checkMessages();
    }
    
    @Test public void testIntLiteralWithUnderscore() {
        String v = "123_456";
        Scanner sc = fac.newScanner(v, true);
        sc.nextToken();
        assertEquals(INTLITERAL,sc.token().kind);
        assertEquals("123456",sc.token().stringVal());
        assertEquals(123456,Integer.parseInt(sc.token().stringVal()));
        checkMessages();
    }
    
    @Test public void testIntLiteralWithUnderscoreBin() {
        String v = "0b0101_1010";
        Scanner sc = fac.newScanner(v, true);
        sc.nextToken();
        assertEquals(INTLITERAL,sc.token().kind);
        assertEquals("01011010",sc.token().stringVal());
        assertEquals(90,Integer.parseInt(sc.token().stringVal(),2));
        checkMessages();
    }
    
    @Test public void testIntLiteralWithUnderscoreHex() {
        String v = "0xDE_AF";
        Scanner sc = fac.newScanner(v, true);
        sc.nextToken();
        assertEquals(INTLITERAL,sc.token().kind);
        assertEquals("DEAF",sc.token().stringVal());
        assertEquals(57007,Integer.parseInt(sc.token().stringVal(),16));
        checkMessages();
    }
    
    @Test public void testIntLiteralWithUnderscoreHexLong() {
        String v = "0xDEAF_DEAF";
        Scanner sc = fac.newScanner(v, true);
        sc.nextToken();
        assertEquals(INTLITERAL,sc.token().kind);
        assertEquals("DEAFDEAF",sc.token().stringVal());
        assertEquals(3736067759L,Long.parseLong(sc.token().stringVal(),16));
        checkMessages();
    }
    
    @Test public void testDotDot() {
        helpScanner("//@ ..",
                new Object[]{SJML,dotdotKind,EOF},
                new int[]{0,3,4,6,6,6},
                0);
        checkMessages();
    }
    
    @Test public void testDotDot2() {
        helpScanner("//@ modifies ..;",
                new Object[]{SJML,IDENTIFIER,dotdotKind,SEMI,EOF},
                null,
                0);
        checkMessages();
    }
    
    @Test public void testDotDot2a() {
        helpScanner("//@ 123..456;",
                new Object[]{SJML,INTLITERAL,dotdotKind,INTLITERAL,SEMI,EOF},
                null,
                0);
        checkMessages();
    }
    
    @Test public void testDotDot3() {
        helpScanner("//@ modifies a[b .. c];",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,LBRACKET,IDENTIFIER,dotdotKind,IDENTIFIER,RBRACKET,SEMI,EOF},
                null,
                0);
        checkMessages();
    }
 
    @Test public void testDotDot4() {
        helpScanner("//@ modifies a[0..4];",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,LBRACKET,INTLITERAL,dotdotKind,INTLITERAL,RBRACKET,SEMI,EOF},
                null,
                0);
        checkMessages();
    }
 
    @Test public void testDotDot4a() {
        helpScanner("//@ modifies a[0 ..4];",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,LBRACKET,INTLITERAL,dotdotKind,INTLITERAL,RBRACKET,SEMI,EOF},
                null,
                0);
        checkMessages();
    }
 
    @Test public void testDotDot5() {
        helpScanner("//@ modifies ..234;",
                new Object[]{SJML,IDENTIFIER,dotdotKind,INTLITERAL,SEMI,EOF},
                null,
                0);
        checkMessages();
    }
    
    @Test public void testDotDot6() {
        helpScanner("//@ modifies .234;",
                new Object[]{SJML,IDENTIFIER,DOUBLELITERAL,SEMI,EOF},
                null,
                0);
        checkMessages();
    }
    
    @Test public void testDotDot7() {
        helpScanner("//@ modifies 0.234;",
                new Object[]{SJML,IDENTIFIER,DOUBLELITERAL,SEMI,EOF},
                null,
                0);
        checkMessages();
    }
    
    @Test public void testDotDot8() {
        helpScanner("//@ modifies a[0. .4];",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,LBRACKET,DOUBLELITERAL,DOUBLELITERAL,RBRACKET,SEMI,EOF},
                null,
                0);
        checkMessages();
    }
 
    @Test public void testDotDot9() {
        helpScanner("//@ 0xApA\n ",
                new Object[]{SJML,DOUBLELITERAL,IDENTIFIER,EJML,EOF},
                null,
                1);
        checkMessages("/TEST.java:1: error: malformed floating-point literal",5);
    }
 
    @Test public void testDotDot10() {
        helpScanner("//@ 1.0eZ \n ",
                new Object[]{SJML,DOUBLELITERAL,IDENTIFIER,EJML,EOF},
                null,
                1);
        checkMessages("/TEST.java:1: error: malformed floating-point literal",5);
    }
 
    @Test public void testDotDot11() {
        helpScanner("//@ 0xA.0pZ\n ",
                new Object[]{SJML,DOUBLELITERAL,IDENTIFIER,EJML,EOF},
                null,
                1);
        checkMessages("/TEST.java:1: error: malformed floating-point literal",5);
    }
 
    @Test public void testDotDot12() {
        helpScanner("//@ 0xA.Z\n ",
                new Object[]{SJML,DOUBLELITERAL,IDENTIFIER,EJML,EOF},
                null,
                1);
        checkMessages("/TEST.java:1: error: malformed floating-point literal",5);
    }
    
    // FIXME - in some ConditionalKey and DotDot tests, the scanner reports an IDENTIFIER instead of a JML token. Why? 
 
    @Test public void testConditionalKey1() {
        helpScanner("//+POS@ requires\n  /*+POS@ requires */",
                new Object[]{EOF},
                null);
        checkMessages();
    }

    @Test public void testConditionalKey2() {
        helpScanner("//-NEG@ requires\n  /*-NEG@ requires */",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,EJML,EOF},
                null);
        checkMessages();
    }

    @Test public void testConditionalKey3() {
        keys = new String[]{"POS"};
        helpScanner("//+POS@ requires\n  /*+POS@ requires */",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,EJML,EOF},
                null);
        checkMessages();
    }

    @Test public void testConditionalKey4() {
        keys = new String[]{"NEG"};
        helpScanner("//-NEG@ requires\n  /*-NEG@ requires */",
                new Object[]{EOF},
                null);
        checkMessages();
    }

    @Test public void testConditionalKey5() {
        helpScanner("//-NEG+POS@ requires\n  /*-NEG+POS@ requires */",
                new Object[]{EOF},
                null);
        checkMessages();
    }

    @Test public void testConditionalKey6() {
        keys = new String[]{"POS"};
        helpScanner("//-NEG+POS@ requires\n  /*-NEG+POS@ requires */",
                new Object[]{SJML,IDENTIFIER,IDENTIFIER,EJML,EOF},
                null);
        checkMessages();
    }

    @Test public void testConditionalKey7() {
        keys = new String[]{"NEG"};
        helpScanner("//-NEG+POS@ requires\n  /*-NEG+POS@ requires */",
                new Object[]{EOF},
                null);
        checkMessages();
    }

    @Test public void testConditionalKey8() {
        keys = new String[]{"NEG","POS"};
        helpScanner("//-NEG+POS@ requires\n  /*-NEG+POS@ requires */",
                new Object[]{EOF},
                null);
        checkMessages();
    }

    @Test public void testConditionalKey9() {
    	Options.instance(context).put("-Xlint:deprecation","true");
        helpScanner("//+@ requires\n x  /*+@ requires */",
                new Object[]{SJML, IDENTIFIER, EJML, IDENTIFIER, SJML, IDENTIFIER, EJML, EOF},
                new int[] { 0,4, 5,13, 13,14, 15,16, 18,22, 23,31, 32,34, 34,34},
                2);
        checkMessages("/TEST.java:1: warning: [deprecated] The //+@ and //-@ annotation styles are deprecated - use keys instead",3
                ,"/TEST.java:2: warning: [deprecated] The //+@ and //-@ annotation styles are deprecated - use keys instead",7);
    }

    @Test public void testConditionalKey10() {
        addOptions("-Xlint:deprecation");
        helpScanner("//-@ requires\n  /*-@ requires */",
                new Object[]{EOF},
                null,
                2);
        checkMessages("/TEST.java:1: warning: [deprecated] The //+@ and //-@ annotation styles are deprecated - use keys instead",3
        		,"/TEST.java:2: warning: [deprecated] The //+@ and //-@ annotation styles are deprecated - use keys instead",5);
    }

    @Test public void testLeadingPosition() {
        helpScanner(" int //@@@@@ requires ",
                new Object[]{INT,SJML,IDENTIFIER},
                new int[] {1,4,5,12,13,21});
        checkMessages();
    }
    
    @Test public void testLeadingPosition2() {
        helpScanner(" int /*@@@@@ requires @@*/",
                new Object[]{INT,SJML,IDENTIFIER,EJML},
                new int[] {1,4,5,12,13,21,22,26});
        checkMessages();
    }
    
    @Test public void testUnexpectedAt() { // FIXME - no message?
        helpScanner("/*@ @ @*/",
                new Object[]{SJML,MONKEYS_AT,EJML},
                new int[] {0,3,4,5,6,9});
        checkMessages();
    }
    
    @Test public void testIllegalJavadoc() {
        helpScanner("/*@ /**  */ @*/",
                new Object[]{SJML,EJML,EOF},
                new int[] {0,3,12,15,15,15},
                1);
        checkMessages("/TEST.java:1: error: Javadoc comments are not permitted within JML comments", 5);
    }
    
    @Test public void testIgnoredInvalidComment() {
        helpScanner("/*5@ @*/",
                new Object[]{EOF},
                new int[] {8,8},
                0);
        checkMessages();
    }
    
    @Test public void testIgnoredInvalidComment2() {
        helpScanner("/*+5@ @*/",
                new Object[]{EOF},
                new int[] {9,9},
                0);
        checkMessages();
    }
    
    @Test public void testRequireWhiteSpace() {
        addOptions("--require-white-space");
        helpScanner("/*@requires@*/",
                new Object[]{EOF},
                new int[] {14,14},
                0);
        checkMessages();
    }
    
    @Test public void testEndingAts() {
        helpScanner("/*@ requires @@@@@@*/",
                new Object[]{SJML,IDENTIFIER, EJML,EOF},
                new int[] {0,3,4,12, 13,21, 21,21},
                0);
        checkMessages();
    }
    
    @Test public void testEndingBadAts() {
        helpScanner("/*@ requires @@@@@@ */",
                new Object[]{SJML,IDENTIFIER, EJML, EOF},
                new int[] {0,3, 4,12, 20,22, 22,22},
                1);
        checkMessages("/TEST.java:1: error: These @ symbols are illegal here", 15); // FIXME expected 14 instead of 15
    }
    
    @Test public void testEndingNoSlash() {
        helpScanner("/*@ requires @@@@@@* */",
                new Object[]{SJML, IDENTIFIER, EJML, EOF},
                new int[] {0,3, 4,12, 21,23, 23,23},
                1);
        checkMessages("/TEST.java:1: error: A sequence of @ symbols followed by a * is expected to be followed by a / to end the JML comment", 15); // FIXME expected 14 instead of 15
    }
    
    @Test public void testBadSymbol() {
        helpScanner("#",
                new Object[]{ERROR, EOF},
                new int[] {0,1, 1,1},
                1);
        checkMessages("/TEST.java:1: error: illegal character: '#'", 1);
    }
    
    @Test public void testOctalEscape() {
        helpScanner("'\\77' '\\100'",
                new Object[]{CHARLITERAL,CHARLITERAL,EOF},
                new int[] {0,5, 6,12, 12,12},
                0);
        checkMessages();
    }
    
    @Test public void testOctalEscape1() {
        helpScanner("'\\39'",
                new Object[]{ERROR,INTLITERAL,ERROR,EOF},
                new int[] {0,3, 3,4, 4,5, 5,5},
                2);
        checkMessages("/TEST.java:1: error: unclosed character literal", 1
                ,"/TEST.java:1: error: unclosed character literal",5);
    }
    @Test public void testOctalEscape2() {
        helpScanner("'\\109'",
                new Object[]{ERROR,INTLITERAL,ERROR,EOF},
                new int[] {0,4, 4,5, 5,6, 6,6},
                2);
        checkMessages("/TEST.java:1: error: unclosed character literal", 1
                ,"/TEST.java:1: error: unclosed character literal",6);
    }
    
    @Test public void testWSEscape() {
        helpScanner("'\\s'",
                new Object[]{CHARLITERAL,EOF},
                new int[] {0,4, 4,4},
                0);
        checkMessages();
    }
    
    @Test public void testIllegalEscapeChar() {
        helpScanner("'\\z'",
                new Object[]{ERROR,IDENTIFIER,ERROR,EOF},
                new int[] {0,2, 2,3, 3,4, 4,4},
                3);
        checkMessages("/TEST.java:1: error: illegal escape character",3
                ,"/TEST.java:1: error: unclosed character literal",1
                ,"/TEST.java:1: error: unclosed character literal",4);
    }
    
    // FIXME - this was intended to exercize the '\n' and '\r' block in JavaTokenizer L473 -- but it does not
    @Test public void testIllegalLineEnd() {
        helpScanner("'\\\\n'",
                new Object[]{ERROR,IDENTIFIER,ERROR,EOF},
                new int[] {0,3, 3,4, 4,5, 5,5},
                2);
        checkMessages(
                 "/TEST.java:1: error: unclosed character literal",1
                ,"/TEST.java:1: error: unclosed character literal",5);
    }
    
    @Test public void testOpenTextBlock() {
        helpScanner("\"\"\"   sd\n \"\"\"",
                new Object[]{ERROR,IDENTIFIER,ERROR,EOF},
                new int[] {0,6, 6,8, 10,13, 13, 13},
                2);
        checkMessages(
                 "/TEST.java:1: error: illegal text block open delimiter sequence, missing line terminator",7
                ,"/TEST.java:2: error: illegal text block open delimiter sequence, missing line terminator",5);
    }    
}
