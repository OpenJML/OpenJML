package tests;
import static com.sun.tools.javac.parser.Token.*;
import static org.jmlspecs.openjml.JmlToken.*;

import org.jmlspecs.openjml.JmlToken;
import org.junit.Ignore;
import org.junit.Test;

import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.Scanner;
import com.sun.tools.javac.parser.ScannerFactory;
import com.sun.tools.javac.parser.Token;
import com.sun.tools.javac.util.Log;
import static org.junit.Assert.*;

// TODO - should test unicode, especially with multiple backslashes
// TODO - should test errPos for error tokens (is endPos set?)

public class scanner extends JmlTestCase {

    final static JmlToken EJML = ENDJMLCOMMENT;
    
    ScannerFactory fac;
    
    String[] keys;
    
    // TODO - do we need to collect and compare System.out,err
    
    /** Initializes a fresh scanner factory for each test */
    @Override
    public void setUp() throws Exception {
        super.setUp(); // Sets up a main program, diagnostic collector
        fac = ScannerFactory.instance(context);
        keys = null;
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
    public void helpFailure(String failureMessage, String s, Enum<? extends Enum<?>>[] list, /*@nullable*/ int[] positions, int numErrors) {
        boolean failed = false;
        try {
            helpScanner(s,list,positions,numErrors);
        } catch (AssertionError a) {
            failed = true;
            assertEquals("Failure report wrong",failureMessage,a.getMessage());
        }
        if (!failed) fail("Test harness failed to report an error");
    }


    /** This scans the input string and checks whether the tokens obtained
     * match those in the list array and whether the positions found
     * match those in the positions array and whether the number of
     * errors found is 0.  The positions array contains a start and end position
     * for each token.
     */
    public void helpScanner(String s, Enum<? extends Enum<?>>[] list, int[] positions) {
        helpScanner(s,list,positions,0);
    }
    
    /** This scans the input string and checks whether the tokens obtained
     * match those in the list array and whether the positions found
     * match those in the positions array and whether the number of
     * errors found is the last argument.  The positions array contains a start and end position
     * for each token.
     */
    public void helpScanner(String s, Enum<? extends Enum<?>>[] list, int[] positions, int numErrors) {
        try {
            Log.instance(context).useSource(new TestJavaFileObject(s) );
            Scanner sc = fac.newScanner(s, true);
            if (keys != null) {
                for (String k: keys) { ((JmlScanner)sc).keys().add(k); }
            }
            int i = 0;
            while (i<list.length) {
                sc.nextToken();
                if (print) System.out.println(sc.token() + " " + ((JmlScanner)sc).jmlToken());
                Enum<?> e = ((JmlScanner)sc).jmlToken();
                if (e == null) e = sc.token();
                if (e != list[i]) {
                    fail("Unexpected token at position " + i + " expected: " + list[i] + " actual: " + e );
                }
                if (positions != null && 2*i+1 < positions.length) {
                    assertEquals("pos for token " + i, positions[2*i], sc.pos());
                    assertEquals("endpos for token " + i, positions[2*i+1], sc.endPos());
                }
                i++;
            }
            sc.nextToken();
            if (sc.token() != Token.EOF) {
                fail("Scanner not at EOF: " + sc.token());
            }
            if (collector.getDiagnostics().size() != numErrors) {
                if (!noExtraPrinting) printDiagnostics();
                fail("Saw wrong number of errors: expected " + numErrors 
                        + " actual " + collector.getDiagnostics().size());
            }
            if (positions != null && 2*i != positions.length) fail("Number of start/end locations (" + (positions.length) + ") should be double the number of tokens (" + i + ")");
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }


    ////////////////////////////////////////////////////////////////////////
    
    /** Test scanning something very simple */
    @Test public void testSomeJava() {
        helpScanner("",new Enum<?>[]{},null);
        helpScanner("A",new Enum<?>[]{IDENTIFIER},new int[]{0,1});
    }
    
    /** Test some unicode */
    @Test public void testSomeUnicode() {
        helpScanner("\\u0041\\u0020\\u0041",
                new Enum<?>[]{IDENTIFIER,IDENTIFIER},
                new int[]{5,11,17,18});  // Current behavior but wrong - BUG - FIXME
                //new int[]{0,6,12,18}); // This is what it should be
    }
    
    /** Test some unicode  - multiple u*/
    @Test public void testSomeUnicode2() {
        helpScanner("\\uuuu0041 A",
                new Enum<?>[]{IDENTIFIER,IDENTIFIER},
                null);  
    }

    // FIXME - understand correct behavior here
    /** Test some unicode  - multiple backslash*/
    @Ignore
    @Test public void testSomeUnicode3() {
        helpScanner("\\\\u0041 A",new Enum[]{ERROR,IDENTIFIER,IDENTIFIER},
                new int[]{0,1,2,7,8,9});  
    }
    
    /** This tests that the test harness records if not enough tokens are listed */
    @Test public void testHarness1() {
        helpFailure("Scanner not at EOF: token.identifier",
                "A A",new Enum<?>[]{IDENTIFIER},null,0);
    }
    
    /** This tests that the test harness records if too many tokens are listed */
    @Test public void testHarness2() {
        helpFailure("Unexpected token at position 1 expected: token.identifier actual: token.end-of-input",
                "A",new Enum<?>[]{IDENTIFIER,IDENTIFIER},null,0);
    }
    
    /** This tests that the test harness records if a wrong token is listed */
    @Test public void testHarness3() {
        helpFailure("Unexpected token at position 0 expected: public actual: token.identifier",
                "A",new Enum<?>[]{PUBLIC},null,0);
    }

    /** This tests that the test harness records if too many tokens are listed */
    @Test public void testHarness4() {
        helpFailure("Unexpected token at position 2 expected: token.identifier actual: token.end-of-input",
                "A",new Enum<?>[]{IDENTIFIER,EOF,IDENTIFIER},null,0);
    }
    
    /** This tests that the test harness records if wrong start position is given */
    @Test public void testHarness5() {
        helpFailure("pos for token 0 expected:<1> but was:<0>",
                "A",new Enum<?>[]{IDENTIFIER,EOF},new int[]{1,2,3,4},0);
    }
    
    /** This tests that the test harness fails if wrong end position is given */
    @Test public void testHarness6() {
        helpFailure("endpos for token 0 expected:<2> but was:<1>",
                "A",new Enum<?>[]{IDENTIFIER,EOF},new int[]{0,2,3,4},0);
    }
    
    /** This tests that the test harness fails if wrong number of errors is given */
    @Test public void testHarness7() {
        noExtraPrinting = true;
        helpFailure("Saw wrong number of errors: expected 1 actual 0",
                "A",new Enum<?>[]{IDENTIFIER,EOF},new int[]{0,1,1,1},1);
    }
    
    /** This tests that the test harness fails if too few positions are given */
    @Test public void testHarness8() {
        helpFailure("Number of start/end locations (1) should be double the number of tokens (2)",
                "A",new Enum<?>[]{IDENTIFIER,EOF},new int[]{0},0);
    }
    
    /** This tests that the test harness fails if too few positions are given */
    @Test public void testHarness9() {
        helpFailure("Number of start/end locations (2) should be double the number of tokens (2)",
                "A",new Enum<?>[]{IDENTIFIER,EOF},new int[]{0,1},0);
    }
    
    /** This tests that the test harness fails if too few positions are given */
    @Test public void testHarness10() {
        helpFailure("Number of start/end locations (0) should be double the number of tokens (2)",
                "A",new Enum<?>[]{IDENTIFIER,EOF},new int[]{},0);
    }
    
    /** This tests that the test harness fails if too many positions are given */
    @Test public void testHarness11() {
        helpFailure("Number of start/end locations (7) should be double the number of tokens (2)",
                "A",new Enum<?>[]{IDENTIFIER,EOF},new int[]{0,1,1,1,4,5,6},0);
    }
    

    /** Tests that JML keywords are not found in Java */
    @Test public void testJmlKeywordsNotInJml() {
        helpScanner("requires ensures pure",
                new Enum<?>[]{IDENTIFIER,IDENTIFIER,IDENTIFIER,},
                new int[]{0,8,9,16,17,21});
    }
    
    /** Tests that JML keywords are found in a JML comment */
    @Test public void testJmlKeywordsInJml() {
        helpScanner("/*@requires ensures pure */",
                new Enum<?>[]{REQUIRES,ENSURES,PURE,EJML,},
                new int[]{3,11,12,19,20,24,25,27});
    }
    
    /** Tests that JML keywords are found in a JML comment */
    @Test public void testJmlKeywordsInJmlA() {
        helpScanner("//@requires ensures pure \n ",
                new Enum<?>[]{REQUIRES,ENSURES,PURE,EJML,EOF},
                new int[]{3,11,12,19,20,24,25,26,27,27});
    }
    
    /** Tests that JML keywords are found in a JML comment with nowarn */
    @Test public void testJmlKeywordsInJmlWithNoWarn() {
        helpScanner("/*@nowarn A; nowarn B,requires,C; requires ensures pure */",
                new Enum<?>[]{REQUIRES,ENSURES,PURE,EJML,},
                new int[]{34,42,43,50,51,55,56,58});
    }
    
    /** Tests that JML keywords are not found in a Java comment */
    @Test public void testJmlKeywordsNotInJavaComment() {
        helpScanner("/* requires */ /*@requires */",
                new Enum<?>[]{REQUIRES,EJML,},
                new int[]{18,26,27,29});
    }
    
    /** Tests that JML keywords are not found after a JML comment ends */
    @Test public void testJmlKeywordsAfterJml() {
        helpScanner("/*@requires */requires ensures pure",
                new Enum<?>[]{REQUIRES,EJML,IDENTIFIER,IDENTIFIER,IDENTIFIER,},
                new int[]{3,11,12,14,14,22,23,30,31,35});
    }
    
    /** Tests JML operators */
    @Test public void testOperators() {
        helpScanner("/*@ ==> <== <: <==> <=!=> -> <- */",
                new Enum<?>[]{IMPLIES,REVERSE_IMPLIES,SUBTYPE_OF,EQUIVALENCE,INEQUIVALENCE,RIGHT_ARROW,LEFT_ARROW,EJML},
                new int[]{4,7, 8,11, 12,14, 15,19, 20,25, 26,28, 29,31, 32,34});
    }
    
    /** Tests the Java operators related to JML operators */
    @Test public void testOperators1() {
        helpScanner("/*@ ==  <=  <  */",
                new Enum<?>[]{EQEQ,LTEQ,LT,EJML},
                new int[]{4,6,8,10,12,13,15,17});
    }
    
    /** Tests JML operators when in Java land */
    @Test public void testOperators2() {
        helpScanner("    ==> <== <: <==> <=!=> ",
                new Enum<?>[]{EQEQ,GT, LTEQ,EQ, LT,COLON, LTEQ,EQ,GT, LTEQ,BANGEQ,GT},
                new int[]{4,6,6,7, 8,10,10,11, 12,13,13,14, 15,17,17,18,18,19, 20,22,22,24,24,25});
    }
    
    @Test public void testBadOperator() {
        helpScanner("/*@ <=! + */",
                new Enum<?>[]{LTEQ,BANG,PLUS,EJML},
                new int[]{4,6,6,7,8,9,10,12});
    }

    @Test public void testBadOperator2() {
        helpScanner("/*@ <=!= + */",
                new Enum<?>[]{LTEQ,BANGEQ,PLUS,EJML},
                new int[]{4,6,6,8,9,10,11,13});
    }

    // NOTE:  In the test strings, backslash characters must be escaped.  So
    // within the string you write \\result, not \result, to get the effect of
    // \result in a test program.
    
    /** Test that a backslash token is found */
    @Test public void testBackslash() {
        helpScanner("/*@ \\result */",
                new Enum<?>[]{BSRESULT,EJML},
                null);
    }
    
    /** Test that two immediately consecutive backslash tokens are found */
    @Test public void testBackslash1() {
        helpScanner("/*@ \\result\\result */",
                new Enum<?>[]{BSRESULT,BSRESULT,EJML},
                null);
    }
    
    /** Test that backslash tokens are found immediately after a line termination */
    @Test public void testBackslash2() {
        helpScanner("/*@ \\result \n\\result*/",
                new Enum<?>[]{BSRESULT,BSRESULT,EJML},
                null);
    }
    
    /** Test that a backslash token without the backslash is a regular identifier */
    @Test public void testBackslash3() {
        helpScanner("/*@ \\result result*/",
                new Enum<?>[]{BSRESULT,IDENTIFIER,EJML},
                null);
    }
    
    /** Test for an invalid backslash identifier */
    @Test public void testBackslash5() {
        helpScanner("/*@ \\xyz result*/",
                new Enum<?>[]{ERROR,IDENTIFIER,EJML},
                null,
                1);
        checkMessages(new String[]{"/TEST.java:1: This backslash token is unknown: \\xyz"},
                      new int[]{5});
    }

    /** Test for a JML backslash with no identifier */
    @Test public void testBackslash6() {
        helpScanner("/*@ \\ \\result*/",
                new Enum<?>[]{ERROR,BSRESULT,EJML},
                null,
                1);
        checkMessages("/TEST.java:1: A backslash in a JML comment expects to be followed by a valid identifier",5);
    }
    

    /** Test an empty Java line comment */
    @Test public void testEmptyJavaComment() {
        helpScanner("//",
                new Enum<?>[]{},
                new int[]{});
    }

    /** Test a mismatched comment ending */
    @Test public void testMisMatchedJMLComment() {
        helpScanner("//@*/ requires",
                new Enum<?>[]{STAR,SLASH,REQUIRES,EOF},
                null);
    }

    /** Test an empty JML line comment */
    @Test public void testEmptyJMLComment() {
        helpScanner("//\n//@requires",
                new Enum<?>[]{REQUIRES,EOF},
                null);
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment() {
        helpScanner("//@requires //@ requires",
                new Enum<?>[]{REQUIRES,REQUIRES,EOF},
                null);
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment3() {
        helpScanner("/*@requires /*@ requires */ requires */ public",
                new Enum<?>[]{REQUIRES,REQUIRES,EJML,IDENTIFIER,STAR,SLASH,PUBLIC,EOF},
                null);
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment4() {
        helpScanner("/*@requires //@ requires  \n requires */ public",
                new Enum<?>[]{REQUIRES,REQUIRES,REQUIRES,EJML,PUBLIC,EOF},
                null);
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment2() {
        helpScanner("/*@requires //@ requires */ public",
                new Enum<?>[]{REQUIRES,REQUIRES,EJML,PUBLIC,EOF},
                null);
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJMLComment5() {
        helpScanner("//@requires /*@ requires\n requires */ requires",
                new Enum<?>[]{REQUIRES,REQUIRES,EJML,IDENTIFIER,STAR, SLASH,IDENTIFIER,EOF},
                null);
    }

    /** Test an embedded Java comment */
    @Test public void testEmbeddedJavaComment() {
        helpScanner("//@requires // requires",
                new Enum<?>[]{REQUIRES,EOF},
                null);
    }

    /** Test an embedded JML comment */
    @Test public void testEmbeddedJavaComment2() {
        helpScanner("//@requires /* requires */ ensures ",
                new Enum<?>[]{REQUIRES,ENSURES,EOF},
                null);
    }

    /** Test an embedded JML comment */
    // TODO: DO we really want this to work?
    @Ignore
    @Test public void testEmbeddedJavaComment3() { 
        helpScanner("//@requires /* requires ensures \n signals */ modifies ",
                new Enum<?>[]{REQUIRES,ASSIGNABLE,EOF},
                new int[]{3,11,45,53,54,54});
    }

    /** Test an embedded Java comment */
    @Test public void testEmbeddedJavaComment4() {
        helpScanner("/*@requires // modifies \n ensures */ signals ",
                new Enum<?>[]{REQUIRES,ENSURES,EJML,IDENTIFIER,EOF},
                new int[]{3,11,26,33,34,36,37,44,45,45});
    }

    /** Test an embedded Java comment */
    @Ignore
    @Test public void testEmbeddedJavaComment6() {
        // TODO: DO we really want this to work?
        helpScanner("/*@requires /* modifies \n ensures */ requires */ signals ",
                new Enum<?>[]{REQUIRES,IDENTIFIER,STAR,SLASH,IDENTIFIER,EOF},
                null);
    }

    @Test public void testLineComment1() {
        helpScanner("//@ requires",new Enum<?>[]{REQUIRES,EOF},null);
    }

    // NOTE: The scanner absorbs ending whitespace into the EOF.
    @Test public void testLineComment2() {
        helpScanner("//@ requires\n",new Enum<?>[]{REQUIRES,EOF},null);
    }

    /** Test that a line comment ends with a NL character */
    @Test public void testLineComment3() {
        helpScanner("//@ requires\n ",
                new Enum<?>[]{REQUIRES,EJML},
                new int[]{4,12,12,13});
    }

    /** Test that a line comment ends with a CR character */
    @Test public void testLineComment4() {
        helpScanner("//@ requires\r ",
                new Enum<?>[]{REQUIRES,EJML},
                null);
    }

    /** Test that a line comment ends with a CR NL combination */
    @Test public void testLineComment5() {
        helpScanner("//@ requires\r\n",
                new Enum<?>[]{REQUIRES,EJML},
                null);
    }

    /** Test that JML identifiers are not found after a JML line comment ends*/
    @Test public void testLineComment6() {
        helpScanner("//@ requires\nrequires",
                new Enum<?>[]{REQUIRES,EJML,IDENTIFIER},
                null);
    }
    
    /** Test that an @ at the end of a line comment is found */
    @Test public void testLineComment7() {
        helpScanner("//@ requires @\n ",
                new Enum<?>[]{REQUIRES,MONKEYS_AT,EJML},
                null);
    }
    
    /** Test an empty line comment */
    @Test public void testLineComment8() {
        helpScanner("//\nrequires ",
                new Enum<?>[]{IDENTIFIER},
                null);
    }
    
    /** Test an empty JML line comment */
    @Test public void testLineComment9() {
        helpScanner("//@\nrequires ",
                new Enum<?>[]{IDENTIFIER},
                null);
    }
    
    /** Test an empty JML line comment */
    @Test public void testLineComment10() {
        helpScanner("//@@@@@\nrequires ",
                new Enum<?>[]{IDENTIFIER},
                null);
    }
    
    /** Test a bad backslash */
    @Test public void testLineComment11() {
        helpScanner("//@@x\\@@@\nrequires ",
                new Enum<?>[]{IDENTIFIER,ERROR,MONKEYS_AT,MONKEYS_AT,MONKEYS_AT,EJML,IDENTIFIER},
                null,1);
        checkMessages("/TEST.java:1: A backslash in a JML comment expects to be followed by a valid identifier",6);
    }
    
    /** Test a bad backslash */
    @Test public void testLineComment11a() {
        helpScanner("//@@\\@x@@\nrequires ",
                new Enum<?>[]{ERROR,MONKEYS_AT,IDENTIFIER,MONKEYS_AT,MONKEYS_AT,EJML,IDENTIFIER},
                null,1);
        checkMessages("/TEST.java:1: A backslash in a JML comment expects to be followed by a valid identifier",5);
    }
    
    @Test public void testMultiLine() {
        helpScanner("/*@ requires\nrequires@*/",
                new Enum<?>[]{REQUIRES,REQUIRES,EJML},
                null);
    }

    @Test public void testMultiLine1() {
        helpScanner("/*@ requires\n  requires@*/",
                new Enum<?>[]{REQUIRES,REQUIRES,EJML},
                null);
    }

    @Test public void testMultiLine2() {
        helpScanner("/*@ requires\n@requires@*/",
                new Enum<?>[]{REQUIRES,REQUIRES,EJML},
                null);
    }

    @Test public void testMultiLine3() {
        helpScanner("/*@ requires\n@@@requires@*/",
                new Enum<?>[]{REQUIRES,REQUIRES,EJML},
                null);
    }

    @Test public void testMultiLine4() {
        helpScanner("/*@ requires\n @requires@*/",
                new Enum<?>[]{REQUIRES,REQUIRES,EJML},
                null);
    }

    @Test public void testMultiLine5() {
        helpScanner("/*@ requires\n  @@@requires@*/",
                new Enum<?>[]{REQUIRES,REQUIRES,EJML},
                null);
    }

    @Test public void testMultiLineError() {
        helpScanner("/*@ \\result\n  @@@\\xyz@*/",
                new Enum<?>[]{BSRESULT,ERROR,EJML,EOF},
                new int[]{4,11,17,21,21,24,24,24},
                1);
        checkMessages("/TEST.java:2: This backslash token is unknown: \\xyz",6);
    }

    @Test public void testInformalComment() {
        helpScanner("/*@ \\result(* requires *)*/",
                new Enum<?>[]{BSRESULT,INFORMAL_COMMENT,EJML},
                new int[]{4,11,11,25,25,27},
                0);
    }
    @Test public void testInformalComment2() {
        helpScanner("/*@ \\result(* requires *****)*/",
                new Enum<?>[]{BSRESULT,INFORMAL_COMMENT,EJML},
                new int[]{4,11,11,29,29,31},
                0);
    }
    @Test public void testInformalComment3() {
        helpScanner("/*@ \\result(* requires **** *)*/",
                new Enum<?>[]{BSRESULT,INFORMAL_COMMENT,EJML},
                new int[]{4,11,11,30,30,32},
                0);
    }
    

    // Testing an unclosed informal comment in a BLOCK comment
    @Test public void testInformalComment4() {
        helpScanner("/*@ \\result(* requires **** */",
                new Enum<?>[]{BSRESULT,INFORMAL_COMMENT,EJML},
                new int[]{4,11,11,28,28,30},
                1);
        checkMessages("/TEST.java:1: The informal expression is not closed",13);
    }
    
    // Testing an unclosed informal comment in a BLOCK comment
    @Test public void testInformalComment4a() {
        helpScanner("/*@ \\result(* requires *\n*** */",
                new Enum<?>[]{BSRESULT,INFORMAL_COMMENT,EJML},
                new int[]{4,11,11,29,29,31},
                1);
        checkMessages("/TEST.java:1: The informal expression is not closed",13);
    }
    
    // Testing an unclosed informal comment in a BLOCK comment
    @Test public void testInformalComment4b() {
        helpScanner("/*@ \\result(* requires *\n*** ",
                new Enum<?>[]{ERROR,EOF},
                null, //new int[]{4,11,11,30,30,31},
                1);
        checkMessages("/TEST.java:1: unclosed comment",1);
    }
    
    // Testing an unclosed informal comment in a LINE comment
    @Test public void testInformalComment5() {
        helpScanner("//@ \\result(* requires **** \n public",
                new Enum<?>[]{BSRESULT,INFORMAL_COMMENT,EJML,PUBLIC,EOF},
                new int[]{4,11,11,28,28,29,30,36,36,36},
                1);
        checkMessages("/TEST.java:1: The informal expression is not closed",13);
    }
    
    // Testing an unclosed informal comment in a LINE comment
    @Test public void testInformalComment5a() {
        helpScanner("//@ \\result(* requires *****",
                new Enum<?>[]{BSRESULT,INFORMAL_COMMENT,EOF},
                new int[]{4,11,11,28,28,28},
                1);
        checkMessages("/TEST.java:1: The informal expression is not closed",13);
    }
    
    // Testing an unclosed informal comment in a LINE comment
    @Test public void testInformalComment6() {
        helpScanner("//@ \\result(* requires ***\"*) \" requires\n",
                new Enum<?>[]{BSRESULT,INFORMAL_COMMENT,ERROR,EOF},
                new int[]{4,11,11,29,30,40,41,41},
                1);
        checkMessages("/TEST.java:1: unclosed string literal",31);
    }
    
    @Test public void testStringLiteral() {
        Scanner sc = fac.newScanner("\"\\tA\\\\B\"", true);
        sc.nextToken();
        assertEquals(STRINGLITERAL,sc.token());
        assertEquals("\tA\\B",sc.stringVal());
    }
    
    @Test public void testCharLiteral() {
        Scanner sc = fac.newScanner("\'\\t\'", true);
        sc.nextToken();
        assertEquals(CHARLITERAL,sc.token());
        assertEquals("\t",sc.stringVal());
    }
    
    @Test public void testIntLiteralWithUnderscore() {
        String v = "123_456";
        Scanner sc = fac.newScanner(v, true);
        sc.nextToken();
        assertEquals(INTLITERAL,sc.token());
        assertEquals("123456",sc.stringVal());
        assertEquals(123456,Integer.parseInt(sc.stringVal()));
    }
    
    @Test public void testIntLiteralWithUnderscoreBin() {
        String v = "0b0101_1010";
        Scanner sc = fac.newScanner(v, true);
        sc.nextToken();
        assertEquals(INTLITERAL,sc.token());
        assertEquals("01011010",sc.stringVal());
        assertEquals(90,Integer.parseInt(sc.stringVal(),2));
    }
    
    @Test public void testIntLiteralWithUnderscoreHex() {
        String v = "0xDE_AF";
        Scanner sc = fac.newScanner(v, true);
        sc.nextToken();
        assertEquals(INTLITERAL,sc.token());
        assertEquals("DEAF",sc.stringVal());
        assertEquals(57007,Integer.parseInt(sc.stringVal(),16));
    }
    
    @Test public void testIntLiteralWithUnderscoreHexLong() {
        String v = "0xDEAF_DEAF";
        Scanner sc = fac.newScanner(v, true);
        sc.nextToken();
        assertEquals(INTLITERAL,sc.token());
        assertEquals("DEAFDEAF",sc.stringVal());
        assertEquals(3736067759L,Long.parseLong(sc.stringVal(),16));
    }
    
    @Test public void testDotDot() {
        helpScanner("//@..",
                new Enum<?>[]{DOT_DOT,EOF},
                new int[]{3,5,5,5},
                0);
    }
    
    @Test public void testDotDot2() {
        helpScanner("//@ modifies ..;",
                new Enum<?>[]{ASSIGNABLE,DOT_DOT,SEMI,EOF},
                null,
                0);
    }
    
    @Test public void testDotDot2a() {
        helpScanner("//@ 123..456;",
                new Enum<?>[]{INTLITERAL,DOT_DOT,INTLITERAL,SEMI,EOF},
                null,
                0);
    }
    
    @Test public void testDotDot3() {
        helpScanner("//@ modifies a[b .. c];",
                new Enum<?>[]{ASSIGNABLE,IDENTIFIER,LBRACKET,IDENTIFIER,DOT_DOT,IDENTIFIER,RBRACKET,SEMI,EOF},
                null,
                0);
    }
 
    @Test public void testDotDot4() {
        helpScanner("//@ modifies a[0..4];",
                new Enum<?>[]{ASSIGNABLE,IDENTIFIER,LBRACKET,INTLITERAL,DOT_DOT,INTLITERAL,RBRACKET,SEMI,EOF},
                null,
                0);
    }
 
    @Test public void testDotDot4a() {
        helpScanner("//@ modifies a[0 ..4];",
                new Enum<?>[]{ASSIGNABLE,IDENTIFIER,LBRACKET,INTLITERAL,DOT_DOT,INTLITERAL,RBRACKET,SEMI,EOF},
                null,
                0);
    }
 
    @Test public void testDotDot5() {
        helpScanner("//@ modifies ..234;",
                new Enum<?>[]{ASSIGNABLE,DOT_DOT,INTLITERAL,SEMI,EOF},
                null,
                0);
    }
    
    @Test public void testDotDot6() {
        helpScanner("//@ modifies .234;",
                new Enum<?>[]{ASSIGNABLE,DOUBLELITERAL,SEMI,EOF},
                null,
                0);
    }
    
    @Test public void testDotDot7() {
        helpScanner("//@ modifies 0.234;",
                new Enum<?>[]{ASSIGNABLE,DOUBLELITERAL,SEMI,EOF},
                null,
                0);
    }
    
    @Test public void testDotDot8() {
        helpScanner("//@ modifies a[0. .4];",
                new Enum<?>[]{ASSIGNABLE,IDENTIFIER,LBRACKET,DOUBLELITERAL,DOUBLELITERAL,RBRACKET,SEMI,EOF},
                null,
                0);
    }
 
    @Test public void testDotDot9() {
        helpScanner("//@ 0xApA\n ",
                new Enum<?>[]{DOUBLELITERAL,IDENTIFIER,EJML,EOF},
                null,
                1);
        checkMessages("/TEST.java:1: malformed floating point literal",5);
    }
 
    @Test public void testDotDot10() {
        helpScanner("//@ 1.0eZ \n ",
                new Enum<?>[]{DOUBLELITERAL,IDENTIFIER,EJML,EOF},
                null,
                1);
        checkMessages("/TEST.java:1: malformed floating point literal",5);
    }
 
    @Test public void testDotDot11() {
        helpScanner("//@ 0xA.0pZ\n ",
                new Enum<?>[]{DOUBLELITERAL,IDENTIFIER,EJML,EOF},
                null,
                1);
        checkMessages("/TEST.java:1: malformed floating point literal",5);
    }
 
    @Test public void testDotDot12() {
        helpScanner("//@ 0xA.Z\n ",
                new Enum<?>[]{DOUBLELITERAL,IDENTIFIER,EJML,EOF},
                null,
                1);
        checkMessages("/TEST.java:1: malformed floating point literal",5);
    }
 
    @Test public void testConditionalKey1() {
        helpScanner("//+POS@ requires\n  /*+POS@ requires */",
                new Enum<?>[]{EOF},
                null);
    }

    @Test public void testConditionalKey2() {
        helpScanner("//-NEG@ requires\n  /*-NEG@ requires */",
                new Enum<?>[]{REQUIRES,EJML,REQUIRES,EJML,EOF},
                null);
    }

    @Test public void testConditionalKey3() {
        keys = new String[]{"POS"};
        helpScanner("//+POS@ requires\n  /*+POS@ requires */",
                new Enum<?>[]{REQUIRES,EJML,REQUIRES,EJML,EOF},
                null);
    }

    @Test public void testConditionalKey4() {
        keys = new String[]{"NEG"};
        helpScanner("//-NEG@ requires\n  /*-NEG@ requires */",
                new Enum<?>[]{EOF},
                null);
    }

    @Test public void testConditionalKey5() {
        helpScanner("//-NEG+POS@ requires\n  /*-NEG+POS@ requires */",
                new Enum<?>[]{EOF},
                null);
    }

    @Test public void testConditionalKey6() {
        keys = new String[]{"POS"};
        helpScanner("//-NEG+POS@ requires\n  /*-NEG+POS@ requires */",
                new Enum<?>[]{REQUIRES,EJML,REQUIRES,EJML,EOF},
                null);
    }

    @Test public void testConditionalKey7() {
        keys = new String[]{"NEG"};
        helpScanner("//-NEG+POS@ requires\n  /*-NEG+POS@ requires */",
                new Enum<?>[]{EOF},
                null);
    }

    @Test public void testConditionalKey8() {
        keys = new String[]{"NEG","POS"};
        helpScanner("//-NEG+POS@ requires\n  /*-NEG+POS@ requires */",
                new Enum<?>[]{EOF},
                null);
    }

    @Test public void testConditionalKey9() {
        helpScanner("//+@ requires\n  /*+@ requires */",
                new Enum<?>[]{REQUIRES,EJML,REQUIRES,EJML,EOF},
                null);
    }

    @Test public void testConditionalKey10() {
        helpScanner("//-@ requires\n  /*-@ requires */",
                new Enum<?>[]{EOF},
                null);
    }



}
