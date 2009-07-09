package tests;
import static com.sun.tools.javac.parser.Token.*;
import static org.jmlspecs.openjml.JmlToken.*;
import junit.framework.AssertionFailedError;

import org.jmlspecs.openjml.JmlToken;
import org.junit.Test;

import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.Scanner;
import com.sun.tools.javac.parser.Token;
import com.sun.tools.javac.util.Log;

// TODO - should test unicode, especially with multiple backslashes
// TODO - should test errPos for error tokens (is endPos set?)

public class scanner extends JmlTestCase {

    final static JmlToken SJML = STARTJMLCOMMENT;
    final static JmlToken EJML = ENDJMLCOMMENT;
    
    Scanner.Factory fac;
    
    // TODO - do we need to collect and compare System.out,err
    
    /** Initializes a fresh scanner factory for each test */
    protected void setUp() throws Exception {
        super.setUp(); // Sets up a main program, diagnostic collector
        fac = Scanner.Factory.instance(context);
        Log.instance(context).multipleErrors = true;
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
        } catch (AssertionFailedError a) {
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
            Scanner sc = fac.newScanner(s);
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
                if (!noExtraPrinting) printErrors();
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
//    /** Test some unicode  - multiple backslash*/
//    @Test public void testSomeUnicode3() {
//        helpScanner("\\\\u0041 A",new Enum[]{ERROR,IDENTIFIER,IDENTIFIER},
//                new int[]{0,1,2,7,8,9});  
//    }
    
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
    

    // TODO - add tests that the checkMessages calls work even with bad arguments
    
    /** Tests that JML keywords are not found in Java */
    @Test public void testJmlKeywordsNotInJml() {
        helpScanner("requires ensures pure",
                new Enum<?>[]{IDENTIFIER,IDENTIFIER,IDENTIFIER,},
                new int[]{0,8,9,16,17,21});
    }
    
    /** Tests that JML keywords are found in a JML comment */
    @Test public void testJmlKeywordsInJml() {
        helpScanner("/*@requires ensures pure */",
                new Enum<?>[]{SJML,REQUIRES,ENSURES,PURE,EJML,},
                new int[]{2,3,3,11,12,19,20,24,25,26});
    }
    
    /** Tests that JML keywords are not found in a Java comment */
    @Test public void testJmlKeywordsNotInJavaComment() {
        helpScanner("/* requires */ /*@requires */",
                new Enum<?>[]{SJML,REQUIRES,EJML,},
                new int[]{17,18,18,26,27,28});
    }
    
    /** Tests that JML keywords are not found after a JML comment ends */
    @Test public void testJmlKeywordsAfterJml() {
        helpScanner("/*@requires */requires ensures pure",
                new Enum<?>[]{SJML,REQUIRES,EJML,IDENTIFIER,IDENTIFIER,IDENTIFIER,},
                new int[]{2,3,3,11,12,13,14,22,23,30,31,35});
    }
    
    /** Tests JML operators */
    @Test public void testOperators() {
        helpScanner("/*@ ==> <== <: <==> <=!=> -> <- */",
                new Enum<?>[]{SJML,IMPLIES,REVERSE_IMPLIES,SUBTYPE_OF,EQUIVALENCE,INEQUIVALENCE,RIGHT_ARROW,LEFT_ARROW,EJML},
                new int[]{2,3, 4,7, 8,11, 12,14, 15,19, 20,25, 26,28, 29,31, 32,33});
    }
    
    /** Tests the Java operators related to JML operators */
    @Test public void testOperators1() {
        helpScanner("/*@ ==  <=  <  */",
                new Enum<?>[]{SJML,EQEQ,LTEQ,LT,EJML},
                new int[]{2,3,4,6,8,10,12,13,15,16});
    }
    
    /** Tests JML operators when in Java land */
    @Test public void testOperators2() {
        helpScanner("    ==> <== <: <==> <=!=> ",
                new Enum<?>[]{EQEQ,GT, LTEQ,EQ, LT,COLON, LTEQ,EQ,GT, LTEQ,BANGEQ,GT},
                new int[]{4,6,6,7, 8,10,10,11, 12,13,13,14, 15,17,17,18,18,19, 20,22,22,24,24,25});
    }
    
    @Test public void testBadOperator() {
        helpScanner("/*@ <=! + */",
                new Enum<?>[]{SJML,LTEQ,BANG,PLUS,EJML},
                new int[]{2,3,4,6,6,7,8,9,10,11});
    }

    @Test public void testBadOperator2() {
        helpScanner("/*@ <=!= + */",
                new Enum<?>[]{SJML,LTEQ,BANGEQ,PLUS,EJML},
                new int[]{2,3,4,6,6,8,9,10,11,12});
    }

    // NOTE:  In the test strings, backslash characters must be escaped.  So
    // within the string you write \\result, not \result, to get the effect of
    // \result in a test program.
    
    /** Test that a backslash token is found */
    @Test public void testBackslash() {
        helpScanner("/*@ \\result */",
                new Enum<?>[]{SJML,BSRESULT,EJML},
                null);
    }
    
    /** Test that two immediately consecutive backslash tokens are found */
    @Test public void testBackslash1() {
        helpScanner("/*@ \\result\\result */",
                new Enum<?>[]{SJML,BSRESULT,BSRESULT,EJML},
                null);
    }
    
    /** Test that backslash tokens are found immediately after a line termination */
    @Test public void testBackslash2() {
        helpScanner("/*@ \\result \n\\result*/",
                new Enum<?>[]{SJML,BSRESULT,BSRESULT,EJML},
                null);
    }
    
    /** Test that a backslash token without the backslash is a regular identifier */
    @Test public void testBackslash3() {
        helpScanner("/*@ \\result result*/",
                new Enum<?>[]{SJML,BSRESULT,IDENTIFIER,EJML},
                null);
    }
    
    /** Test for an invalid backslash identifier */
    @Test public void testBackslash5() {
        helpScanner("/*@ \\xyz result*/",
                new Enum<?>[]{SJML,IDENTIFIER,EJML},
                null,
                1);
        checkMessages(new String[]{"/TEST.java:1: This backslash token is unknown: xyz"},
                      new int[]{5});
    }

    /** Test for a JML backslash with no identifier */
    @Test public void testBackslash6() {
        helpScanner("/*@ \\ \\result*/",
                new Enum<?>[]{SJML,BSRESULT,EJML},
                null,
                1);
        checkMessages("/TEST.java:1: A backslash in a JML comment expects to be followed by a valid identifier",5);
    }
    

    // FIXME - bug in Scanner - processComment is not called if a line comment - test this for a block comment also
    // is at the very end of the input buffer, even with a line terminator
//    @Test public void testLineComment1() {
//        helpScanner("//@ requires",new Enum<?>[]{SJML,REQUIRES,EOF},null);
//    }
//
//    @Test public void testLineComment2() {
//        helpScanner("//@ requires\n",new Enum<?>[]{SJML,REQUIRES,EJML,EOF},null);
//    }

    /** Test that a line comment ends with a NL character */
    @Test public void testLineComment3() {
        helpScanner("//@ requires\n ",
                new Enum<?>[]{SJML,REQUIRES,EJML},
                new int[]{2,3,4,12,12,13});
    }

    /** Test that a line comment ends with a CR character */
    @Test public void testLineComment4() {
        helpScanner("//@ requires\r ",
                new Enum<?>[]{SJML,REQUIRES,EJML},
                null);
    }

    /** Test that a line comment ends with a CR NL combination */
    @Test public void testLineComment5() {
        helpScanner("//@ requires\r\n",
                new Enum<?>[]{SJML,REQUIRES,EJML},
                null);
    }

    /** Test that JML identifiers are not found after a JML line comment ends*/
    @Test public void testLineComment6() {
        helpScanner("//@ requires\nrequires",
                new Enum<?>[]{SJML,REQUIRES,EJML,IDENTIFIER},
                null);
    }
    
    /** Test that an @ at the end of a line comment is found */
    @Test public void testLineComment7() {
        helpScanner("//@ requires @\n ",
                new Enum<?>[]{SJML,REQUIRES,MONKEYS_AT,EJML},
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
    
                                // FIXME - the behavior with a bad backslash is not entirely right, though it causes no trouble
    /** Test a bad backslash */
    @Test public void testLineComment11() {
        helpScanner("//@@x\\@@@\nrequires ",
                new Enum<?>[]{SJML,IDENTIFIER,ERROR,MONKEYS_AT,MONKEYS_AT,MONKEYS_AT,EJML,IDENTIFIER},
                null,1);
        checkMessages("/TEST.java:1: A backslash in a JML comment expects to be followed by a valid identifier",6);
    }
    
    /** Test a bad backslash */
    @Test public void testLineComment11a() {
        helpScanner("//@@\\@x@@\nrequires ",
                new Enum<?>[]{SJML,MONKEYS_AT,IDENTIFIER,MONKEYS_AT,MONKEYS_AT,EJML,IDENTIFIER},
                null,1);
        checkMessages("/TEST.java:1: A backslash in a JML comment expects to be followed by a valid identifier",5);
    }
    
    @Test public void testMultiLine() {
        helpScanner("/*@ requires\nrequires@*/",
                new Enum<?>[]{SJML,REQUIRES,REQUIRES,EJML},
                null);
    }

    @Test public void testMultiLine1() {
        helpScanner("/*@ requires\n  requires@*/",
                new Enum<?>[]{SJML,REQUIRES,REQUIRES,EJML},
                null);
    }

    @Test public void testMultiLine2() {
        helpScanner("/*@ requires\n@requires@*/",
                new Enum<?>[]{SJML,REQUIRES,REQUIRES,EJML},
                null);
    }

    @Test public void testMultiLine3() {
        helpScanner("/*@ requires\n@@@requires@*/",
                new Enum<?>[]{SJML,REQUIRES,REQUIRES,EJML},
                null);
    }

    @Test public void testMultiLine4() {
        helpScanner("/*@ requires\n @requires@*/",
                new Enum<?>[]{SJML,REQUIRES,REQUIRES,EJML},
                null);
    }

    @Test public void testMultiLine5() {
        helpScanner("/*@ requires\n  @@@requires@*/",
                new Enum<?>[]{SJML,REQUIRES,REQUIRES,EJML},
                null);
    }

    @Test public void testMultiLineError() {
        helpScanner("/*@ \\result\n  @@@\\xyz@*/",
                new Enum<?>[]{SJML,BSRESULT,ERROR,EJML},
                new int[]{2,3,4,11,17,21,21,22},  // FIXME - what should the pos of the start and end JML be?
                1);
        checkMessages("/TEST.java:2: This backslash token is unknown: xyz",6);
    }

    @Test public void testInformalComment() {
        helpScanner("/*@ \\result(* requires *)*/",
                new Enum<?>[]{SJML,BSRESULT,INFORMAL_COMMENT,EJML},
                new int[]{2,3,4,11,11,25,25,26},
                0);
    }
    @Test public void testInformalComment2() {
        helpScanner("/*@ \\result(* requires *****)*/",
                new Enum<?>[]{SJML,BSRESULT,INFORMAL_COMMENT,EJML},
                new int[]{2,3,4,11,11,29,29,30},
                0);
    }
    @Test public void testInformalComment3() {
        helpScanner("/*@ \\result(* requires **** *)*/",
                new Enum<?>[]{SJML,BSRESULT,INFORMAL_COMMENT,EJML},
                new int[]{2,3,4,11,11,30,30,31},
                0);
    }
    

    // FIXME - unclosed informal comment
//  // Testing an unclosed informal comment in a BLOCK comment
//    @Test public void testInformalComment4() {
//        helpScanner("/*@ \\result(* requires **** */",
//                new Enum<?>[]{SJML,BSRESULT,INFORMAL_COMMENT,EJML},
//                new int[]{2,3,4,11,11,30,30,31},
//                0);
//    }
    
//    // Testing an unclosed informal comment in a LINE comment
//    @Test public void testInformalComment5() {
//        helpScanner("//@ \\result(* requires **** \n public",
//                new Enum<?>[]{SJML,BSRESULT,INFORMAL_COMMENT,EJML},
//                new int[]{2,3,4,11,11,30,30,31},
//                0);
//    }
    
    @Test public void testStringLiteral() {
        Scanner sc = fac.newScanner("\"\\tA\\\\B\"");
        sc.nextToken();
        assertEquals(STRINGLITERAL,sc.token());
        assertEquals("\tA\\B",sc.stringVal());
    }
    
    @Test public void testCharLiteral() {
        Scanner sc = fac.newScanner("\'\\t\'");
        sc.nextToken();
        assertEquals(CHARLITERAL,sc.token());
        assertEquals("\t",sc.stringVal());
    }
    

}
