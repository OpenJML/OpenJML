package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.RacBase;

import org.junit.*;

/** These tests exercise the RAC checking.  They compile a test class 
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racnew extends RacBase {

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true; print = true;
        ignoreNotes = false;  // FIXME - change notes to warnings; get rid of ignoreNotes
        super.setUp();
        addOptions("--code-math=java","--spec-math=java");  // FIXME - errors if we use bigint math
        addOptions("-jmltesting");
        addOptions("--rac-show-source=line");
    }

    /** Basic Hello World test, with no RAC tests triggered */
    @Test public void testJava() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { System.out.println(\"HELLO WORLD\"); }}"
                ,"HELLO WORLD"
                );
    }

    /** Basic Hello World test, with no RAC tests triggered */
    @Test public void testJavaExit() {
        expectedRACExit = 5;
        addOptions("--rac-show-source=none");
        helpRacText("tt.TestJavaExit","package tt; public class TestJavaExit { public static void main(String[] args) { System.exit(5); }}"
                ,"verify: JML diverges assertion is false"
                ,"verify: Associated declaration"
                );
    }

    /** Basic Hello World test, with no RAC tests triggered */
    @Test public void testJavaNull() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) {  }}"
                );
    }

    /** Simple test of output from a JML set statement */
    @Test public void testJML() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ ghost int i = 0; \n //@ set i = 1; \n //@ set System.out.println(i); \n System.out.println(\"END\"); }}"
                ,"1"
                ,"END"
                );
    }

    /** JML assert statement failure */
    @Test public void testAssertion() {
        helpRacText("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { \n//@ assert false; \n System.out.println(\"END\"); }}"
                ,"/tt/TestAssert.java:2: JML assertion is false"
                ,"END"
                );
    }

    /** JML labeled assert statement failure */
    @Test public void testAssertion2() {
        helpRacText("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { \n//@ assert false: \"ABC\"; \n System.out.println(\"END\"); }}"
                ,"ABC"
                ,"END"
                );
    }

    /** Tests that an optional argument on a JML assert is converted to a String and is what is printed as an error message */
    @Test public void testAssertion3() {
        helpRacText("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { //@ assert false: (int)args.length; \n System.out.println(\"END\"); }}"
                ,"0"
                ,"END"
                );
    }

    /** Tests that an optional argument on a JML assert is converted to a String and is what is printed as an error message */
    @Test public void testAssertion3a() {
        helpRacText("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { //@ assert true: args.length; \n System.out.println(\"END\"); }}"
                ,"END"
                );
    }

    /** Assumption failure */
    @Test public void testAssumption() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ assume false; \n System.out.println(\"END\"); }}"
                ,"/tt/TestJava.java:1: JML assumption is false"
                ,"END"
                );
    }

    /** Labeled assumption failure */
    @Test public void testAssumption2() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ assume false: \"DEF\"; \n System.out.println(\"END\"); }}"
                ,"DEF"
                ,"END"
                );
    }

    /** Failed unreachable statement */
    @Test public void testUnreachable() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ unreachable; \n System.out.println(\"END\"); }}"
                ,"/tt/TestJava.java:1: JML unreachable statement reached"
                ,"END"
                );
    }

    /** Successful precondition */
    @Test public void testPrecondition() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(0); System.out.println(\"END\"); }\n" +
                " /*@ requires i == 0; */ static void m(int i) {} " +
                "}"
                ,"END"
                );
    }
    
    /** Failed precondition */
    @Test public void testPrecondition2() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(0); System.out.println(\"END\"); }\n" +
                " /*@ requires i != 0; */ \n" +
                " static public void m(int i) {} " +
                "}"
                ,"/tt/TestJava.java:1: JML precondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"END"
                );
    }
    
    /** Failed precondition */
    @Test public void testPrecondition3() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(1); \n" +
                " m(-1); \n" +
                " m(0); \n" +
                " System.out.println(\"END\"); }\n" +
                " /*@ requires i > 0; */ \n" +
                " /*@ requires i < 0; */ \n" +
                " static public void m(int i) {} " +
                "}"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:8: Associated declaration"
                ,"/tt/TestJava.java:6: JML precondition is false"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"/tt/TestJava.java:8: Associated declaration"
                ,"/tt/TestJava.java:6: JML precondition is false"
                ,"/tt/TestJava.java:4: JML precondition is false"
                ,"/tt/TestJava.java:8: Associated declaration"
                ,"/tt/TestJava.java:6: JML precondition is false"
                ,"END"
                );
    }

    
    @Test public void testNonnullPrecondition() {
        addOptions("--rac-show-source=source");
        helpRacText("tt.TestJava",
                """
                package tt; public class TestJava {
                public static void main(String[] args) {
                 m(null,1);
                 //@ print "END";
                 }
                 /*@ requires true; */
                 static public void m(/*@non_null*/ Object o, int i) {
                 }
                }
                """
//                ,"/tt/TestJava.java:3: JML actual argument may not be null: o in m(java.lang.@org.jmlspecs.annotation.NonNull Object,int)"
//                ," m(null,1); "
//                ,"   ^"
//                ,"/tt/TestJava.java:6: Associated declaration: /tt/TestJava.java:3:"
//                ," static public void m(/*@non_null*/ Object o, int i) {"
//                ,"                         ^"
                ,"/tt/TestJava.java:3: verify: JML precondition is false"
                ," m(null,1);"
                ,"  ^"
                ,"/tt/TestJava.java:7: verify: Associated declaration: /tt/TestJava.java:3:"
                ," static public void m(/*@non_null*/ Object o, int i) {"
                ,"                    ^"
                ,"/tt/TestJava.java:6: JML precondition is false"
                ," /*@ requires true; */"
                ,"     ^"
                ,"END"
                );
    }
    
    @Test public void testNonnullPrecondition2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static void main(String[] args) {
                        m(null,1);
                        //@ print "END";
                    }
                    static public void m(/*@ non_null*/ Object o, int i) {}
                }
                """
//                ,"/tt/TestJava.java:4: verify: JML actual argument may not be null: o in m(java.lang.@org.jmlspecs.annotation.NonNull Object,int)"
//                ,"/tt/TestJava.java:7: verify: Associated declaration: /tt/TestJava.java:1:"
                ,"/tt/TestJava.java:4: verify: JML precondition is false"
                ,"/tt/TestJava.java:7: verify: Associated declaration: /tt/TestJava.java:1:"
                ,"/tt/TestJava.java:7: verify: JML precondition is false"
                ,"END"
                );
    }
    
    @Test public void testNonnullPostcondition() {
        helpRacText("tt.TestJava",
                """
                package tt; public class TestJava {
                    public static void main(String[] args) {
                        m(null,1);
                        System.out.println(\"END\");
                    }
                    static public /*@ non_null*/Object m( /*@ nullable*/Object o, int i) { return null; }
                }
                """
                ,"/tt/TestJava.java:6: verify: JML null return value from method m"
                ,"/tt/TestJava.java:6: verify: Associated declaration: /tt/TestJava.java:3:"
                ,"/tt/TestJava.java:3: verify: JML null return value from method m(java.lang.@org.jmlspecs.annotation.Nullable Object,int), checked in caller main(java.lang.String[])"
                ,"/tt/TestJava.java:6: verify: Associated declaration: /tt/TestJava.java:3:"
                ,"END"
                );
    }
    
    // TODO need multiple requires, multiple spec cases

    @Test public void testPostcondition() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures k == i; */ static int m(int i) { k = i; return 13; } " +
                "}"
                ,"END"
                );
    }

    @Test public void testPostcondition1() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(1); System.out.println(\"END\"); } \n" +
                " static public int k = 0; \n" +
                " /*@ ensures k == 0; */ \n" +
                " static public int m(int i) { k = i; return 13; } " +
                "}"
                ,"/tt/TestJava.java:5: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"END"
                );
    }

    @Test public void testPostcondition2() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ requires true; \nalso \nrequires false; \nensures k == 0; */ static void m(int i) { k = i; } " +
                "}"
                ,"END"
                );
    }

    @Test public void testPostcondition3() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ requires true; \nensures true; \nalso \nrequires false; \nensures k == 0; */ static void m(int i) { k = i; } " +
                "}"
                ,"END"
                );
    }

    @Test public void testPostcondition4() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(1); System.out.println(\"END\"); } \n" +
                " static public int k = 0; \n" +
                " /*@ requires true; \n" +
                "     ensures k != i; \n" +
                "     also \n" +
                "     requires true; \n" +
                "     ensures k == 0; */ \n" +
                " static public void m(int i) { k = i; } " +
                "}"
                ,"/tt/TestJava.java:9: JML postcondition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:9: JML postcondition is false"
                ,"/tt/TestJava.java:8: Associated declaration"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:8: Associated declaration"
                ,"END"
                );
    }
    
    @Test public void testPostcondition5() {
        expectedRACExit = 1;
        helpRacText("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String[] args) { \n"
                +"    org.jmlspecs.runtime.Utils.useExceptions = true; \n"
                +"    m(1); \n"
                +"    System.out.println(\"END\"); \n"
                +"  } \n"
                +"  static int k = 0; \n"
                +"  /*@   requires true; \n"
                +"        ensures k != i; \n" 
                +"      also \n"
                +"        requires true; \n"
                +"        ensures k == 0; */\n"
                +"  static void m(int i) { k = i; } " +
                "}"
                ,"Exception in thread \"main\" org.jmlspecs.runtime.JmlAssertionError: /tt/TestJava.java:14: verify: JML postcondition is false"
                ,"/tt/TestJava.java:10: Associated declaration"
                ,"\tat java.base/org.jmlspecs.runtime.Utils.createException"+locA
                ,"\tat java.base/org.jmlspecs.runtime.Utils.assertionFailureL"+locB
                ,"\tat tt.TestJava.m(TestJava.java:14)"
                ,"\tat tt.TestJava.main(TestJava.java:5)"
                );
    }
    
    @Test public void testSignals() {
        helpRacText("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \n"
                +"     signals (java.io.FileNotFoundException e) e == null; */\n"
                +"static public void m(int i) throws java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML signals condition is false"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"/tt/TestJava.java:3: JML signals condition is false"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"END"
                );
    }

    @Test public void testSignals2() {
        helpRacText("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static public int k = 0; \n"
                +" /*@ requires true; \nsignals (java.io.FileNotFoundException e) e == null; */\n"
                +"static public void m(int i) throws Exception, java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML signals condition is false"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"/tt/TestJava.java:3: JML signals condition is false"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"END"
                );
    }
    
    @Test public void testSignalsOnly() {
        helpRacText("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \nsignals_only \\nothing; */\n"
                +"static public void m(int i) throws Exception, java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML unexpected exception for the signals_only clause: java.io.FileNotFoundException" // check by callee
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"/tt/TestJava.java:3: JML unexpected exception for the signals_only clause: java.io.FileNotFoundException" // check of postcondition assumption by caller
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"END"
                );
    }

    @Test public void testSignalsOnly1() {
        helpRacText("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \nsignals_only java.io.FileNotFoundException; */\n"
                +"static void m(int i) throws Exception, java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"END"
                );
    }

    @Test public void testSignalsOnly2() {
        helpRacText("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \nsignals_only java.io.FileNotFoundException; */\n"
                +"static void m(int i) throws Exception, java.io.FileNotFoundException { throw new Exception(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML unexpected exception for the signals_only clause: java.lang.Exception"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"/tt/TestJava.java:3: JML unexpected exception for the signals_only clause: java.lang.Exception"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"END"
                );
    }

    @Test public void testSignalsOnlyDefault() {
        helpRacText("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \n*/\n"
                +"static void m(int i) throws java.io.FileNotFoundException { throw new RuntimeException(); } "
                +"}"
//                ,"/tt/TestJava.java:8: JML unexpected exception for the signals_only clause"
//                ,"/tt/TestJava.java:8: Associated declaration"
//                ,"/tt/TestJava.java:3: JML unexpected exception for the signals_only clause"
//                ,"/tt/TestJava.java:8: Associated declaration"
                ,"END"
                );
    }

    @Test public void testSignalsOnlyDefault1() {
        helpRacText("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \n*/\n"
                +"static void m(int i) throws java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"END"
                );
    }

    @Test public void testSignalsOnlyDefault2() {
        helpRacText("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) throws RuntimeException { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" \n"
                +"static void m(int i) \n"
                +"    throws java.io.FileNotFoundException \n"
                +"   { throw new RuntimeException(); }\n"
                +"}"
//                ,"/tt/TestJava.java:7: JML unexpected exception for the signals_only clause"
//                ,"/tt/TestJava.java:7: Associated declaration"
//                ,"/tt/TestJava.java:3: JML unexpected exception for the signals_only clause"
//                ,"/tt/TestJava.java:7: Associated declaration"
                ,"END"
                );
    }

    @Test public void testResult() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) {  m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures \\result == 4; */ static int m(int i) { return 4; } " +
                "}"
                ,"END"
        );
    }

    @Test public void testResult1() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +" m(1); \n"
                +" System.out.println(\"END\"); } \n"
                +" static int k = 0; \n" 
                +" /*@ ensures \\result == 4; */ \n"
                +" static public int m(int i) { \n"
                +" return 5; } "
                +"}"
                ,"/tt/TestJava.java:6: JML postcondition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"END"
        );
    }
    
    @Test public void havoc() {
        runrac = false;
        ignoreNotes = false;
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    int j ;
                    //@ havoc j;
                  }
                }
                """
                ,"/tt/TestJava.java:5: Note: Not implemented for runtime assertion checking: havoc statement",9
                );
    }
    
    @Test public void testLabel() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures (\\lbl ENS \\result == 1); */ static public int m(int i) { return i; } " +
                "}"
                ,"LABEL ENS = true"
                ,"LABEL ENS = true"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:1: JML postcondition is false"
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"END"
        );        
    }
    
    @Test public void testLabel2() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures (\\lbl ENS (\\lbl RES \\result) == 1); */ static public int m(int i) { return i; } " +
                "}"
                ,"LABEL RES = 1"
                ,"LABEL ENS = true"
                ,"LABEL RES = 1"
                ,"LABEL ENS = true"
                ,"LABEL RES = 0"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"LABEL RES = 0"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:1: JML postcondition is false"
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"END"
        );        
    }
    
    @Test public void testOld() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static public int k = 0; \n" +
                " /*@ ensures (\\lbl ENS \\old(k)) == k; */ static public int m(int i) { k=i; return i; } " +
                "}"
                ,"LABEL ENS = 0" // k==0 at beginning of m(1)
                ,"/tt/TestJava.java:2: JML postcondition is false" // postcondition false because k is now 1
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"LABEL ENS = 0"
                ,"/tt/TestJava.java:1: JML postcondition is false" // caller check, after m(1)
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"LABEL ENS = 1" // k==1 at beginning of m(0)
                ,"/tt/TestJava.java:2: JML postcondition is false" // callee check
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"LABEL ENS = 1"
                ,"/tt/TestJava.java:1: JML postcondition is false" // caller check, after m(0)
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"END"
        );        
    }
    
    @Test public void testOld2() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " static int m(int i) { //@ assert (\\lbl AST \\old(k)) == 0; \n k=i; //@ assert (\\lbl AST2 \\old(k)) == 0;\n //@ assert (\\lbl AST3 k) == 0; \n return i; } " +
                "}"
                ,"LABEL AST = 0"
                ,"LABEL AST2 = 0"
                ,"LABEL AST3 = 1"
                ,"/tt/TestJava.java:4: JML assertion is false"
                ,"LABEL AST = 1"
                ,"/tt/TestJava.java:2: JML assertion is false"
                ,"LABEL AST2 = 1"
                ,"/tt/TestJava.java:3: JML assertion is false"
                ,"LABEL AST3 = 0"
                ,"END"
        );        
    }
    
    @Test public void testOld3() {  // FIXME - \old at a label not working for RAC
        helpRacText("tt.TestJava","package tt; public class TestJava { \n"
                + "public static void main(String[] args) { \n"
                + "  m(1); m(0); \n"
                + "  System.out.println(\"END\"); "
                + "} \n"
                + "static int k = 0; \n"
                + "static int m(int i) { \n"
                + "  //@ ghost int p = (\\lbl AST \\old(k)); \n"
                + "  k=i; \n"
                + "  lab: k = 9+i; \n"
                + "  //@ ghost int kk =  (\\lbl AST2 \\old(k));\n "
                + "  //@ set kk = (\\lbl AST3 k); \n "
                + "  //@ set kk = (\\lbl AST4 \\old(k,lab)); \n "
                + "  return i; } "
                + "}"
                ,"LABEL AST = 0"  // k==0 at beginning of m(1)
                ,"LABEL AST2 = 0" // k==0 at beginning of m(1)
                ,"LABEL AST3 = 10" // k currently 10 in m(1)
                ,"LABEL AST4 = 1" // k was 1 at lab
                                  // k is 10 at exit of m(1)
                ,"LABEL AST = 10"  // so k is 10 at beginning of m(0) 
                ,"LABEL AST2 = 10" //  k is 10 at beginning of m(0)
                ,"LABEL AST3 = 9"  // k is 9 just after lab
                ,"LABEL AST4 = 0" // k was 0 (== i) at lab
                ,"END"
        );        
    }
    
    @Test public void testInformal() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " static int m(int i) { System.out.println(i); //@ assert (i==0) <==> (* informal *); \n return i; } " +
                "}"
                ,"1"
                ,"/tt/TestJava.java:2: JML assertion is false"
                ,"0"
                ,"END"
                );
    }

    @Test public void testTypeOfA() {
        helpRacText("tt.TestJava","package tt; import static org.jmlspecs.lang.JML.*; public class TestJava { public static void main(String[] args) { \n" +
                "m(new Object()); m(new String()); m(Boolean.TRUE); System.out.println(\"END\"); } \n" +
                " //@ requires JML.informal(\"asd\") && (\\lbl CLS \\erasure(\\typeof(i))) == Object.class; \n" +
                " static public void m(/*@nullable*/Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"LABEL CLS = class java.lang.Object"
                ,"LABEL CLS = class java.lang.Object"
                ,"CLASS class java.lang.Object"
                ,"LABEL CLS = class java.lang.String"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"LABEL CLS = class java.lang.String"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.lang.String"
                ,"LABEL CLS = class java.lang.Boolean"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"LABEL CLS = class java.lang.Boolean"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.lang.Boolean"
                ,"END"
                );
    }
    
    @Test public void testTypeOf1() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(new Object[1]); m(new String[2]); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i)) == \\type(Object); \n" +
                " static public void m(/*@nullable*/Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"LABEL CLS = java.lang.Object[]"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"LABEL CLS = java.lang.Object[]"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class [Ljava.lang.Object;"
                ,"LABEL CLS = java.lang.String[]"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"LABEL CLS = java.lang.String[]"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class [Ljava.lang.String;"
                ,"END"
                );
    }
    
    @Test public void testTypeOf2() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i)) == \\type(Object); \n" +
                " static public void m(int i) { \n" +
                "//@ assert (\\lbl AST \\typeof(true)) == \\typeof(true); \n" +
                "//@ assert (\\lbl AST2 \\typeof((short)0)) != \\typeof(true); \n" +
                "//@ assert (\\lbl AST3 \\typeof((long)0)) != \\typeof(true); \n" +
                "//@ assert (\\lbl AST4 \\typeof((byte)0)) != \\typeof(true); \n" +
                "//@ assert (\\lbl AST5 \\typeof('c')) != \\typeof(true); \n" +
                "//@ assert (\\lbl AST6 \\typeof(\"c\")) != \\typeof(true); \n" +
                "//@ assert (\\lbl AST7 \\typeof((float)0)) != \\typeof(true); \n" +
                "//@ assert (\\lbl AST8 \\typeof((double)0)) != \\typeof(true); \n" +
                "} " +
                "}"
                ,"LABEL CLS = int"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"LABEL CLS = int"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"LABEL AST = boolean"
                ,"LABEL AST2 = short"
                ,"LABEL AST3 = long"
                ,"LABEL AST4 = byte"
                ,"LABEL AST5 = char"
                ,"LABEL AST6 = java.lang.String"
                ,"LABEL AST7 = float"
                ,"LABEL AST8 = double"
                ,"END"
                );
    }
    
    @Test public void testTypeOf3() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "//@ assert (\\lbl AST9 \\typeof(5/0)) == \\typeof(5/0); \n" +
                "//@ assert (\\lbl AST10 \\typeof(5.0/0.0)) != \\typeof(5/0); \n" +
                "} " +
                "}"
                ,"LABEL AST9 = int"
                ,"LABEL AST10 = double"
                ,"END"
                );
    }

    @Test public void testTypeOf4() {
        helpRacText("tt.TestJava",
                """
                package tt; import java.util.*; public class TestJava {
                  public static void main(String[] args) {
                    //@ set System.out.println("COMPARE " + ( \\type(LinkedList<String>) == \\type(LinkedList<Integer>)));
                    //@ set System.out.println("COMPARE " + ( \\type(HashSet<Integer>) == \\type(LinkedList<Integer>)));
                    //@ set System.out.println("COMPARE " + ( \\type(LinkedList<Integer>) == \\type(LinkedList<Integer>)));
                    System.out.println("END");
                  }
                }
                """
                ,"COMPARE false"
                ,"COMPARE false"
                ,"COMPARE true"
                ,"END"
                );
    }

    @Test public void testTypeOf4a() {
        expectedExit = 1;
        helpRacText("tt.TestJava",
                """
                package tt; import java.util.*; public class TestJava {
                  public static void main(String[] args) {
                    //@ set System.out.println("COMPARE " + ( \\type(LinkedList) == \\type(LinkedList)));
                    //@ set System.out.println("COMPARE " + ( \\type(LinkedList<?>) == \\type(LinkedList<?>)));
                    System.out.println("END");
                  }
                }
                """
                ,"/tt/TestJava.java:3: error: The argument of a \\type construct must be a fully parameterized type: LinkedList", 52
                ,"/tt/TestJava.java:3: error: The argument of a \\type construct must be a fully parameterized type: LinkedList", 73
                ,"/tt/TestJava.java:4: error: Wildcards are not allowed within \\type expressions: LinkedList<?>", 64
                ,"/tt/TestJava.java:4: error: Wildcards are not allowed within \\type expressions: LinkedList<?>", 88
                ,"END"
                );
    }

    
    // FIXME - want typeof to return a JML type with type parameter information
    @Test public void testTypeOf5() {
        helpRacText("tt.TestJava",
                """
                package tt; import java.util.*; public class TestJava {
                  public static void main(String[] args) {
                    m(new LinkedList<String>());
                    m(new LinkedList<Integer>());
                    m(new HashSet<Integer>());
                    System.out.println(\"END\");
                  }
                  //@ requires (\\lbl CLS \\typeof(i)) == ( \\type(LinkedList<Integer>) );
                  static public void m(/*@nullable*/Object i) {
                    System.out.println(\"CLASS \" + i.getClass());
                  }
                }
                """
                ,"LABEL CLS = java.util.LinkedList"
                ,"Warning: runtime type information has no type arguments: java.util.LinkedList"
//                ,"/tt/TestJava.java:3: JML precondition is false"
//                ,"/tt/TestJava.java:9: Associated declaration"
                ,"LABEL CLS = java.util.LinkedList"
                ,"Warning: runtime type information has no type arguments: java.util.LinkedList"
//                ,"/tt/TestJava.java:8: JML precondition is false"
                ,"CLASS class java.util.LinkedList"
                ,"LABEL CLS = java.util.LinkedList"
                ,"Warning: runtime type information has no type arguments: java.util.LinkedList"
                ,"LABEL CLS = java.util.LinkedList"
                ,"Warning: runtime type information has no type arguments: java.util.LinkedList"
                ,"CLASS class java.util.LinkedList"
                ,"LABEL CLS = java.util.HashSet"
                ,"/tt/TestJava.java:5: JML precondition is false"
                ,"/tt/TestJava.java:9: Associated declaration"
                ,"LABEL CLS = java.util.HashSet"
                ,"/tt/TestJava.java:8: JML precondition is false"
                ,"CLASS class java.util.HashSet"
                ,"END"
                );
    }
    
    @Test public void testNonnullelement() {
        expectedRACExit = 1;
        helpRacText("tt.TestJava","package tt; public class TestJava { static int z = 0; public static void main(String[] args) { \n" +
                "String[] s2null = new String[]{null,\"B\"}; \n" +
                "String[] s2 = new String[]{\"A\",\"B\"}; \n" +
                "m(new Object[]{}); \n" +
                "m(new String[]{\"A\"}); \n" +
                "m(s2); \n" +
                "m(s2null); \n" +
                "//@ assert \\nonnullelements(s2,s2null); \n" +
                "//@ assert \\nonnullelements(s2,s2); \n" +
                        // Tests shortcut evaluation - should evaluate all arguments first
                "//@ assert \\nonnullelements(s2null,new Integer[]{5/z}); \n" +
                "System.out.println(\"END\"); } \n" +
                " static void m(Object[] o) { \n" +
                "//@ assert (\\lbl ELEM \\nonnullelements(o)); \n" +
                "} " +
                "}"
                ,"LABEL ELEM = true"
                ,"LABEL ELEM = true"
                ,"LABEL ELEM = true"
                ,"LABEL ELEM = false"
                ,"/tt/TestJava.java:13: JML assertion is false"
                ,"/tt/TestJava.java:8: JML assertion is false"
                ,"/tt/TestJava.java:10: JML Division by zero"
                ,"Exception in thread \"main\" java.lang.ArithmeticException: / by zero"
                ,"\tat tt.TestJava.main(TestJava.java:10)"
                );
    }
    
    @Test public void testNonnullelement2() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null); \n" +
                "System.out.println(\"END\"); } \n" +
                " static void m(Object /*@nullable*/[] o) { \n" +
                "//@ assert (\\lbl ELEM \\nonnullelements((\\lbl O o))); \n" +
                "} " +
                "}"
                ,"LABEL O = null"
                ,"LABEL ELEM = false"
                ,"/tt/TestJava.java:5: JML assertion is false"
                ,"END"
                );
    }
    
    @Test public void testLbl() { // FIXME - same as in racnew2?
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null); \n" +
                "System.out.println(\"END\"); } \n" +
                "static int i = 0; static String n = \"asd\";\n" +
                " static void m(/*@nullable*/ Object o) { \n" +
                "//@ assert (\\lbl STRING \"def\") != null; \n" +
                "++i; //@ assert (\\lbl SHORT (short)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl LONG (long)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl BYTE (byte)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl INT (int)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl FLOAT (float)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl DOUBLE (double)(i)) != 0; \n" +
                "//@ assert (\\lbl CHAR n.charAt(0)) != 0; \n" +
                "//@ assert (\\lbl BOOLEAN (i == 0)) ; \n" +
                "//@ assert (\\lbl OBJECT o) == null; \n" +
                "//@ assert (\\lbl STRING \"abc\") != null; \n" +
                "} " +
                "}"
                ,"LABEL STRING = def"
                ,"LABEL SHORT = 1"
                ,"LABEL LONG = 2"
                ,"LABEL BYTE = 3"
                ,"LABEL INT = 4"
                ,"LABEL FLOAT = 5.0"
                ,"LABEL DOUBLE = 6.0"
                ,"LABEL CHAR = a"
                ,"LABEL BOOLEAN = false"
                ,"/tt/TestJava.java:14: JML assertion is false"
                ,"LABEL OBJECT = null"
                ,"LABEL STRING = abc"
                ,"END"
                );
    }
    
    @Test public void testLblConst() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null); \n" +
                "System.out.println(\"END\"); } static int i = 0; \n" +
                " static void m(/*@ nullable */ Object o) { \n" +
                "//@ assert (\\lbl OBJECT null) == null; \n" +
                "//@ assert (\\lbl INT (int)(4)) != 0; \n" +
                "//@ assert (\\lbl SHORT (short)(1)) != 0; \n" +
                "//@ assert (\\lbl LONG (long)(2)) != 0; \n" +
                "//@ assert (\\lbl BYTE (byte)(3)) != 0; \n" +
                "//@ assert (\\lbl FLOAT (float)(5)) != 0; \n" +
                "//@ assert (\\lbl DOUBLE (double)(6)) != 0; \n" +
                "//@ assert (\\lbl CHAR 'a') != 0; \n" +
                "//@ assert (\\lbl BOOLEAN true) ; \n" +
                "//@ assert (\\lbl STRING \"abc\") != null; \n" +
                "} " +
                "}"
                ,"LABEL OBJECT = null"
                ,"LABEL INT = 4"
                ,"LABEL SHORT = 1"
                ,"LABEL LONG = 2"
                ,"LABEL BYTE = 3"
                ,"LABEL FLOAT = 5.0"
                ,"LABEL DOUBLE = 6.0"
                ,"LABEL CHAR = a"
                ,"LABEL BOOLEAN = true"
                ,"LABEL STRING = abc"
                ,"END"
                );
    }
    
    @Test public void testLblX() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(); mm(); ma(); mg(); \n" +
                "System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(int); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\type(boolean); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "}\n" +
                " static void mm() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(java.lang.Object); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\type(Object); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "//@ set c = \\type(java.lang.String); \n" +
                "//@ set c = (\\lbl TYP3 c); \n" +
                "//@ set c = \\type(String); \n" +
                "//@ set c = (\\lbl TYP4 c); \n" +
                "}\n" +
                " static void ma() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(java.lang.String[]); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\type(String[]); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "//@ set c = \\type(java.lang.String[][]); \n" +
                "//@ set c = (\\lbl TYP3 c); \n" +
                "//@ set c = \\type(String[][]); \n" +
                "//@ set c = (\\lbl TYP4 c); \n" +
                "} \n" +
                " static void mg() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(java.lang.Class<Integer>); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ ghost boolean bbb = (\\lbl TRUE Class.class == \\erasure(\\type(Class<Boolean>))); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "} " +
                "}"
                ,"LABEL TYP1 = int"
                ,"LABEL TYP2 = boolean"
                ,"LABEL TYP1 = java.lang.Object"
                ,"LABEL TYP2 = java.lang.Object"
                ,"LABEL TYP3 = java.lang.String"
                ,"LABEL TYP4 = java.lang.String"
                ,"LABEL TYP1 = java.lang.String[]"
                ,"LABEL TYP2 = java.lang.String[]"
                ,"LABEL TYP3 = java.lang.String[][]"
                ,"LABEL TYP4 = java.lang.String[][]"
                ,"LABEL TYP1 = java.lang.Class<java.lang.Integer>"
                ,"LABEL TRUE = true"
                ,"LABEL TYP2 = java.lang.Class<java.lang.Integer>"
                ,"END"
                );
    }
    
    @Test
    public void testTypelc() { 
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(); mm(); ma(); mg(); \n" +
                "System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(int); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\type(boolean); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "}\n" +
                " static void mm() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(java.lang.Object); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\type(Object); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "//@ set c = \\type(java.lang.String); \n" +
                "//@ set c = (\\lbl TYP3 c); \n" +
                "//@ set c = \\type(String); \n" +
                "//@ set c = (\\lbl TYP4 c); \n" +
                "}\n" +
                " static void ma() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(java.lang.String[]); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\type(String[]); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "//@ set c = \\type(java.lang.String[][]); \n" +
                "//@ set c = (\\lbl TYP3 c); \n" +
                "//@ set c = \\type(String[][]); \n" +
                "//@ set c = (\\lbl TYP4 c); \n" +
                "} \n" +
                " static void mg() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(java.lang.Class<Integer>); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "} " +
                "}"
                ,"LABEL TYP1 = int"
                ,"LABEL TYP2 = boolean"
                ,"LABEL TYP1 = java.lang.Object"
                ,"LABEL TYP2 = java.lang.Object"
                ,"LABEL TYP3 = java.lang.String"
                ,"LABEL TYP4 = java.lang.String"
                ,"LABEL TYP1 = java.lang.String[]"
                ,"LABEL TYP2 = java.lang.String[]"
                ,"LABEL TYP3 = java.lang.String[][]"
                ,"LABEL TYP4 = java.lang.String[][]"
                ,"LABEL TYP1 = java.lang.Class<java.lang.Integer>"
                ,"END"
                );
    }

    @Test
    public void testSubtype() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(); mm(); \n" +
                "System.out.println(\"END\"); } \n" +
                "static Object o = new Object(); \n" +
                "static Object oo = new String(); \n" +
                "static Object ob = Boolean.FALSE; \n" +
                "static String s = new String(); \n" +
                "static Boolean b = Boolean.TRUE; \n" +
                " static void m() { \n" +
                "//@ ghost boolean c; \n" +
                "//@ set c = o.getClass() <:= o.getClass(); \n" + // Object <:= Object  // Class
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\typeof(o) <:= \\typeof(o); \n" +  // Object <:= Object // \TYPE
                "//@ set c = (\\lbl TYP2 c); \n" +
                "//@ set c = \\typeof(o) <:= \\typeof(oo); \n" + // Object <:= String // \TYPE
                "//@ set c = (\\lbl TYP3 c); \n" +
                "//@ set c = \\typeof(oo) <:= \\typeof(o); \n" + // String <:= Object // \TYPE
                "//@ set c = (\\lbl TYP4 c); \n" +
                "//@ set c = \\typeof(ob) <:= \\typeof(oo); \n" + // Boolean <:= String // \TYPE
                "//@ set c = (\\lbl TYP5 c); \n" +
                "}\n" +
                " static void mm() { \n" +
                "//@ ghost boolean c; \n" +
                "//@ set c = s.getClass() <:= b.getClass(); \n" + // String <:= Boolean // Class
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\typeof(s) <:= \\typeof(b); \n" +  // String <:= Boolean // \TYPE
                "//@ set c = (\\lbl TYP2 c); \n" +
                "//@ set c = \\type(int) <:= \\typeof(o); \n" + // int <:= Object // \TYPE
                "//@ set c = (\\lbl TYP3 c); \n" +
                "//@ set c = \\type(int) <:= \\type(int); \n" + // int <:= int  // false
                "//@ set c = (\\lbl TYP4 c); \n" +
                "//@ set c = \\type(int) <:= \\type(boolean); \n" + // int <:= boolean
                "//@ set c = (\\lbl TYP5 c); \n" +
                "}\n" +
                "}"
                ,"LABEL TYP1 = true"
                ,"LABEL TYP2 = true"
                ,"LABEL TYP3 = false"
                ,"LABEL TYP4 = true"
                ,"LABEL TYP5 = false"
                ,"LABEL TYP1 = false"
                ,"LABEL TYP2 = false"
                ,"LABEL TYP3 = false"
                ,"LABEL TYP4 = true"
                ,"LABEL TYP5 = false"
                ,"END"
                );
    }

    @Test public void testUndefined() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); m(1); m(2); System.out.println(\"END\"); } \n" +
                " //@ requires 10/i != 0; \n" +
                " //@ ensures 10/(i-1) == 0; \n" +
                " static public void m(int i) { \n" +
                "   System.out.println(\"VALUE \" + i); \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:3: JML Division by zero"
                ,"JML undefined precondition - exception thrown" // FIXME - this should have a line number
                ,"java.lang.ArithmeticException: / by zero"
                ,"\tat tt.TestJava.main(TestJava.java:3)"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:3: JML Division by zero"
                ,"Runtime exception while evaluating preconditions - preconditions are undefined in JML"
                ,"java.lang.ArithmeticException: / by zero"
                ,"\tat tt.TestJava.m(TestJava.java:3)"
                ,"\tat tt.TestJava.main(TestJava.java:2)"
                ,"VALUE 0"
                ,"VALUE 1"
                ,"/tt/TestJava.java:4: JML Division by zero"
                ,"Runtime exception while evaluating postconditions - postconditions are undefined in JML"
                ,"java.lang.ArithmeticException: / by zero"
                ,"\tat tt.TestJava.m(TestJava.java:4)"
                ,"\tat tt.TestJava.main(TestJava.java:2)"
                ,"/tt/TestJava.java:4: JML Division by zero"
                ,"JML undefined postcondition - exception thrown"
                ,"java.lang.ArithmeticException: / by zero"
                ,"\tat tt.TestJava.main(TestJava.java:4)"
                ,"VALUE 2"
                ,"/tt/TestJava.java:5: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"END"
                );
        // FIXME - would like to make the stack traces above more helpful
    }
    
    // tests that requires clauses in the same spec case are evaluated in order as if connected by &&
    // (if not, in this case we would get an exception)
    @Test public void testUndefined2() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); m(1); System.out.println(\"END\"); } \n" +
                " //@ requires i != 0; \n" +
                " //@ requires 10/i == 10; \n" +
                " static public void m(int i) { \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"END"
                );
    }
    
    @Test public void testSpecFile() {
        addMockFile("$A/tt/A.jml",
                """
                package tt;
                public class A {
                    //@ ghost public static int i = 0;
                    //@ public invariant i == 0;
                    //@ requires i == 1;
                    static public int m();
                }
                """
                );
        helpRacText("tt.A",
                """
                package tt;
                public class A {
                    static public int m() { return 0; }
                    public static void main(String[] args) {
                        m();
                        System.out.println("END");
                    }
                }
                """
                ,"/tt/A.java:5: JML precondition is false"
                ,"/$A/tt/A.jml:6: Associated declaration"
                ,"/$A/tt/A.jml:5: JML precondition is false"
                ,"END"
                );
    }

    @Test public void testSpecFile2() {
        addMockFile("$A/tt/A.jml",
                """
                package tt;
                public class A {
                  //@ ghost static int i = 0;
                  //@ invariant i == 0;
                  //@ ensures i == 1;
                  static int m();
                }
                """
                );
        helpRacText("tt.A",
                """
                package tt;
                public class A {
                  static int m() {
                    //@ set i = 1;
                    return 0;
                  }
                  public static void main(String[] args) {
                    m(); System.out.println("END");
                  }
                }
                """
                ,"END"
                );
    }

    @Test public void testSpecModelMethod() {
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"/*@ model static pure public int mm() { return 5; } */ \n"
                +"//@ ghost static public int i = 0;\n  "
                +"//@ public invariant i == 0; \n //@ ensures i == 1;\n static public int m(); "
                +"}"
                );
        helpRacText("tt.A","package tt; public class A { static public int m() { \n"
                +"  //@ set i = mm(); \n"
                +"  return 0; }  \n"
                +" public static void main(String[] args) { m(); System.out.println(\"END\"); }}"
                ,"/tt/A.java:1: JML postcondition is false"
                ,"/$A/tt/A.jml:5: Associated declaration"
                ,"/tt/A.java:4: JML postcondition is false"
                ,"/$A/tt/A.jml:5: Associated declaration"
                ,"END"
                );
    }

    @Test
    public void testSpecModelClass() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"/*@ model public static class AA { static public int mm() { return 5; }} */ \n"
                +"//@ ghost public static int i = 0;\n"
                +"//@ public invariant i == 0; \n"
                +"//@ ensures i == 0;\n"
                +"static public int m() { \n"
                +"  //@ set i = AA.mm(); \n"
                +"  return 0; \n"
                +"}  \n "
                +"public static void main(String[] args) { \n"
                +"  m(); \n"
                +"  System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:6: verify: JML postcondition is false"  // TODO: Would like this to be line 8
                ,"/tt/A.java:5: verify: Associated declaration"
                ,"/tt/A.java:11: verify: JML postcondition is false"
                ,"/tt/A.java:5: verify: Associated declaration"
                ,"END"
                );
    }
    
    @Test
    public void testSpecModelClass2() { 
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"/*@ model public static class AB { static public int mm() { return 5; }} */ \n"
                +"//@ ghost public static int i = 0;\n"
                +"//@ public invariant i == 0; \n"
                +"//@ ensures i == 0;\n "
                +"static public int m(); \n"
                +"}"
                );
        helpRacText("tt.A","package tt; public class A { \n"
                +"static public int m() { \n"
                +"  //@ set i = AB.mm(); \n"
                +"  return 0; \n"
                +"}  \n "
                +"public static void main(String[] args) { \n"
                +"  m(); \n"
                +"  System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:2: JML postcondition is false"  // TODO: Would like this to be line 4
                ,"/$A/tt/A.jml:5: Associated declaration"
                ,"/tt/A.java:7: JML postcondition is false"
                ,"/$A/tt/A.jml:5: Associated declaration"
                ,"END"
                );
    }
    
    @Test public void testStaticInvariant() {
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ static public invariant i == 0; \n "
                +"public static void m(); \n"
                +"}"
                );
        helpRacText("tt.A","package tt; public class A { \n"
                +"static public int i = 0;  \n "
                +"static public void m() { i = 1-i; }  \n "
                +"public static void main(String[] args) { \n"
                +"m(); \n"
                +"System.out.println(\"MID \" + i); \n"
                +"m(); \n"
                +"System.out.println(\"END \" + i); \n"
                +"}}"
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()" // callee invariant by callee
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:5: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])" // callee invariant by caller
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"MID 1"
                ,"/tt/A.java:7: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())" // callee invariant by caller
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:3: JML assumed invariant is false on entering method tt.A.m()" // callee invariant by callee
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"END 0"
                );
    }

    @Test public void testStaticInvariant2() { 
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ static public invariant i == 0; \n "
                +"public void m(); \n"
                +"}"
                );
        helpRacText("tt.A","package tt; public class A { \n"
                +"static public int i = 0;  \n "
                +"public void m() { i = 1-i; }  \n "
                +"public static void main(String[] args) { \n"
                +"new A().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"new A().m(); i = 5; \n"
                +"System.out.println(\"MID\"); \n"
                +"new A().m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                // i == 0 initially
                // i == 1 on exit from m
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()"  // Leaving m
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:5: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"MID" // line 6
                ,"/tt/A.java:7: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.A())"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:1: JML assumed invariant is false on entering method tt.A.A()"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:7: JML assumed invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/A.jml:2: Associated declaration"
                // i still 1, since it is static
                ,"/tt/A.java:7: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:3: JML assumed invariant is false on entering method tt.A.m()"
                ,"/$A/tt/A.jml:2: Associated declaration"
                // now i is 5
                ,"MID"
                ,"/tt/A.java:9: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.A())"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:1: JML assumed invariant is false on entering method tt.A.A()"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:9: JML assumed invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/A.jml:2: Associated declaration"
                
                ,"/tt/A.java:9: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:3: JML assumed invariant is false on entering method tt.A.m()"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:9: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"END"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.main(java.lang.String[])"
                ,"/$A/tt/A.jml:2: Associated declaration"
                );
    }

    @Test public void testInvariant() { 
        addOptions("--rac-show-source=source");
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ public invariant i == 0;\n"
                +"public void m(); \n"
                +"}"
                );
        helpRacText("tt.A","package tt; public class A { \n"
                +"public int i = 0; static int j; \n"
                +"public void m() { i = 1-i; }  \n"
                +"public static void main(String[] args) { \n"
                +"new A().m();\n"
                +"j = 0; System.out.println(\"MID\"); j = 1;\n"
                +"new A().m();\n"
                +"j = 2; System.out.println(\"END\");\n"
                +"}}"
                
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()" // Leaving m(), Line 5
                ,"public void m() { i = 1-i; }  "
                ,"            ^"
                ,"/$A/tt/A.jml:2: Associated declaration: /tt/A.java:3:"
                ,"//@ public invariant i == 0;"
                ,"           ^"
                ,"/tt/A.java:5: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"new A().m();"
                ,"         ^"
                ,"/$A/tt/A.jml:2: Associated declaration: /tt/A.java:5:"
                ,"//@ public invariant i == 0;"
                ,"           ^"
                ,"MID"
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()"
                ,"public void m() { i = 1-i; }  "
                ,"            ^"
                ,"/$A/tt/A.jml:2: Associated declaration: /tt/A.java:3:"
                ,"//@ public invariant i == 0;"
                ,"           ^"
                ,"/tt/A.java:7: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"new A().m();"
                ,"         ^"
                ,"/$A/tt/A.jml:2: Associated declaration: /tt/A.java:7:"
                ,"//@ public invariant i == 0;"
                ,"           ^"
                ,"END"
                );
    }

    @Test public void testInitially() {
        addMockFile("$A/tt/A.jml",
                """
                package tt; public class A {
                  //@ public initially i == 1;
                  //@ public initially j == 1;
                  //@ public invariant i == j;
                  public void m();
                  /*@ assignable j; */
                  public A();
                }
                """
                );
        helpRacText("tt.A",
                """
                package tt; public class A {
                  public int i = 0;
                  static public int j = 0;
                  public A() { i++; j++; }
                  public void m() { i++; j++; }
                  public static void main(String[] args) {
                    System.out.println(\"START\");
                    new A().m();  // OK
                    System.out.println(\"MID\");
                    new A().m();
                    System.out.println(\"END\");
                  }
                }
                """
                ,"START"
                ,"MID"
                ,"/tt/A.java:4: verify: JML invariant is false on leaving method tt.A.A()"  // i == 1, j == 3, callee check
                ,"/$A/tt/A.jml:4: verify: Associated declaration"
                ,"/tt/A.java:4: verify: JML initially clause is false at exit from constructor"  // j == 3, callee check
                ,"/$A/tt/A.jml:3: verify: Associated declaration"
                ,"/tt/A.java:10: verify: JML assumed invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])" // caller check
                ,"/$A/tt/A.jml:4: verify: Associated declaration"
                ,"/tt/A.java:10: verify: JML initially clause is false at exit from constructor" // j == 3, caller check, assumption
                ,"/$A/tt/A.jml:3: verify: Associated declaration"
                ,"/tt/A.java:10: verify: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/A.jml:4: verify: Associated declaration"
                ,"/tt/A.java:5: verify: JML assumed invariant is false on entering method tt.A.m()"
                ,"/$A/tt/A.jml:4: verify: Associated declaration"
                ,"/tt/A.java:5: verify: JML invariant is false on leaving method tt.A.m()"
                ,"/$A/tt/A.jml:4: verify: Associated declaration"
                ,"/tt/A.java:10: verify: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/A.jml:4: verify: Associated declaration"
                ,"END"
                );
    }

    @Test public void testConstraint() {
        addMockFile("$A/tt/A.jml","package tt; public class A { \n"
                +"//@ constraint i == \\old(i)+1; \n "
                +"void m(); \n"
                +"}"
                );
        helpRacText("tt.A","package tt; public class A { \n"
                +"int i = 1;  \n "
                +"void m() { i *= 2; }  \n "
                +"public static void main(String[] args) { \n"
                +"A a = new A();\n"
                +"System.out.println(\"START\"); \n"
                +"a.m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"a.m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"START"
                ,"MID"
                ,"/tt/A.java:3: JML constraint clause is false on leaving method"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:9: JML constraint clause is false on leaving method"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"END"
                );
    }

    @Test public void testHelper() {
        addMockFile("$A/tt/A.jml","package tt; public class A { \n"
                +"//@ invariant i == 0; \n "
                +"/*@ private helper */ void m(); \n"
                +"}"
                );
        helpRacText("tt.A","package tt; public class A { \n"
                +"int i = 0;  \n "
                +"private void m() { i = 1-i; }  \n "
                +"public static void main(String[] args) { \n"
                +"new A().m(); "
                +"System.out.println(\"MID\"); "
                +"new A().m(); "
                +"System.out.println(\"END\"); "
                +"}}"
                ,"MID"
                ,"END"
                );
    }

    @Test public void testSuchThat() {
        addOptions("--rac-show-source=source");
        helpRacText("tt.A",
                """
                package tt;
                public class A {
                    static int j = 5; //@ in i;
                    //@ static model int i;
                    //@ static represents i \\such_that i == j+1;
                    public static void main(String[] args) {
                        System.out.println("END");
                    }
                }
                """
                ,"/tt/A.java:4: warning: JML model field does not have a representation: i",26
                ,"/tt/A.java:5: Note: Not implemented for runtime assertion checking: relational represents clauses (\\such_that)",16 // FIXME -point to the \such_that token instead?
                ,"END"
                );
    }
   
    @Test public void testModelField() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"static int j = 5; //@ in i; \n "
                +"//@ static model int i; \n "
                +"//@ static represents i = j+1; \n "
                +"public static void main(String[] args) { \n"
                +"//@ set System.out.println(\"A \" + i); \n"
                +" j = 10; \n"
                +"//@ set System.out.println(\"A \" + i); \n"
                +"System.out.println(\"END\"); "
                +"}"
                +"//@ static ghost int ii; \n "
                +"}"
                ,"A 6"
                ,"A 11"
                ,"END"
                );
    }
   
    // FIXME - this results of this test are different when run standalone
    @Test public void testModelFieldST() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"static int j = 5; //@ in i ; \n "
                +"//@ static model int i; \n "
                +"//@ static represents i \\such_that i==j+1; \n "
                +"//@ static represents i =j+1; \n "
                +"public static void main(String[] args) { \n"
                +"//@ set System.out.println(\"A \" + i); \n"
                +" j = 10; \n"
                +"//@ set System.out.println(\"A \" + i); \n"
                +"System.out.println(\"END\"); "
                +"}"
                +"//@ static ghost int ii; \n "
                +"}"
                ,"/tt/A.java:4: Note: Not implemented for runtime assertion checking: relational represents clauses (\\such_that)",13
                ,"A 6"
                ,"A 11"
                ,"END"
                );
    }
   
    /** Duplicate represents */
    @Test public void testModelField1() {
        continueAnyway = true;
        helpRacText("tt.A","package tt; public class A { \n"
                +"static int j = 5; //@ in i;\n "
                +"//@ static model int i; \n "
                +"//@ static represents i = j+1; \n "
                +"//@ static represents i = j; \n "
                +"public static void main(String[] args) { \n"
                +"//@ set System.out.println(\"A \" + i); \n"
                +" j = 10; \n"
                +"//@ set System.out.println(\"A \" + i); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:5: warning: Duplicate represents clause - only the first is used for RAC",13
                ,"A 6"
                ,"A 11"
                ,"END"
                );
    }
   
    // TODO - the following two tests fail when the compile policy is
    // SIMPLE instead of BY_TODO - for some reason the principal class
    // file (PA or QA) does not get written.
   
    /** Represents with super model field */
    @Test public void testModelField3() {
        continueAnyway = true; // That is, even though there are compile errors
        helpRacText("tt.PA","package tt; public class PA extends PB { \n"
                +" int j = 5; //@ in i;\n "
                +"//@  represents i = j+1; \n "
                +"public static void main(String[] args) { \n"
                +"PA a = new PA();\n"
                +"PB b = new PB();\n"
                +"//@ set System.out.println(\"A \" + a.i); \n"
                +"//@ set System.out.println(\"B \" + b.i); \n"
                +"b = new PA();\n"
                +"//@ set System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\");\n"
                +"}}\n"
                +"class PB { //@ model  int i;  \n}"
                ,"/tt/PA.java:13: warning: JML model field does not have a representation: i",27
                ,"A 6"
                ,"B 0"
                ,"B 6"
                ,"END"
                );
    }

    /** Represents with super model field */
    @Test public void testModelField3a() {
        helpRacText("tt.PA","package tt; public class PA extends PB { \n"
                +" int j = 5; //@ in i;\n "
                +"//@  represents super.i = j+1; \n "
                +"public static void main(String[] args) { \n"
                +"PA a = new PA();\n"
                +"PB b = new PB();\n"
                +"//@ set System.out.println(\"A \" + a.i); \n"
                +"//@ set System.out.println(\"B \" + b.i); \n"
                +"b = new PA();\n"
                +"//@ set System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); \n"
                +"}} class PB { //@ model protected int i; represents i = 100; }\n"
                ,"A 6"
                ,"B 100"
                ,"B 6"
                ,"END"
                );
    }

    /** Represents with super model field */
    @Test public void testModelField3b() {
        helpRacText("tt.PA","package tt; public class PA extends PB { \n"
                +" int j = 5; //@ in i;\n "
                +"//@  represents super.i = j+1; \n "
                +"public static void main(String[] args) { \n"
                +"PA a = new PA();\n"
                +"//@ set System.out.println(\"A \" + a.i); \n"
                +"PB b = new PA();\n"
                +"//@ set System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); \n"
                +"}} class PB { //@ model protected int i; }\n"
                ,"/tt/PA.java:10: warning: JML model field does not have a representation: i",39
                ,"A 6"
                ,"B 6"
                ,"END"
                );
    }

    /** Using a model field in a field access */
    @Test public void testModelField1a() {
        helpRacText("tt.PA",
                """
                package tt;
                public class PA {
                    static int j = 5; //@ in i;
                    //@ model int i; represents i = j;
                    public static void main(String[] args) {
                        PA a = new PA();
                        //@ set System.out.println(\"A \" + a.i);
                        PB b = new PB();
                        //@ set System.out.println(\"B \" + b.i);
                        System.out.println(\"END\");
                    }
                }
                class PB {
                    //@ model int i; represents i = PA.j+1;
                }
                """
                ,"A 5"
                ,"B 6"
                ,"END"
                );
    }

    /** Represents with super model field */
    @Test public void testModelField4() {
        addOptions("--rac-missing-model-field-rep=zero");
        helpRacText("tt.QA",
                """
                package tt;
                public class QA extends QB {
                  int j = 5;
                  public static void main(String[] args) {
                    QA a = new QA();
                    QB b = new QB();
                    //@ set System.out.println(\"A \" + a.i);
                    //@ set System.out.println(\"B \" + b.i);
                    b = new QA();
                    //@ set System.out.println(\"B \" + b.i);
                    System.out.println(\"END\");
                  }
                }
                class QB { //@ model  int i;
                }
                """
                ,"/tt/QA.java:14: warning: JML substituting zero-equivalent representation because model field does not have a representation: i",27
                ,"A 0"
                ,"B 0"
                ,"B 0"
                ,"END"
                );
    }

    /** Model field with no represents */
    @Test public void testModelField2() {
        addOptions("--rac-missing-model-field-rep=skip");
        expectedExit = 0;
        continueAnyway = true;
        helpRacText("tt.A",
                """
                package tt; public class A {
                  static int j = 5;
                  //@ static model int i;
                  public static void main(String[] args) {
                    //@ set System.out.println(\"A \" + i);
                    System.out.println(\"END\");
                  }
                }
                """
                ,"/tt/A.java:3: warning: JML model field does not have a representation: i", 24
                ,"/tt/A.java:5: warning: JML ignoring statement because model field does not have a representation: tt.A.i",39
                ,"END"
        );
    }

    /** Model field with no represents */
    @Test public void testModelField2x() {
        addOptions("--rac-missing-model-field-rep=zero");
        expectedExit = 0;
        continueAnyway = true;
        helpRacText("tt.A",
                """
                package tt; public class A {
                  static int j = 5;
                  //@ static model int i;
                  public static void main(String[] args) {
                    //@ set System.out.println(\"A \" + i);
                    System.out.println(\"END\");
                  }
                }
                """
                ,"/tt/A.java:3: warning: JML substituting zero-equivalent representation because model field does not have a representation: i", 24
                ,"A 0"
                ,"END"
        );
    }
   
    /** Forall, exists quantifier */
    @Test public void testForallQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost boolean n = (\\forall int i; 0<=i && i<=5; i >= 2); \n "
                +"//@ ghost boolean nn = (\\exists int i; 0<=i && i<=5; i >= 2); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A false true"
                ,"END"
        );
    }
   
    /** Forall, exists quantifier */
    @Test public void testForallQuantifier2() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost boolean n = (\\forall int i; 0<=i && i<=5; i >= 0); \n "
                +"//@ ghost boolean nn = (\\exists int i; 0<=i && i<=5; i >= 6); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A true false"
                ,"END"
        );
    }
   
    /** Forall, exists quantifier */
    @Test public void testForallQuantifier3() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost boolean n = (\\forall int i; ; i >= 0); \n "
                +"//@ set System.out.println(\"A \" + n ); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:3: warning: Runtime assertion checking is not implemented for this type or number of declarations in a quantified expression",25
                ,"A false"
                ,"END"
        );
    }
   
    /** Forall, exists quantifier */
    @Test public void testForallQuantifier5() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost boolean n = (\\exists int i; i == 4; i >= 3); \n "
                +"//@ ghost boolean nn = (\\exists int i; !(i < 0 || i > 5); i == 3); \n "
                +"//@ set nn &= (\\exists int i; 0 < i < 5; i == 3); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A true true"
                ,"END"
        );
    }
   
    @Test public void testForallQuantifier4() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost boolean n = (\\forall int i; 0<i && i<=5; (\\exists int j; 0<=j && j < 5; j<i)); \n "
                +"//@ ghost boolean nn = (\\forall int i; 0<=i && i<=5; (\\exists int j; 0<=j && j < 5; j<i)); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A true false"
                ,"END"
        );
    }
    
    /** Numof quantifier */
    @Test public void testCountQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n1 = (\\num_of int i; 0 <= i && i <= 5; true); \n "
                +"//@ ghost long n2 = (\\num_of int i; 0 < i && i < 5; true); \n "
                +"//@ set System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 6 4"
                ,"END"
        );
    }
    
    /** Numof quantifier */
    @Test public void testCountQuantifier3() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n = (\\num_of int i; 0 <= i && i < 5; i >= 2); \n "
                +"//@ ghost long nn = (\\num_of int i; 0 <= i && i < 5; false); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 3 0"
                ,"END"
        );
    }
    
    /** Numof quantifier */
    @Test public void testCountQuantifierExt() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static int m = 2;\n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n = (\\num_of int i; 0 <= i && i < 5; i >= m); \n "
                +"//@ ghost long nn = (\\num_of int i; 0 <= i && i < 5; m > 0); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn ); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 3 5"
                ,"END"
        );
    }
    
    /** Possible implementation of the \num_of quantifier */
    @Test public void testCountQuantifierExtA() {
        helpRacText("tt.A",
                """
                package tt; public class A {
                    public static int m = 2;
                    public static void main(String[] argv) {
                    /*@ ghost var v = new org.jmlspecs.runtime.Utils.ValueInt() {
                            public int value(final Object[] args) {
                                int count = 0;
                                int lo = (Integer)(args[0]);
                                int hi = (Integer)(args[1]);
                                int i = lo;
                                while (i <= hi) {
                                    if (i>=lo && i<=hi) count++; i++;
                                }
                                return count;
                            }
                        };
                        ghost int nnn = v.value(new Object[]{0,5});
                        set System.out.println(\"A \" + nnn );
                    @*/
                    System.out.println(\"END\");
                }}
                """
                ,"A 6"
                ,"END"
        );
    }
    
    /** Possible implementation of the \num_of quantifier */
    //  FIXME - crashes, despite its similarity to the test above
    @Test public void testCountQuantifierExtB() {
        helpRacText("tt.A",
                """
                package tt; public class A {
                    public static int m = 2;
                    public static void main(String[] argv) {
                    /*@ ghost var nnn = new org.jmlspecs.runtime.Utils.ValueInt() {
                            public int value(final Object[] args) {
                                int count = 0;
                                int lo = (Integer)(args[0]);
                                int hi = (Integer)(args[1]);
                                int i = lo;
                                while (i <= hi) {
                                    if (i>=lo && i<=hi) count++;
                                    i++;
                                }
                                return count;
                            }
                        }.value(new Object[]{0,5});
                        set System.out.println(\"A \" + nnn );
                    @*/
                    System.out.println(\"END\");
                }}
                """
                ,"A 6"
                ,"END"
        );
    }
    
    /** Numof quantifier */
    @Test public void testCountQuantifierExtE() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static int m = 2;\n"
                +"//@ ensures (\\num_of int i; 0 <= i && i < 5; i >= m) == 3;\n"
                +"//@ ensures (\\num_of int i; 0 <= i && i < 5; i >= m) == 4;\n"
                +"public static void main(String[] argv) { \n "
                +"System.out.println(\"END\"); "
                +"}}"
                ,"END"
                ,"/tt/A.java:5: verify: JML postcondition is false"
                ,"/tt/A.java:4: verify: Associated declaration"
        );
    }
    
    // FIXME - quantifiers witrh multiple declarations
    /** Numof quantifier */
    @Test public void testCountTwo() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n1 = (\\num_of int i,j; 0 <= i && i <= 5 && 0 <= j && j < i; true); \n "
                +"//@ set System.out.println(\"A \" + n1); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:3: warning: Runtime assertion checking is not implemented for this type or number of declarations in a quantified expression",23
                ,"A 0"
                ,"END"
        );
    }
    
    /** Sum quantifier */
    @Test public void testSumQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\sum int i; 0<i && i<=5; i+1); \n "
                +"//@ ghost int nn = (\\sum int i; 0<i && i<0; i+1); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 20 0"
                ,"END"
        );
    }
    
    /** Sum quantifier */
    @Test public void testProdQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\product int i; 0<i && i<=5; i+1); \n "
                +"//@ ghost int nn = (\\product int i; 0<i && i<0; i+1); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 720 1"
                ,"END"
        );
    }
    
    /** Max quantifier */
    @Test public void testMaxQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\max int i; 0<=i && i<=5 && (i%2)==0; i+1); \n "
                +"//@ ghost int nn = (\\max int i; 0<i && i<0; i+1); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 -2147483648"
                ,"END"
        );
    }
    
    /** Max quantifier, with function call */
    @Test public void testMaxQuantifier2() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"  public static int inc(int i) { return i + 10; }\n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\max int i; 0<=i && i<=5 && (i%2)==0; inc(i)); \n "
                +"//@ ghost int nn = (\\max int i; -9<=i && i<=5 ; Math.abs(i)); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 14 9"
                ,"END"
        );
    }
    
    /**  quantifier over short */
    @Test public void testShortQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost short n1 = (\\max int i; 0<=i && i<=5; (short)(i+10)); \n "
                +"//@ ghost short n2 = (\\min int i; 0<=i && i<=5; (short)(i+10)); \n "
                +"//@ set System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15 10"
                ,"END"
        );
    }
    
    /**  quantifier over short */
    @Test public void testShortQuantifierB() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost short n1 = (\\max short i; 2<=i && i<=5; i); \n "
                +"//@ ghost short n2 = (\\min short i; 2<=i && i<=5; i); \n "
                +"//@ set System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 2"
                ,"END"
        );
    }
    
    /**  quantifier over byte */
    @Test public void testByteQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost byte n1 = (\\max int i; 2<=i && i<=5; (byte)i); \n "
                +"//@ ghost byte n2 = (\\min int i; 2<=i && i<=5; (byte)i); \n "
                +"//@ set System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 2"
                ,"END"
        );
    }
    
    /**  quantifier over byte */
    @Test public void testByteQuantifierB() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost byte n1 = (\\max byte i; 2<=i && i<=5; i); \n "
                +"//@ ghost byte n2 = (\\min byte i; 2<=i && i<=5; i); \n "
                +"//@ set System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 2"
                ,"END"
        );
    }
    
    /**  quantifier over long */
    @Test public void testLongQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n1 = (\\max int i; 0<=i && i<=5; (i+10L)); \n "
                +"//@ ghost long n2 = (\\min int i; 0<=i && i<=5; (i+10L)); \n "
                +"//@ set System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15 10"
                ,"END"
        );
    }
    
    /**  quantifier over long */
    @Test public void testLongQuantifierB() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n1 = (\\max long i; 0<=i && i<=5; (i+10L)); \n "
                +"//@ ghost long n2 = (\\min long i; 0<=i && i<=5; (i+10L)); \n "
                +"//@ set System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15 10"
                ,"END"
        );
    }
    
    /**  quantifier over double */
    @Test public void testDoubleQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost double n1 = (\\max int i; 0<=i && i<=5; (double)(i+10.5)); \n "
                +"//@ ghost double n2 = (\\min int i; 0<=i && i<=5; (double)(i+10.5)); \n "
                +"//@ set System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15.5 10.5"
                ,"END"
        );
    }
    
    /**  quantifier over float */
    @Test public void testFloatQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost float n1 = (\\max int i; 0<=i && i<=5; (float)(i+10.5)); \n "
                +"//@ ghost float n2 = (\\min int i; 0<=i && i<=5; (float)(i+10.5)); \n "
                +"//@ set System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15.5 10.5"
                ,"END"
        );
    }
    
    /**  quantifier over char */
    @Test public void testCharQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost char n1 = (\\max int i; 'a'<i && i<='q'; (char)i); \n "
                +"//@ ghost char n2 = (\\min int i; 'a'<i && i<='q'; (char)i); \n "
                +"//@ set System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A q b"
                ,"END"
        );
    }
    
    /**  quantifier over char */
    @Test public void testCharQuantifierB() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost char n1 = (\\max char i; 'a'<i && i<='q'; i); \n "
                +"//@ ghost char n2 = (\\min char i; 'a'<i && i<='q'; i); \n "
                +"//@ set System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A q b"
                ,"END"
        );
    }
    
    /** Min quantifier */
    @Test public void testMinQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\min int i; 0<=i && i<=5 && (i%2)==1; i+1); \n "
                +"//@ ghost int nn = (\\min int i; 0<i && i<0; i+1); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 2 2147483647"
                ,"END"
        );
    }
    
    /** Max quantifier */
    @Test public void testMaxLongQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n = (\\max int i; 0<=i && i<=5 && (i%2)==0; (long)i+1); \n "
                +"//@ ghost long nn = (\\max int i; 0<i && i<0; i+1); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 -2147483648"
                ,"END"
        );
    }
    
    /** Min quantifier */
    @Test public void testMinLongQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n = (\\min int i; 0<=i && i<=5 && (i%2)==1; (long)i+1); \n "
                +"//@ ghost long nn = (\\min int i; 0<i && i<0; i+1); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 2 2147483647"
                ,"END"
        );
    }
    
    /** Max quantifier */
    @Test public void testMaxDoubleQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost double n = (\\max int i; 0<=i && i<=5 && (i%2)==0; (double)i+1); \n "
                +"//@ ghost double nn = (\\max int i; 0<i && i<0; i+1); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5.0 -2.147483648E9"
                ,"END"
        );
    }
    
    /** double quantifier */
    @Test public void testMinDoubleQuantifier() {
        helpRacText("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost double n = (\\min int i; 0<=i && i<=5 && (i%2)==1; (double)i+1); \n "
                +"//@ ghost double nn = (\\min int i; 0<i && i<0; (double)i+1); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 2.0 1.7976931348623157E308"
                ,"END"
        );
    }
    
    /** boolean quantifier */
    @Test public void testBooleanQuantifier() {
        helpRacText("tt.A",
                """
                package tt; public class A {
                  public static void main(String[] argv) {
                    boolean bb = true;
                    //@ ghost int n = (\\sum boolean i; bb; (i?2:5));
                    //@ ghost int nn = (\\sum boolean i; !i; (i?2:5));
                    //@ ghost int nnn = (\\sum boolean i; i; (i?2:5));
                    //@ ghost int nnnn = (\\sum boolean i; false; (i?2:5));
                    //@ set System.out.println("A " + n + " " + nn + " " + nnn + " " + nnnn);
                    System.out.println(\"END\");
                  }
                }
                """
                ,"A 7 5 2 0"
                ,"END"
        );
    }
    
    /** Object quantifier */
    @Test public void testObjectQuantifier() {
        helpRacText("tt.A","package tt; import java.util.*; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +" List<Object> list = new LinkedList<Object>();\n"
                +"//@ ghost long n = (\\num_of Object o; list.contains(o); true); \n "
                +" Object oo = new Object(); list.add(new Object());\n"
                +"//@ ghost long nn = (\\num_of Object o; list.contains(o) && true; true); \n "
                +" list.add(oo);\n"
                +"//@ ghost long nnn = (\\num_of Object o; list.contains(o) && o == oo; true); \n "
                +"//@ set System.out.println(\"A \" + n + \" \" + nn + \" \" + nnn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 0 1 1"
                ,"END"
        );
    }
    
    /** Represents with super model field */
    @Test public void testModelField5a() {
        continueAnyway = true;
        addMockFile("$A/tt/B.java","package tt; class B{ //@ model int i; \n}");
        helpRacText("tt.A","package tt; public class A extends tt.B { \n"
                +" int j = 5; \n "
                +"public static void main(String[] args) { \n"
                +"A a = new A();\n"
                +"tt.B b = new tt.B();\n"
                +"// @ debug System.out.println(\"A \" + a.i); \n"
                +"// @ debug System.out.println(\"B \" + b.i); \n"
                +"b = new A();\n"
                +"// @ debug System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/$A/tt/B.java:1: warning: JML model field does not have a representation: i",36
                ,"END"
                );
    }

    /** Represents with super model field */
    @Test public void testModelField5() {
        addOptions("--rac-missing-model-field-rep=zero");
        continueAnyway = true;
        addMockFile("$A/tt/B.java","package tt; class B{ //@ model int i; \n}");
        helpRacText("tt.A","package tt; public class A extends tt.B { \n"
                +" int j = 5; \n "
                +"public static void main(String[] args) { \n"
                +"A a = new A();\n"
                +"tt.B b = new tt.B();\n"
                +"//@ set System.out.println(\"A \" + a.i); \n"
                +"//@ set System.out.println(\"B \" + b.i); \n"
                +"b = new A();\n"
                +"//@ set System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/$A/tt/B.java:1: warning: JML substituting zero-equivalent representation because model field does not have a representation: i",36
                ,"A 0"  //FIXME - check this
                ,"B 0"
                ,"B 0"
                ,"END"
                );
    }

    @Test public void testNullAssignment() {
        helpRacText("tt.A","package tt; import org.jmlspecs.annotation.*; @NullableByDefault public class A  { \n"
                +"/*@non_null*/ static String o=\"\",oo=\"\"; static Object ooo;\n"
                +"public static void main(String[] args) { \n"
                +"   oo = null;\n"
                +"   ooo = null;\n"
                +"   /*@ non_null*/ String local = \"\";\n"
                +"   local = (String)ooo;"
                +"System.out.println(\"END\"); "
                +"}} class B { //@ model  int i; represents i = 0; \n}"
                ,"/tt/A.java:4: JML assignment of null to a non_null variable"
                ,"/tt/A.java:7: JML assignment of null to a non_null variable"
                ,"END"
                ,"/tt/A.java:2: JML non-null field is null"
                );
    }

    @Test public void testNullAssignment2() {
        helpRacText("tt.A","package tt; import org.jmlspecs.annotation.*; @NullableByDefault public class A  { \n"
                +"/*@non_null*/ static Object o,oo; static Object ooo; \n"
                +"public static void main(String[] args) { \n"
                +"   A.oo = null;\n"
                +"   A.ooo = null;\n"
                +"System.out.println(\"END\"); "
                +"}} "
                ,"/tt/A.java:2: JML static initialization may be incorrect: non-null static field has null value: o"
                ,"/tt/A.java:2: JML static initialization may be incorrect: non-null static field has null value: oo"
                ,"/tt/A.java:4: JML assignment of null to a non_null variable"
                ,"END"
                ,"/tt/A.java:2: JML non-null field is null"
                ,"/tt/A.java:2: JML non-null field is null"
                );
    }
    
    // FIXME - no warning when exception is allowed?
    @Test public void testNullReference() {
        expectedRACExit = 1;
        helpRacText("tt.A",
                """
                package tt; import org.jmlspecs.annotation.*; public class A  {
                  /*@ nullable*/ static A a = null;
                  /*@ nullable*/ A b = null;
                  static int i = 9;
                  public static void main(String[] args) {
                    int j; j = A.i;
                    j = a.i; // No null dereference warning since i is static
                    try { j = a.b.i; } catch (NullPointerException e) { System.out.println(e); } //@ forbid NullPointerException;// Exception
                    //@ ghost int k; set k = A.i;
                    //@ set k = a.i;
                    //@ set k = a.b.i; // ERROR
                    System.out.println("END");
                  }
                }
                """
                ,"/tt/A.java:8: verify: JML A null object is dereferenced"
                ,"java.lang.NullPointerException: Cannot read field \"b\" because \"tt.A.a\" is null"
                ,"/tt/A.java:11: verify: JML A null object is dereferenced within a JML expression"
                ,"Exception in thread \"main\" java.lang.NullPointerException: Cannot read field \"b\" because \"tt.A.a\" is null"
                ,"\tat tt.A.main(A.java:11)"
                );
    }

    @Test public void testNullReference2() {
        expectedRACExit = 1;
        helpRacText("tt.A",
                """
                package tt; import org.jmlspecs.annotation.*; public class A  {
                  /*@ nullable*/ static A a = null;
                  /*@ nullable*/ A b = null;
                  static int i = 9;
                  public static void main(String[] args) {
                    int j; j = A.i;
                    j = a.i; // No null dereference warning since i is static
                    try { j = a.b.i; } catch (NullPointerException e) { System.out.println(e); } // Exception
                    //@ ghost int k; set k = A.i;
                    //@ set k = a.i;
                    //@ set k = a.b.i; // ERROR
                    System.out.println("END");
                  }
                }
                """
                ,"java.lang.NullPointerException: Cannot read field \"b\" because \"tt.A.a\" is null"
                ,"/tt/A.java:11: verify: JML A null object is dereferenced within a JML expression"
                ,"Exception in thread \"main\" java.lang.NullPointerException: Cannot read field \"b\" because \"tt.A.a\" is null"
                ,"\tat tt.A.main(A.java:11)"
                );
    }

    @Test public void testNullInitialization() {
        helpRacText("tt.A","package tt; /*@nullable_by_default*/ public class A  { \n"
                +"/*@non_null*/ static Object o,oo = null; \n"
                +"static String ooo = null;\n"
                +"//@ non_null ghost static Object oooo = null;\n"
                +"public static void main(String[] args) { \n"
                +"   /*@ non_null*/ String local = ooo;\n"
                +"   //@ ghost non_null String loc = null; \n"
                +"System.out.println(\"END\"); "
                +"}} "
                ,"/tt/A.java:2: JML null initialization of non_null field oo"
                ,"/tt/A.java:4: JML null initialization of non_null field oooo"
                ,"/tt/A.java:2: JML static initialization may be incorrect: non-null static field has null value: o"
                ,"/tt/A.java:2: JML static initialization may be incorrect: non-null static field has null value: oo"
                ,"/tt/A.java:4: JML static initialization may be incorrect: non-null static field has null value: oooo"
                ,"/tt/A.java:6: JML null initialization of non_null field local"
                ,"/tt/A.java:7: JML null initialization of non_null field loc"
                ,"END"
                ,"/tt/A.java:2: JML non-null field is null" // FIXME - add the name of the field
                ,"/tt/A.java:2: JML non-null field is null"
                ,"/tt/A.java:4: JML non-null field is null"
                );
    }
    
    @Test public void testNullDefault() {
        helpRacText("tt.A","package tt; public class A  { \n"
                +"/*@nullable*/ static Object o,oo = null; \n"
                +"static Object ooo = null;\n"
                +"//@ nullable ghost static Object oooo = null;\n"
                +"public static void main(String[] args) { \n"
                +"   /*@ nullable*/ String local = (String)ooo;\n"
                +"   //@ ghost String loc = null; \n"
                +"System.out.println(\"END\"); "
                +"}} class B { \n}"
                ,"/tt/A.java:3: JML null initialization of non_null field ooo"
                ,"/tt/A.java:3: JML static initialization may be incorrect: non-null static field has null value: ooo"
                ,"/tt/A.java:6: JML non-null field is null"
                ,"/tt/A.java:7: JML null initialization of non_null field loc"
                ,"END"
                ,"/tt/A.java:3: JML non-null field is null"
                );
    }
    
    @Test public void testNullInit() {
        helpRacText("tt.A","package tt; public class A  { \n"
                +"/*@nullable*/ public static Object o,oo = null; \n"
                +"public static Object ooo = null;\n"
                +"//@ public static invariant o != ooo;\n"
                +"//@ nullable ghost static Object oooo = null;\n"
                +"public static void main(String[] args) { \n"
                +"   /*@ nullable*/ String local = (String)ooo;\n"
                +"   //@ ghost String loc = null; \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:3: JML null initialization of non_null field ooo"
                ,"/tt/A.java:3: JML static initialization may be incorrect: non-null static field has null value: ooo"
                ,"/tt/A.java:1: JML static invariant is false"
                ,"/tt/A.java:4: Associated declaration"
                ,"/tt/A.java:6: JML assumed invariant is false on entering method tt.A.main(java.lang.String[])"
                ,"/tt/A.java:4: Associated declaration"
                ,"/tt/A.java:7: JML non-null field is null"
                ,"/tt/A.java:8: JML null initialization of non_null field loc"
                ,"END"
                ,"/tt/A.java:6: JML invariant is false on leaving method tt.A.main(java.lang.String[])"
                ,"/tt/A.java:4: Associated declaration"
                ,"/tt/A.java:3: JML non-null field is null"
                );
    }
    
    // FIXME
    // check readable, writable, monitors for
    // check modifiers?
    // check more method clauses
    // check other expression types
    // what about assignable
    // check any problems with grouped clauses
    @Test public void testNotImplemented() {
        expectedExit = 1;
        helpRacText("tt.A","package tt; public class A  { \n"
                +"//@ axiom true;\n"
                +"//@ public invariant \\duration(true) == 0;\n"
                +"//@ public model long i;\n"
                +"//@ public represents i =  \\duration(true);\n"
                +"//@ public constraint \\duration(true) == 0;\n"
                +"//@ public initially \\duration(true) == 0;\n"
                +"public static void main(String[] args) { \n"
                +"    \n"
                +"    //@ assert \\duration(true) == 0;\n"
                +"    //@ assume \\duration(true) == 0;\n"
                +"    //@ ghost long k = \\duration(true);\n"
                +"    //@ set k = \\duration(true);\n"
                +"    //@ set k = \\duration(true);\n"
                +"    System.out.println(\"END\"); "
                +"}\n"
                +"//@ ghost long z = \\duration(true);\n"
                +"//@ ghost long[] zz = { \\duration(true) } ;\n"
                +"/*@ requires \\duration(true) == 0;*/\n"
                +"int ma() { return 0; }\n"
                +"//@ ensures \\duration(true) == 0;\n"
                +"//@ signals (Exception ex) \\duration(true) == 0;\n"
                +"//@ signals_only RuntimeException;\n" 
                +"//@ diverges \\duration(true) == 0;\n" // line 23
                +"//@ duration  \\duration(true);\n"
                +"//@ working_space \\duration(true);\n"
                +"int mb() { return 0; }\n"
                +"}"    // FIXME - the column positions are unexpected
                ,"/tt/A.java:10: Note: Not implemented for runtime assertion checking: assert statement containing \\duration",25
                ,"/tt/A.java:11: Note: Not implemented for runtime assertion checking: assume statement containing \\duration",25
                ,"/tt/A.java:12: Note: Not implemented for runtime assertion checking: ghost declaration containing \\duration",33
                ,"/tt/A.java:13: Note: Not implemented for runtime assertion checking: set statement containing \\duration",26
                ,"/tt/A.java:14: Note: Not implemented for runtime assertion checking: set statement containing \\duration",26   // FIXME - should say debug not set
                ,"/tt/A.java:16: Note: Not implemented for runtime assertion checking: ghost declaration containing \\duration",29
                ,"/tt/A.java:17: Note: Not implemented for runtime assertion checking: ghost declaration containing \\duration",34
                ,"/tt/A.java:18: Note: Not implemented for runtime assertion checking: requires clause containing \\duration",23
                ,"/tt/A.java:6: Note: Not implemented for runtime assertion checking: constraint clause containing \\duration",32
                ,"/tt/A.java:20: Note: Not implemented for runtime assertion checking: ensures clause containing \\duration",22
                ,"/tt/A.java:21: Note: Not implemented for runtime assertion checking: signals clause containing \\duration",37
                ,"/tt/A.java:24: Note: Not implemented for runtime assertion checking: duration clause containing \\duration",24
                ,"/tt/A.java:25: Note: Not implemented for runtime assertion checking: working_space clause containing \\duration",28
                ,"/tt/A.java:3: Note: Not implemented for runtime assertion checking: invariant clause containing \\duration",31
                ,"/tt/A.java:7: Note: Not implemented for runtime assertion checking: initially clause containing \\duration",31
                ,"/tt/A.java:5: Note: Not implemented for runtime assertion checking: represents clause containing \\duration",37
                ,"/tt/A.java:5: error: Unrecoverable situation: Unimplemented construct in a method or model method or invariant or represents clause",37   // FIXME
                ,"END"
                );
    }
    
    @Test public void testNotImplemented2() {
        helpRacText("tt.A","package tt; public class A  { \n"
                +"public static void main(String[] args) { \n"
                +"    m();\n"
                +"    System.out.println(\"END\"); "
                +"}\n"
                +"//@   requires \\duration(true) == 0;\n"
                +"//@   ensures true;\n"
                +"//@ also\n"
                +"//@   requires \\duration(true) == 0;\n"
                +"//@   signals (Exception ex) true;\n"
                +"//@ also\n"
                +"//@   requires \\duration(true) == 0;\n"
                +"//@   signals_only RuntimeException;\n"
                +"//@ also\n"
                +"//@   ensures true;\n"
                +"static int m() { return 0; }\n"
                +"}"
                ,"/tt/A.java:5: Note: Not implemented for runtime assertion checking: requires clause containing \\duration",25
                ,"/tt/A.java:8: Note: Not implemented for runtime assertion checking: requires clause containing \\duration",25
                ,"/tt/A.java:11: Note: Not implemented for runtime assertion checking: requires clause containing \\duration",25
                ,"END"
                );
    }

    // Testing inheritance of invariants; here m() is implemented for classes A and C, but not B
    @Test public void testSuperInvariant() {
        //addOptions("--rac-check-assumptions=false");
        helpRacText("tt.A","package tt; public class A  extends B { \n"
                +" public void m() {} //@ public  invariant i == 1; \n"
                +"public static void main(String[] args) { \n"
                +"   new A().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"   new B().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"   new C().m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                +"class B extends C { //@ public invariant i == 2; \n"
                +"}\n"
                +"class C { \n"  // Line 13
                +"  Object o = this; \n"
                +"  public int i=0; \n"
                +"  public void m() {} \n"
                +"  //@ public invariant i == 3; \n"
                +"}\n"
                ,"/tt/A.java:13: JML invariant is false on leaving method tt.C.C()"  // Invariant in C, exiting C()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:11: JML invariant is false on leaving method tt.B.B()" // Invariant in C, exiting B()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:11: JML invariant is false on leaving method tt.B.B()" // Invariant in B, exiting B()
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()" // Invariant in C, exiting A()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()" // Invariant in B, exiting A()
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()" // Invariant in A, exiting A()
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:4: JML assumed invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])" // Invariant in C, exiting caller
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:4: JML assumed invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])" // Invariant in B, exiting caller
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:4: JML assumed invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])" // Invariant in A, exiting caller
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())" // Invariant in C, entering m
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())" // Invariant in B, entering m
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())" // Invariant in A, entering m
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:2: JML assumed invariant is false on entering method tt.A.m()" // Invariant in C, beginning m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:2: JML assumed invariant is false on entering method tt.A.m()" // Invariant in B, beginning m()
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:2: JML assumed invariant is false on entering method tt.A.m()" // Invariant in A, beginning m()
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on leaving method tt.A.m()" // Invariant in C, completing m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on leaving method tt.A.m()" // Invariant in B, completing m()
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on leaving method tt.A.m()" // Invariant in A, completing m()
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:4: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])" // Invariant in C, leaving m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:4: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])" // Invariant in B, leaving m()
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:4: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])" // Invariant in A, leaving m()
                ,"/tt/A.java:2: Associated declaration"
                ,"MID"
                ,"/tt/A.java:13: JML invariant is false on leaving method tt.C.C()"  // Invariant in C, exiting C()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:11: JML invariant is false on leaving method tt.B.B()" // Invariant in C, exiting B()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:11: JML invariant is false on leaving method tt.B.B()" // Invariant in B, exiting B()
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:6: JML assumed invariant is false on leaving method tt.B.B(), returning to tt.A.main(java.lang.String[])"
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:6: JML assumed invariant is false on leaving method tt.B.B(), returning to tt.A.main(java.lang.String[])"
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())" // Invariant in C, entering m() - this is C.m()
                ,"/tt/A.java:17: Associated declaration"
                // FIXME should be checking B's invariants as well, since the receiver is B, above
                ,"/tt/A.java:16: JML assumed invariant is false on entering method tt.C.m()" // Invariant in C, beginning m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:16: JML invariant is false on leaving method tt.C.m()" // Invariant in C, completing m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:6: JML assumed invariant is false on leaving method tt.C.m(), returning to tt.A.main(java.lang.String[])" // Invariant in C, exiting m()
                ,"/tt/A.java:17: Associated declaration"
                ,"MID"
                ,"/tt/A.java:13: JML invariant is false on leaving method tt.C.C()"  // Invariant in C, exiting C()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:8: JML assumed invariant is false on leaving method tt.C.C(), returning to tt.A.main(java.lang.String[])"  // Invariant in C, exiting C()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:8: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())" // Invariant in C, entering m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:16: JML assumed invariant is false on entering method tt.C.m()" // Invariant in C, entering m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:16: JML invariant is false on leaving method tt.C.m()" // Invariant in C, leaving m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:8: JML assumed invariant is false on leaving method tt.C.m(), returning to tt.A.main(java.lang.String[])" // Assumed Invariant in C, leaving m()
                ,"/tt/A.java:17: Associated declaration"
                ,"END"
                );
    }

    // Like above, but with separate files
    @Test public void testSuperInvariantB() {
        addMockFile("$A/tt/B.java","package tt; public class B extends tt.C { \n"
                +"//@ public invariant i == 2; \n"
                +"}\n"
                );
        addMockFile("$A/tt/C.java","package tt; public class C { \n"
                +"public int i=0; public void m() {} \n"
                +"//@ public invariant i == 3; \n"
                +"}\n"
                );
        helpRacText("tt.A","package tt; public class A  extends B { \n"
                +" public void m() {} //@public  invariant i == 1; \n"
                +"public static void main(String[] args) { \n"
                +"   new A().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"   new B().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"   new C().m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                ,"/$A/tt/C.java:1: JML invariant is false on leaving method tt.C.C()"  // leaving C() in A(), invariant in C
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/B.java:1: JML invariant is false on leaving method tt.B.B()"  
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/B.java:1: JML invariant is false on leaving method tt.B.B()"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:4: JML assumed invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:4: JML assumed invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:4: JML assumed invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])"
                ,"/tt/A.java:2: Associated declaration"
                
                ,"/tt/A.java:4: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/tt/A.java:2: Associated declaration"
                
                ,"/tt/A.java:2: JML assumed invariant is false on entering method tt.A.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:2: JML assumed invariant is false on entering method tt.A.m()"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:2: JML assumed invariant is false on entering method tt.A.m()"
                ,"/tt/A.java:2: Associated declaration"

                ,"/tt/A.java:2: JML invariant is false on leaving method tt.A.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on leaving method tt.A.m()"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on leaving method tt.A.m()"
                ,"/tt/A.java:2: Associated declaration"

                ,"/tt/A.java:4: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:4: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:4: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/tt/A.java:2: Associated declaration"
                ,"MID"
                ,"/$A/tt/C.java:1: JML invariant is false on leaving method tt.C.C()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/B.java:1: JML invariant is false on leaving method tt.B.B()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/B.java:1: JML invariant is false on leaving method tt.B.B()"
                ,"/$A/tt/B.java:2: Associated declaration"

                ,"/tt/A.java:6: JML assumed invariant is false on leaving method tt.B.B(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:6: JML assumed invariant is false on leaving method tt.B.B(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/B.java:2: Associated declaration"

                ,"/tt/A.java:6: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                // FIXME should be checking B's invariants as well, since the receiver is B, above
                
                ,"/$A/tt/C.java:2: JML assumed invariant is false on entering method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/C.java:2: JML invariant is false on leaving method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:6: JML assumed invariant is false on leaving method tt.C.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"MID"
                ,"/$A/tt/C.java:1: JML invariant is false on leaving method tt.C.C()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:8: JML assumed invariant is false on leaving method tt.C.C(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                
                ,"/tt/A.java:8: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/C.java:2: JML assumed invariant is false on entering method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/C.java:2: JML invariant is false on leaving method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:8: JML assumed invariant is false on leaving method tt.C.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"END"
                );
    }

    @Test public void testStaticInhInvariant() {
        addMockFile("$A/tt/B.java","package tt; public class B extends tt.C { \n"
                +"//@ static public invariant i == 2; \n"
                +"}\n"
                );
        addMockFile("$A/tt/C.java","package tt; public class C { \n"
                +"static public int i=0; static public void m() {} \n"
                +"//@ static public invariant i == 3; \n"
                +"}\n"
                );
        helpRacText("tt.A","package tt; public class A  extends tt.B { \n"
                +" //@ static public invariant i == 1; \n"
                +" static public void m() {}\n"
                +"public static void main(String[] args) { \n"
                +"System.out.println(\"A\"); \n"
                +"   A.m(); \n"
                +"System.out.println(\"B\"); \n"
                +"   tt.B.m(); \n"
                +"System.out.println(\"C\"); \n"
                +"   tt.C.m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                ,"/$A/tt/C.java:1: JML static invariant is false"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/B.java:1: JML static invariant is false"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/B.java:1: JML static invariant is false"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:1: JML static invariant is false"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:1: JML static invariant is false"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:1: JML static invariant is false"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:4: JML assumed invariant is false on entering method tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:4: JML assumed invariant is false on entering method tt.A.main(java.lang.String[])"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:4: JML assumed invariant is false on entering method tt.A.main(java.lang.String[])"
                ,"/tt/A.java:2: Associated declaration"
                ,"A" // line 18
                ,"/tt/A.java:6: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:3: JML assumed invariant is false on entering method tt.A.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:3: JML assumed invariant is false on entering method tt.A.m()"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:3: JML assumed invariant is false on entering method tt.A.m()"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:6: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:6: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:6: JML assumed invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/tt/A.java:2: Associated declaration"
                ,"B" // line 55
                ,"/tt/A.java:8: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/C.java:2: JML assumed invariant is false on entering method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/C.java:2: JML invariant is false on leaving method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:8: JML assumed invariant is false on leaving method tt.C.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"C" // line 68
                ,"/tt/A.java:10: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/C.java:2: JML assumed invariant is false on entering method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/C.java:2: JML invariant is false on leaving method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:10: JML assumed invariant is false on leaving method tt.C.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"END"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.main(java.lang.String[])"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.main(java.lang.String[])"
                ,"/tt/A.java:2: Associated declaration"
                );
    }
    
    // FIXME - many outputs need column numbers

    @Test public void testInheritedMethod() {
        addMockFile("$A/tt/B.java","package tt; public class B extends tt.C implements I { \n"
                +"//@ also ensures i == 2; \n"
                +"public void m() {} ; \n"
                +"}\n"
                );
        addMockFile("$A/tt/C.java","package tt; public class C implements I { \n"
                +"static public int i=0;  \n"
                +"//@ also ensures i == 3; \n"
                +" public void m() {} ; \n"
                +"}\n"
                );
        addMockFile("$A/tt/I.java","package tt; public interface I { \n"
                +"//@ ensures false; \n"
                +"public void m(); \n"
                +"}\n"
                );
        helpRacText("tt.A","package tt; public class A  extends tt.B { \n"
                +"//@ also ensures i == 2; \n"
                +"public void m() {} ; \n"

                +"public static void main(String[] args) { \n"
                +"System.out.println(\"A\"); \n"
                +"   (new A()).m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                ,"A"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/$A/tt/I.java:2: Associated declaration"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/$A/tt/I.java:2: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/tt/A.java:2: Associated declaration"
                ,"END"
                );
    }
    
    @Test public void testInheritedMethod2() {
        addMockFile("$A/tt/B.java","package tt; public class B extends ttt.C implements I { \n"
                +"//@ also private behavior ensures i == 2; \n"
                +"public void m() {} ; \n"
                +"}\n"
                );
        addMockFile("$A/ttt/C.java","package ttt; public class C implements tt.I { \n"
                +"static public int i=0;  \n"
                +"//@ also ensures i == 3; \n"
                +" public void m() {} ; \n"
                +"}\n"
                );
        addMockFile("$A/tt/I.java","package tt; public interface I { \n"
                +"//@ ensures false; \n"
                +"public void m(); \n"
                +"}\n"
                );
        helpRacText("tt.A","package tt; public class A  extends tt.B { \n"
                +"//@ also ensures i == 2; \n"
                +"public void m() {} ; \n"

                +"public static void main(String[] args) { \n"
                +"System.out.println(\"A\"); \n"
                +"   (new A()).m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                ,"A"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/$A/tt/I.java:2: Associated declaration"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/$A/ttt/C.java:3: Associated declaration"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/$A/tt/I.java:2: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/$A/ttt/C.java:3: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/tt/A.java:2: Associated declaration"
                ,"END"
                );
    }
    
    @Test public void testInheritedMethod3() {
        addMockFile("$A/tt/C.java","package tt; public class C { \n"
                +"static public int i=0;  \n"
                +"//@ requires kc == 3; ensures i == 3; \n"
                +" public void m(int kc) {} ; \n"
                +"}\n"
                );
        addMockFile("$A/tt/B.java","package tt; public class B extends C { \n"
                +"//@ also requires kb == 2; ensures i == 2; \n"
                +"public void m(int kb) {} ; \n"
                +"}\n"
                );
        helpRacText("tt.A","package tt; public class A  extends tt.B { \n"
                +"//@ also requires ka==1; ensures i == 1; \n"
                +"public void m(int ka) {} ; \n"

                +"public static void main(String[] args) { \n"
                +"   System.out.println(\"C\"); (new A()).m(3); \n"
                +"   System.out.println(\"B\"); (new A()).m(2); \n"
                +"   System.out.println(\"A\"); (new A()).m(1); \n"
                +"   System.out.println(\"NONE\"); (new A()).m(0); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                ,"C"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:5: JML postcondition is false"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"B"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"A"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:7: JML postcondition is false"
                ,"/tt/A.java:2: Associated declaration"
                ,"NONE"
                ,"/tt/A.java:8: JML precondition is false"
                ,"/tt/A.java:3: Associated declaration"
                ,"/tt/A.java:2: JML precondition is false"
                ,"END"
                );
    }
    
    @Test public void testAssignable() {
        helpRacText("tt.A","package tt; public class A {\n"
                +"  static public int j=0,k;\n"
                +"  //@ requires i > 0;\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures j == i;\n"
                +"  public static void setj(int i) {\n"
                +"    j = i;\n"
                +"  }\n"
                +"  //@ ensures j == 1;\n"
                +"  public static void main(String[] args) {\n"
                +"    setj(0);\n"
                +"  }\n"
                +"}\n"
                ,"/tt/A.java:11: JML precondition is false"
                ,"/tt/A.java:6: Associated declaration"
                ,"/tt/A.java:3: JML precondition is false"
                ,"/tt/A.java:10: JML postcondition is false"
                ,"/tt/A.java:9: Associated declaration"
        );
    }
    
    @Test public void testAssignable2() {
        helpRacText("tt.A","package tt; public class A {\n"
                +"  static public int j=0,k;\n"
                +"  //@ requires i > 0;\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures j == i;\n"
                +"  public static void setj(int i) {\n"
                +"    k = i;\n" // Intentionally k - but precondition is false, so does not violate the assignable clause
                +"  }\n"
                +"  //@ ensures j == 1;\n"
                +"  public static void main(String[] args) {\n"
                +"    setj(0);\n"
                +"  }\n"
                +"}\n"
                ,"/tt/A.java:11: JML precondition is false"
                ,"/tt/A.java:6: Associated declaration"
                ,"/tt/A.java:3: JML precondition is false"
                ,"/tt/A.java:10: JML postcondition is false"
                ,"/tt/A.java:9: Associated declaration"
        );
    }
    
    @Ignore    // FIXME - assignable turned off for RAC, until we can decide fresh allocations
    @Test public void testAssignable3() {
        helpRacText("tt.A","package tt; public class A {\n"
                +"  static public int j=0,k;\n"
                +"  //@ requires i > 0;\n"
                +"  //@ modifies k;\n"
                +"  //@ ensures j == i;\n"
                +"  public static void setj(int i) {\n"
                +"    j = i;\n" 
                +"  }\n"
                +"  //@ ensures j == 1;\n"
                +"  public static void main(String[] args) {\n"
                +"    setj(1);\n"
                +"  }\n"
                +"}\n"
                ,"/tt/A.java:7: JML An item is assigned that is not in the assignable statement: .tt.A.j"
                ,"/tt/A.java:4: Associated declaration" // FIXME - this does not make sense
        );
    }
    
    @Test public void testLabelledStatement() {
        helpRacText("tt.A","package tt; class A { public static void main(String[] args) { new A().m(); }\n public void m() { int i=5; \n outer: while (i > 0)  { --i; } \n /*@ assert i == 0; */ \n System.out.println(\"END\"); }}"
                ,"END");
    }

    @Test public void testLabelledStatement2() {
        helpRacText("tt.A","package tt; class A { public static void main(String[] args) { new A().m(); }\n public void m() { int i=5; \n outer: while (i > 0)  { --i; } \n /*@ assert i == -1; */ }}"
                ,"/tt/A.java:4: JML assertion is false"
                );
    }

    @Test public void testInitializer() {
        helpRacText("tt.A","package tt; public class A { public static void main(String[] args) {  }\n { //@ assert false; \n } " +
                "}"
                ); // The assert is not executed
    }

    @Test public void testInitializer2() {
        helpRacText("tt.A","package tt; public class A { public static void main(String[] args) { A a = new A(); System.out.println(\"END\"); }\n {  //@ assert false; \n  \n } " +
                "}"
                ,"/tt/A.java:2: JML assertion is false"
                ,"END");
    }

    @Test public void testInitializer2a() {
        helpRacText("tt.A","package tt; public class A { public static void main(String[] args) { A a = new A(); System.out.println(\"END\"); }\n  " +
                "}"
                ,"END");
    }

    @Test public void testInitializer3() {
        helpRacText("tt.A","package tt; public class A { public static void main(String[] args) {  }\n static { //@ assert false; \n } " +
                "}"
                ,"/tt/A.java:2: JML assertion is false");
    }

    @Test
    public void testChangedParam() {
        helpRacText("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures \\result == i;\n"
                +"  public static int m1bad(int i) {\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                +"  //@ ensures \\result == i+1;\n"
                +"  public static int m1good(int i) {\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                +"  public static void main(String ... args) {\n"
                +"    m1good(2);\n"
                +"    m1bad(4);\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:4: JML postcondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"/tt/TestJava.java:13: JML postcondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                );
    }

    @Test public void testSynchronized() {
        helpRacText("tt.A","package tt; class A { public static void main(String[] args) { new A().m(); }\n public void m() { int i; \n synchronized (this) { i = 0; } \n}}"
                );
    }

    @Test public void testForEach3() {
        helpRacText("tt.A","package tt; class A { public static void main(String[] args) { java.util.List<Integer> list = new java.util.LinkedList<Integer>(); list.add(0); m(list); }"
                +"static void m(java.util.List<Integer> list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) {  sum += o; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                );
    }

    @Test public void testForEach3bad() {
        helpRacText("tt.A","package tt; class A { public static void main(String[] args) { java.util.List<Integer> list = new java.util.LinkedList<Integer>(); list.add(0); m(list);}"
                +"static void m(java.util.List<Integer> list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) {  sum += o; }  \n"
                +"//@ assert sum > 0; \n"
                +"}}"
                ,"/tt/A.java:5: JML assertion is false"
                );
    }

    @Test public void testForEach4() {
        helpRacText("tt.A","package tt; class A { public static void main(String[] args) { Integer[] aa = new Integer[]{1,2,3}; m(aa); }"
                +"static void m(Integer[] list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) { /*@ assume o >= 0; */ sum += o; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                );
    }

    @Test public void testForEach4bad() {
        helpRacText("tt.A","package tt; class A { public static void main(String[] args) { Integer[] aa = new Integer[]{0,0,0}; m(aa); }"
                +"static void m(Integer[] list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) { /*@ assume o >= 0; */ sum += o; }  \n"
                +"//@ assert sum > 0; \n"
                +"}}"
                ,"/tt/A.java:5: JML assertion is false"
                );
    }
    
    @Test
    public void testOldClause() {
        helpRacText("tt.TestJava",
                  """
                  package tt;
                  public class TestJava {
                    public static void main(String[] args) {
                      k = 5;
                      m(6);
                      k = 6;
                      m(6);
                    }
                    static public int k;
                    //@ old int kk = k; requires i > kk; assignable k;
                    //@ ensures k == i+1;
                    //@ ensures kk == 5;
                    //@ also
                    //@ old int kkk = k+1; requires i < kkk; assignable k;
                    //@ ensures k == i-1;
                    //@ ensures kkk == 7;
                    static public void m(int i) {
                      if (i>k) k = i+1; else k = i-1;
                    }
                  }
                  """
                 );
        
    }
    
    @Test
    public void testOldClause1() {
        helpRacText("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava { public static void main(String[] args) { m(6); k = 6; m(6); } \n"
                + "  static public int k = 5;\n"
                + "  //@ old int kk = k; requires i > kk; assignable k; ensures k == i+1; ensures kk == 5;\n"
                + "  //@ also\n" // Purposely duplicating the name of the old variable
                + "  //@ old int kk = k+1; requires i < kk; assignable k; ensures k == i-1; ensures kk == 7;\n"
                + "  static public void m(int i) {\n"
                + "     if (i>k) k = i+1; else k = i-1;\n"
                + "  }\n"
                + "}"
                 );
        
    }
    
    @Test
    public void testOldClause2() {
        helpRacText("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava { public static void main(String[] args) { m(6); k = 6; m(4); } \n"
                + "  static public int k = 5;\n"
                + "  //@ old int kk = k;\n"
                + "  //@ {| requires i > kk; assignable k; ensures k == i+1; ensures kk == 5;\n"
                + "  //@ also\n"
                + "  //@    requires i < kk; assignable k; ensures k == i-1; ensures kk == 6;\n"
                + "  //@ |}\n"
                + "  static public void m(int i) {\n"
                + "     if (i>k) k = i+1; else k = i-1;\n"
                + "  }\n"
                + "}"
                 );
        
    }
    
    @Test
    public void testShowStatement() {
        expectedExit = 0;
        addOptions("--code-math=bigint","--method=m");
        helpRacText("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static void main(String[] args) { m(3,-8); } \n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires true; \n"
                        + "  public static void m(int i, int j) {\n"
                        + "     //@ show i, j+1;\n"
                        + "     int k = i+j;\n"
                        + "     //@ show k;\n"
                        + "     //@ assert k > 0;\n"
                        + "     int m = i-j;\n"
                        + "     //@ show m,k;\n"
                        + "     //@ assert m > 0;\n"
                        + "  }\n"
                        + "}\n"
                        ,"LABEL JMLSHOW_1 = 3"
                        ,"LABEL JMLSHOW_2 = -7"
                        ,"LABEL JMLSHOW_3 = -5"
                        ,"/tt/TestJava.java:10: JML assertion is false"
                        ,"LABEL JMLSHOW_4 = 11"
                        ,"LABEL JMLSHOW_5 = -5"
                        );
    }
    
    @Test
    public void testIsArray() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    int i;
                    Object oo = new Object();
                    int[] x = new int[1];
                    Object o = new Object[2];
                    Object[] oa = new Object[2];

                    //@ assert  \\isarray(\\typeof(x));
                    //@ assert  \\isarray(\\type(int[]));
                    //@ assert  \\isarray(\\typeof(o));
                    //@ assert  \\isarray(\\type(Object[]));
                    //  assert !\\isarray(\\typeof(i));  // Cannot apply typeof to a value of primitive type
                    //@ assert !\\isarray(\\type(int));
                    //@ assert !\\isarray(\\typeof(oo));
                    //@ assert !\\isarray(\\type(Object));

                    //@ assert \\isarray(x.getClass());
                    //@ assert \\isarray(int[].class);
                    //@ assert \\isarray(o.getClass());
                    //@ assert \\isarray(Object[].class);
                    //  assert !\\isarray(i.getClass()); // Invalid syntax
                    //@ assert !\\isarray(int.class);
                    //@ assert !\\isarray(oo.getClass());
                    //@ assert !\\isarray(Object.class);
                    System.out.println("DONE");
                  }
                }
                """
                ,"DONE"
                );
        
    }
    
    @Test
    public void testIsArrayN() {
        expectedExit = 0;
        expectedRACExit = 1;
        helpRacText("tt.TestJava",
                """
                package tt;
                //@ nullable_by_default
                public class TestJava {
                  public static void main(String[] args) {
                    Class<?> n = null;
                    //@ assert \\isarray(n);
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: JML actual argument may not be null"
                ,"Exception in thread \"main\" java.lang.NullPointerException: Cannot invoke \"java.lang.Class.isArray()\" because \"<local4>\" is null"
                ,"\tat tt.TestJava.main(TestJava.java:6)"
                );
        
    }

    // If tests are added here, add them also in the corresponding esc tests (currently escall3.testElemTypeN)
    @Test
    public void testElemTypeN() {
        helpRacText("tt.TestJava",
                """
                package tt;
                //@ nullable_by_default
                public class TestJava {
                  public static void main(String[] args) {
                    Object o = new Object();
                    Class<?> n = null;
                    try {
                      //@ assert \\elemtype(n) ==\\type(Object);
                    } catch (Exception e) {
                      System.out.println(e);
                    }
                    try {
                      //@ assert \\elemtype(null) == \\typeof(o);
                    } catch (Exception e) {
                      System.out.println(e);
                    }
                    try {
                      Integer i = 0;
                      //@ assert \\elemtype(i) == \\typeof(o);
                    } catch (Exception e) {
                      System.out.println(e);
                    }
                    try {
                      int i = 0;
                      //@ assert \\elemtype(\\typeof(i)) == \\typeof(o);
                    } catch (Exception e) {
                      System.out.println(e);
                    }
                    try {
                      //@ assert \\elemtype(\\type(Integer)) == \\typeof(o);
                    } catch (Exception e) {
                      System.out.println(e);
                    }
                    try {
                      //@ assert \\elemtype(\\type(int)) == \\typeof(o);
                    } catch (Exception e) {
                      System.out.println(e);
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: JML actual argument may not be null"
                ,"java.lang.NullPointerException: Cannot invoke \"Object.getClass()\" because \"<local7>\" is null"
                ,"/tt/TestJava.java:13: verify: JML actual argument may not be null"
                ,"java.lang.NullPointerException: Cannot invoke \"Object.getClass()\" because \"null\" is null"
                ,"/tt/TestJava.java:19: verify: JML actual argument has an illegal value"
                ,"java.lang.IllegalArgumentException: Calling \\elemtype on a value that is not an (or does not have) array type: java.lang.Integer"
                ,"/tt/TestJava.java:25: verify: JML actual argument has an illegal value"
                ,"java.lang.IllegalArgumentException: Calling \\elemtype on a value that is not an (or does not have) array type: int"
                ,"/tt/TestJava.java:30: verify: JML actual argument has an illegal value"
                ,"java.lang.IllegalArgumentException: Calling \\elemtype on a value that is not an (or does not have) array type: java.lang.Integer"
                ,"/tt/TestJava.java:35: verify: JML actual argument has an illegal value"
                ,"java.lang.IllegalArgumentException: Calling \\elemtype on a value that is not an (or does not have) array type: int"
                );
    }

    // If tests are added here, add them also in the corresponding esc tests (currently escall3.testElemType)
    @Test
    public void testElemType() {
        helpRacText("tt.TestJava",
                """
                package tt;
                //@ nullable_by_default
                public class TestJava {
                  public static void main(String[] args) {
                    Object o = new Object();
                    Object oo = new Object[2];
                    Object[] oa = new Object[2];
                    Object[] ob = new Integer[2];
                    // \\TYPE argument
                    //@ show \\elemtype(\\typeof(oo));
                    //@ assert \\elemtype(\\typeof(oa)) == \\typeof(o);
                    // Object argument
                    //@ show \\elemtype(oa);
                    //@ show \\elemtype(oo);
                    //@ assert \\elemtype(oo) == \\typeof(o);
                    //@ show \\elemtype(ob);
                    //@ assert \\elemtype(ob) == \\type(Integer);
                    //@ assert \\elemtype(\\type(Integer[])) == \\type(Integer);
                    //@ assert \\elemtype(\\type(int[])) == \\type(int);
                  }
                }
                """
                ,"LABEL JMLSHOW_1 = java.lang.Object"
                ,"LABEL JMLSHOW_2 = java.lang.Object"
                ,"LABEL JMLSHOW_3 = java.lang.Object"
                ,"LABEL JMLSHOW_4 = java.lang.Integer"
                );
    }
    
    @Test public void testElemTypeMod() {
        expectedExit = 1;
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" 
                +"//@ ghost nullable \\TYPE tt; \n"
                +"}}"
                ,"/tt/TestJava.java:2: error: the type modifier/annotation is not permitted on a primitive type: \\TYPE",11
                );
        
    }
    
    @Test
    public void testBRC() {
        runrac = false;
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String ... args) {
                    //@ refining
                    //@   returns true;
                    //@   continues false;
                    //@   breaks true;
                    {}
                  }
                }
                """
                ,"/tt/TestJava.java:5: warning: Not implemented for runtime assertion checking: returns clause", 11
                ,"/tt/TestJava.java:6: warning: Not implemented for runtime assertion checking: continues clause", 11
                ,"/tt/TestJava.java:7: warning: Not implemented for runtime assertion checking: breaks clause", 11
                );
        
    }
    
    @Test
    public void testReturn() {
        helpRacText("RET",
                """
                public class RET {
                  public static void main(String ... args) {
                    m(null);
                  }
                  public static /*@ non_null */ Object m(/*@ nullable */ Object o) {
                    return o;
                  }
                }
                """
                ,"/RET.java:5: verify: JML null return value from method m"
                ,"/RET.java:5: verify: Associated declaration"
                ,"/RET.java:3: verify: JML null return value from method m(java.lang.@org.jmlspecs.annotation.Nullable Object), checked in caller main(java.lang.String...)"
                ,"/RET.java:5: verify: Associated declaration"
                );
    }
}
