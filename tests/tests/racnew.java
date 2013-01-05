package tests;

import org.junit.Ignore;
import org.junit.Test;

/** These tests exercise the RAC checking.  They compile a test class 
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
public class racnew extends RacBase {

    /** Sets the classpath used for these tests.  The bin in the classpath
     * brings in the currently compiled runtime classes (so we don't have
     * to build jmlruntime.jar)
     */
    String[] ordrac = new String[]{jdk, "-ea", "-classpath","bin"+z+"bin-runtime"+z+"testdata",null};

    @Override
    public void setUp() throws Exception {
        rac = ordrac;
        jdkrac = false;
        //noCollectDiagnostics = true; print = true;
        super.setUp();
        main.addUndocOption("-newesc");
        main.addUndocOption("-showrac");
        main.addOptions("-showNotImplemented");
        main.addOptions("-noPurityCheck"); // System specs have a lot of purity errors, so turn this off for now
        main.addOptions("-noInternalSpecs"); // Faster with this option; should work either way
        main.addOptions("-noRacSource");
        //main.addOptions("-verboseness=4");
        expectedNotes = 0;
    }

    /** Basic Hello World test, with no RAC tests triggered */
    @Test public void testJava() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { System.out.println(\"HELLO WORLD\"); }}"
                ,"HELLO WORLD"
                );
    }

    /** Basic Hello World test, with no RAC tests triggered */
    @Test public void testJavaExit() {
        expectedRACExit = 5;
        helpTCX("tt.TestJavaExit","package tt; public class TestJavaExit { public static void main(String[] args) { System.exit(5); }}"
                );
    }

    /** Basic Hello World test, with no RAC tests triggered */
    @Test public void testJavaNull() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) {  }}"
                );
    }

    /** Simple test of output from a JML set statement */
    @Test public void testJML() {
        helpTCX("tt.TestJML","package tt; public class TestJML { public static void main(String[] args) { //@ ghost int i = 0; \n //@ set i = 1; \n //@ set System.out.println(i); \n System.out.println(\"END\"); }}"
                ,"1"
                ,"END"
                );
    }

    /** JML assert statement failure */
    @Test public void testAssertion() {
        helpTCX("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { \n//@ assert false; \n System.out.println(\"END\"); }}"
                ,"/tt/TestAssert.java:2: JML assertion is false"
                ,"END"
                );
    }

    /** JML labeled assert statement failure */
    @Test public void testAssertion2() {
        helpTCX("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { \n//@ assert false: \"ABC\"; \n System.out.println(\"END\"); }}"
                ,"ABC"
                ,"END"
                );
    }

    // FIXME - need to put in type conversion
    @Ignore
    @Test public void testAssertion3() {
        helpTCX("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { //@ assert false: args.length; \n System.out.println(\"END\"); }}"
                ,"/tt/TestAssert.java:1: JML assertion is false"
                ,"END"
                );
    }

    /** Assumption failure */
    @Test public void testAssumption() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ assume false; \n System.out.println(\"END\"); }}"
                ,"/tt/TestJava.java:1: JML assumption is false"
                ,"END"
                );
    }

    /** Labeled assumption failure */
    @Test public void testAssumption2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ assume false: \"DEF\"; \n System.out.println(\"END\"); }}"
                ,"DEF"
                ,"END"
                );
    }

    /** Failed unreachable statement */
    @Test public void testUnreachable() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ unreachable; \n System.out.println(\"END\"); }}"
                ,"/tt/TestJava.java:1: JML unreachable statement reached"
                ,"END"
                );
    }

    /** Successful precondition */
    @Test public void testPrecondition() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(0); System.out.println(\"END\"); }\n" +
                " /*@ requires i == 0; */ static void m(int i) {} " +
                "}"
                ,"END"
                );
    }
    
    /** Failed precondition */
    @Test public void testPrecondition2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(0); System.out.println(\"END\"); }\n" +
                " /*@ requires i != 0; */ \n" +
                " static void m(int i) {} " +
                "}"
                ,"/tt/TestJava.java:1: JML precondition is false"
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"END"
                );
    }
    
    /** Failed precondition */
    @Test public void testPrecondition3() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(1); \n" +
                " m(-1); \n" +
                " m(0); \n" +
                " System.out.println(\"END\"); }\n" +
                " /*@ requires i > 0; */ \n" +
                " /*@ requires i < 0; */ \n" +
                " static void m(int i) {} " +
                "}"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:6: Associated declaration"
                ,"/tt/TestJava.java:6: JML precondition is false"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"/tt/TestJava.java:6: Associated declaration"
                ,"/tt/TestJava.java:6: JML precondition is false"
                ,"/tt/TestJava.java:4: JML precondition is false"
                ,"/tt/TestJava.java:6: Associated declaration"
                ,"/tt/TestJava.java:6: JML precondition is false"
                ,"END"
                );
    }
    
    /** Failed precondition with nowarn */
    @Test public void testPrecondition2NoWarn() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); //@ nowarn Precondition;\n" +
                "System.out.println(\"END\"); }\n" +
                " /*@ requires i != 0; */ //@ nowarn Precondition;\n" +
                " static void m(int i) {} \n" +
                "}"
                ,"END"
                );
    }
    
    @Test public void testNonnullPrecondition() {
        main.addOptions("-noRacSource=false");
        helpTCX("tt.TestJava","package tt; public class TestJava { \n" + 
                "public static void main(String[] args) { \n" +
                " m(null,1); \n" +
                " System.out.println(\"END\"); }\n" +
                " /*@ requires true; */ \n" +
                " static void m(/*@non_null*/ Object o, int i) {\n" +
                " }\n" +
                "}"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ," m(null,1); "
                ,"  ^"
                ,"/tt/TestJava.java:6: Associated declaration"
                ," static void m(/*@non_null*/ Object o, int i) {"
                ,"                  ^"
                ,"/tt/TestJava.java:5: JML precondition is false"
                ," /*@ requires true; */ "
                ,"     ^"
                ,"END"
                );
    }
    
    @Test public void testNonnullPrecondition2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(null,1); System.out.println(\"END\"); }\n" +
                " static void m(/*@non_null*/ Object o, int i) {} " +
                "}"
                ,"/tt/TestJava.java:1: JML precondition is false"
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"END"
                );
    }
    
    @Test public void testNonnullPostcondition() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null,1); \n" +
                "System.out.println(\"END\"); }\n" +
                " static /*@non_null*/Object m( /*@nullable*/Object o, int i)\n" +
                "{ return null; } " +
                "}"
                ,"/tt/TestJava.java:4: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"END"
                );
    }
    
    // TODO need multiple requires, multiple spec cases

    @Test public void testPostcondition() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures k == i; */ static int m(int i) { k = i; return 13; } " +
                "}"
                ,"END"
                );
    }

    @Test public void testPostcondition1() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(1); System.out.println(\"END\"); } \n" +
                " static int k = 0; \n" +
                " /*@ ensures k == 0; */ \n" +
                " static int m(int i) { k = i; return 13; } " +
                "}"
                ,"/tt/TestJava.java:5: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"END"
                );
    }

    @Test public void testPostcondition1Nowarn() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(1); System.out.println(\"END\"); } /*@ nowarn Postcondition;*/\n" +
                " static int k = 0; \n" +
                " /*@ ensures k == 0; */ \n"+
                " static int m(int i) { k = i; return 13; }/*@ nowarn Postcondition;*/ " +
                "}"
                ,"END"
                );
    }

    @Test public void testPostcondition2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ requires true; \nalso \nrequires false; \nensures k == 0; */ static void m(int i) { k = i; } " +
                "}"
                ,"END"
                );
    }

    @Test public void testPostcondition3() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ requires true; \nensures true; \nalso \nrequires false; \nensures k == 0; */ static void m(int i) { k = i; } " +
                "}"
                ,"END"
                );
    }

    @Test public void testPostcondition4() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(1); System.out.println(\"END\"); } \n" +
                " static int k = 0; \n" +
                " /*@ requires true; \n" +
                "     ensures k != i; \n" +
                "     also \n" +
                "     requires true; \n" +
                "     ensures k == 0; */ \n" +
                " static void m(int i) { k = i; } " +
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
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String[] args) { \n"
                +"    org.jmlspecs.utils.Utils.useExceptions = true; \n"
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
                ,"Exception in thread \"main\" org.jmlspecs.utils.Utils$JmlAssertionError: /tt/TestJava.java:14: JML postcondition is false"
                ,"/tt/TestJava.java:10: Associated declaration"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailure(Utils.java:24)"
                ,"\tat tt.TestJava.m(TestJava.java:14)"
                ,"\tat tt.TestJava.main(TestJava.java:5)"
                );
    }
    
    @Test public void testSignals() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \n"
                +"     signals (java.io.FileNotFoundException e) e == null; */\n"
                +"static void m(int i) throws java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML signals condition is false"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"END"
                );
    }

    @Test public void testSignals2() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \nsignals (java.io.FileNotFoundException e) e == null; */\n"
                +"static void m(int i) throws Exception, java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML signals condition is false"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"END"
                );
    }
    
    @Test public void testSignalsOnly() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \nsignals_only \\nothing; */\n"
                +"static void m(int i) throws Exception, java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML unexpected exception for the signals_only clause"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"END"
                );
    }

    @Test public void testSignalsOnly1() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
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
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \nsignals_only java.io.FileNotFoundException; */\n"
                +"static void m(int i) throws Exception, java.io.FileNotFoundException { throw new Exception(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML unexpected exception for the signals_only clause"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"END"
                );
    }

    @Test public void testSignalsOnlyDefault() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \n*/\n"
                +"static void m(int i) throws java.io.FileNotFoundException { throw new RuntimeException(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML unexpected exception for the signals_only clause"
                ,"/tt/TestJava.java:8: Associated declaration"
                ,"END"
                );
    }

    @Test public void testSignalsOnlyDefault1() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
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
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" \n"
                +"static void m(int i) throws java.io.FileNotFoundException { throw new RuntimeException(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML unexpected exception" // FIXME - what about this case?
                ,"END"
                );
    }

    @Test public void testResult() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) {  m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures \\result == 4; */ static int m(int i) { return 4; } " +
                "}"
                ,"END"
        );
    }

    @Test public void testResult1() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +" m(1); \n"
                +" System.out.println(\"END\"); } \n"
                +" static int k = 0; \n" 
                +" /*@ ensures \\result == 4; */ \n"
                +" static int m(int i) { \n"
                +" return 5; } "
                +"}"
                ,"/tt/TestJava.java:6: JML postcondition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"END"
        );
    }
    
    @Test public void testOld() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures (\\lbl ENS \\old(k)) == k; */ static int m(int i) { k=i; return i; } " +
                "}"
                ,"LABEL ENS = 0"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"LABEL ENS = 0"
                ,"/tt/TestJava.java:1: JML postcondition is false"
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"LABEL ENS = 1"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"END"
        );        
    }
    
    @Test public void testOld2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
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
    
    @Test public void testOld3() {
        //print = true; main.addUndocOption("-showrac");
        helpTCX("tt.TestJava","package tt; public class TestJava { \n"
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
                ,"LABEL AST = 0"
                ,"LABEL AST2 = 0"
                ,"LABEL AST3 = 10"
                ,"LABEL AST4 = 1"
                ,"LABEL AST = 10"
                ,"LABEL AST2 = 10"
                ,"LABEL AST3 = 9"
                ,"LABEL AST4 = 0"
                ,"END"
        );        
    }
    
    @Test public void testInformal() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " static int m(int i) { System.out.println(i); //@ assert (i==0) <==> (* informal *); \n return i; } " +
                "}"
                ,"1"
                ,"/tt/TestJava.java:2: JML assertion is false"
                ,"0"
                ,"END"
                );
    }

    @Test public void testElemtype() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" 
                +"Object o = new String[3]; Object oo = new int[5]; Object o3 = new Integer(4);\n"
                +"//@ ghost nullable java.lang.Class t; ghost nullable \\TYPE tt; \n"
                +"//@ set tt = (\\lbl A \\elemtype(\\typeof(o)));\n"
                +"//@ set tt = (\\lbl B \\elemtype(\\typeof(oo)));\n"
                +"//@ set tt = (\\lbl C \\elemtype(\\typeof(o3)));\n"
                +"//@ set t = (\\lbl D \\elemtype(java.lang.Class.class));\n"
                +"//@ set t = (\\lbl E \\elemtype(java.lang.Boolean[].class));\n"
                +"System.out.println(\"END\"); } \n"
                +"}"
                ,"LABEL A = class java.lang.String"
                ,"LABEL B = int"
                ,"LABEL C = null"
                ,"LABEL D = null"
                ,"LABEL E = class java.lang.Boolean"
                ,"END"
                );
        
    }
    

    @Test public void testTypeOf() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(new Object()); m(new String()); m(Boolean.TRUE); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i).erasure()) == Object.class; \n" +
                " static void m(/*@nullable*/Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"LABEL CLS = class java.lang.Object"
                ,"LABEL CLS = class java.lang.Object"
                ,"CLASS class java.lang.Object"
                ,"LABEL CLS = class java.lang.String"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"LABEL CLS = class java.lang.String"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.lang.String"
                ,"LABEL CLS = class java.lang.Boolean"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"LABEL CLS = class java.lang.Boolean"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.lang.Boolean"
                ,"END"
                );
        
    }
    
    @Test public void testTypeOf1() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(new Object[1]); m(new String[2]); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i)) == \\type(Object); \n" +
                " static void m(/*@nullable*/Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"LABEL CLS = class [Ljava.lang.Object;"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"LABEL CLS = class [Ljava.lang.Object;"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class [Ljava.lang.Object;"
                ,"LABEL CLS = class [Ljava.lang.String;"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"LABEL CLS = class [Ljava.lang.String;"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class [Ljava.lang.String;"
                ,"END"
                );
        
    }
    
    @Test public void testTypeOf2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i)) == \\type(Object); \n" +
                " static void m(int i) { \n" +
                "//@ assert (\\lbl AST \\typeof(true)) != null; \n" +
                "//@ assert (\\lbl AST2 \\typeof((short)0)) != null; \n" +
                "//@ assert (\\lbl AST3 \\typeof((long)0)) != null; \n" +
                "//@ assert (\\lbl AST4 \\typeof((byte)0)) != null; \n" +
                "//@ assert (\\lbl AST5 \\typeof('c')) != null; \n" +
                "//@ assert (\\lbl AST6 \\typeof(\"c\")) != null; \n" +
                "//@ assert (\\lbl AST7 \\typeof((float)0)) != null; \n" +
                "//@ assert (\\lbl AST8 \\typeof((double)0)) != null; \n" +
                "} " +
                "}"
                ,"LABEL CLS = int"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"LABEL CLS = int"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"LABEL AST = boolean"
                ,"LABEL AST2 = short"
                ,"LABEL AST3 = long"
                ,"LABEL AST4 = byte"
                ,"LABEL AST5 = char"
                ,"LABEL AST6 = class java.lang.String"
                ,"LABEL AST7 = float"
                ,"LABEL AST8 = double"
                ,"END"
                );
        
    }
    
    @Test public void testTypeOf3() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "//@ assert (\\lbl AST9 \\typeof(5/0)) != null; \n" +
                "//@ assert (\\lbl AST10 \\typeof(5.0/0.0)) != null; \n" +
                "} " +
                "}"
                ,"LABEL AST9 = int"
                ,"LABEL AST10 = double"
                ,"END"
                );
        
    }

    // FIXME - want typeof to return a JML type with type parameter information
    @Test public void testTypeOf4() {
        helpTCX("tt.TestJava","package tt; import java.util.*; public class TestJava { public static void main(String[] args) { \n" +
                "m(new LinkedList<String>()); m(new LinkedList<Integer>());  m(new HashSet<Integer>()); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i)) .equals ( \\type(LinkedList<Integer>) ); \n" +
                " static void m(/*@nullable*/Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"LABEL CLS = class java.util.LinkedList"
//                ,"/tt/TestJava.java:2: JML precondition is false"
//                ,"/tt/TestJava.java:3: Associated declaration"
                ,"LABEL CLS = class java.util.LinkedList"
//                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.util.LinkedList"
                ,"LABEL CLS = class java.util.LinkedList"
                ,"LABEL CLS = class java.util.LinkedList"
                ,"CLASS class java.util.LinkedList"
                ,"LABEL CLS = class java.util.HashSet"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"LABEL CLS = class java.util.HashSet"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.util.HashSet"
                ,"END"
                );
        
    }
    
    // FIXME - want typeof to return a JML type with type parameter information
    @Test public void testTypeOf5() {
        helpTCX("tt.TestJava","package tt; import java.util.*; public class TestJava { public static void main(String[] args) { \n" +
                "m(new LinkedList<String>()); m(new LinkedList<Integer>());  m(new HashSet<Integer>()); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i)) == ( \\type(LinkedList<Integer>) ); \n" +
                " static void m(/*@nullable*/Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"LABEL CLS = class java.util.LinkedList"
//                ,"/tt/TestJava.java:2: JML precondition is false"
//                ,"/tt/TestJava.java:3: Associated declaration"
                ,"LABEL CLS = class java.util.LinkedList"
//                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.util.LinkedList"
                ,"LABEL CLS = class java.util.LinkedList"
                ,"LABEL CLS = class java.util.LinkedList"
                ,"CLASS class java.util.LinkedList"
                ,"LABEL CLS = class java.util.HashSet"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"LABEL CLS = class java.util.HashSet"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.util.HashSet"
                ,"END"
                );
        
    }
    
    // FIXME - want typeof to return a JML type with type parameter information
    @Test public void testTypeOf6() {
        helpTCX("tt.TestJava","package tt; import java.util.*; public class TestJava { public static void main(String[] args) { \n" +
                "m(new LinkedList<String>());  m(new HashSet<Integer>()); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i)) != ( \\type(LinkedList<Integer>) ); \n" +
                " static void m(/*@nullable*/Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"LABEL CLS = class java.util.LinkedList"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"LABEL CLS = class java.util.LinkedList"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.util.LinkedList"
                ,"LABEL CLS = class java.util.HashSet"
                ,"LABEL CLS = class java.util.HashSet"
                ,"CLASS class java.util.HashSet"
                ,"END"
                );
        
    }
    

    @Test public void testNonnullelement() {
        helpTCX("tt.TestJava","package tt; public class TestJava { static int z = 0; public static void main(String[] args) { \n" +
                "String[] s2null = new String[]{null,\"B\"}; \n" +
                "String[] s2 = new String[]{\"A\",\"B\"}; \n" +
                "m(new Object[]{}); \n" +
                "m(new String[]{\"A\"}); \n" +
                "m(s2); \n" +
                "m(s2null); \n" +
                "//@ assert \\nonnullelements(s2,s2null); \n" +
                "//@ assert \\nonnullelements(s2,s2); \n" +
                        // Tests shortcut evaluation
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
                ,"/tt/TestJava.java:10: JML assertion is false"
                ,"END"
                );
        
    }
    
    @Test public void testNonnullelement2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null); \n" +
                "System.out.println(\"END\"); } \n" +
                " static void m(/*@nullable*/Object[] o) { \n" +
                "//@ assert (\\lbl ELEM \\nonnullelements((\\lbl O o))); \n" +
                "} " +
                "}"
                ,"LABEL O = null"
                ,"LABEL ELEM = false"
                ,"/tt/TestJava.java:5: JML assertion is false"
                ,"END"
                );
        
    }
    
    @Test 
    public void testTypelc() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
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
                "//@ set c = \\type(Class<?>); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "} " +
                "}"
                ,"LABEL TYP1 = int"
                ,"LABEL TYP2 = boolean"
                ,"LABEL TYP1 = class java.lang.Object"
                ,"LABEL TYP2 = class java.lang.Object"
                ,"LABEL TYP3 = class java.lang.String"
                ,"LABEL TYP4 = class java.lang.String"
                ,"LABEL TYP1 = class [Ljava.lang.String;"
                ,"LABEL TYP2 = class [Ljava.lang.String;"
                ,"LABEL TYP3 = class [[Ljava.lang.String;"
                ,"LABEL TYP4 = class [[Ljava.lang.String;"
                ,"LABEL TYP1 = class java.lang.Class<class java.lang.Integer>"
                ,"LABEL TYP2 = class java.lang.Class<?>"
                ,"END"
                );
        
    }
    
    @Test
    public void testSubtype() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(); mm(); \n" +
                "System.out.println(\"END\"); } \n" +
                "static Object o = new Object(); \n" +
                "static Object oo = new String(); \n" +
                "static Object ob = Boolean.FALSE; \n" +
                "static String s = new String(); \n" +
                "static Boolean b = Boolean.TRUE; \n" +
                " static void m() { \n" +
                "//@ ghost boolean c; \n" +
                "//@ set c = o.getClass() <: o.getClass(); \n" + // Object <: Object  // Class
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\typeof(o) <: \\typeof(o); \n" +  // Object <: Object // \TYPE
                "//@ set c = (\\lbl TYP2 c); \n" +
                "//@ set c = \\typeof(o) <: \\typeof(oo); \n" + // Object <: String // \TYPE
                "//@ set c = (\\lbl TYP3 c); \n" +
                "//@ set c = \\typeof(oo) <: \\typeof(o); \n" + // String <: Object // \TYPE
                "//@ set c = (\\lbl TYP4 c); \n" +
                "//@ set c = \\typeof(ob) <: \\typeof(oo); \n" + // Boolean <: String // \TYPE
                "//@ set c = (\\lbl TYP5 c); \n" +
                "}\n" +
                " static void mm() { \n" +
                "//@ ghost boolean c; \n" +
                "//@ set c = s.getClass() <: b.getClass(); \n" + // String <: Boolean // Class
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\typeof(s) <: \\typeof(b); \n" +  // String <: Boolean // \TYPE
                "//@ set c = (\\lbl TYP2 c); \n" +
                "//@ set c = \\type(int) <: \\typeof(o); \n" + // int <: Object // \TYPE
                "//@ set c = (\\lbl TYP3 c); \n" +
                "//@ set c = \\type(int) <: \\type(int); \n" + // int <: int  // false
                "//@ set c = (\\lbl TYP4 c); \n" +
                "//@ set c = \\type(int) <: \\type(boolean); \n" + // int <: boolean
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
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); m(1); m(2); System.out.println(\"END\"); } \n" +
                " //@ requires 10/i != 0; \n" +
                " //@ ensures 10/(i-1) == 0; \n" +
                " static void m(int i) { \n" +
                "   System.out.println(\"VALUE \" + i); \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:3: JML Division by zero"
                ,"JML undefined precondition - exception thrown" // FIXME - this should have a line number
                ,"java.lang.ArithmeticException: / by zero"
                ,"\tat tt.TestJava.main(TestJava.java:3)"
                ,"/tt/TestJava.java:3: JML Division by zero"
                ,"Runtime exception while evaluating preconditions - preconditions are undefined in JML"
                ,"java.lang.ArithmeticException: / by zero"
                ,"\tat tt.TestJava.m(TestJava.java:3)"
                ,"\tat tt.TestJava.main(TestJava.java:2)"
                ,"VALUE 0"
                ,"JML undefined precondition while checking postconditions - exception thrown"
                ,"java.lang.ArithmeticException: / by zero"
                ,"\tat tt.TestJava.main(TestJava.java:3)"
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
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); m(1); System.out.println(\"END\"); } \n" +
                " //@ requires i != 0; \n" +
                " //@ requires 10/i == 10; \n" +
                " static void m(int i) { \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"END"
                );
        
    }
    
    @Test public void testSpecFile() {
        addMockFile("$A/tt/A.jml","package tt; public class A { //@ ghost static int i = 0;\n  //@ invariant i == 0; \n //@ requires i == 1;\n static int m(); }");
        helpTCX("tt.A","package tt; public class A { static int m() { return 0; }  \n public static void main(String[] args) { m(); System.out.println(\"END\"); }}"
                ,"/tt/A.java:2: JML precondition is false"
                ,"/$A/tt/A.jml:3: Associated declaration"
                ,"/tt/A.java:2: JML precondition is false"
                ,"END"
                );
        
    }

    @Test public void testSpecFile2() {
        addMockFile("$A/tt/A.jml","package tt; public class A { //@ ghost static int i = 0;\n  //@ invariant i == 0; \n //@ ensures i == 1;\n static int m(); }");
        helpTCX("tt.A","package tt; public class A { static int m() { //@ set i = 1; \n return 0; }  \n public static void main(String[] args) { m(); System.out.println(\"END\"); }}"
                ,"END"
                );
        
    }

    @Test public void testSpecModelMethod() {
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"/*@ model static pure int mm() { return 5; } */ \n"
                +"//@ ghost static int i = 0;\n  "
                +"//@ invariant i == 0; \n //@ ensures i == 1;\n static int m(); "
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { static int m() { \n"
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

    @Test @Ignore
    public void testSpecModelClass() { // FIXME - nested class problems?
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"/*@ model static class AA { static int mm() { return 5; }} */ \n"
                +"//@ ghost static int i = 0;\n  "
                +"//@ invariant i == 0; \n "
                +"//@ ensures i == 0;\n "
                +"static int m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int m() { \n"
                +"  //@ set i = AA.mm(); \n"
                +"  return 0; \n"
                +"}  \n "
                +"public static void main(String[] args) { \n"
                +"  m(); \n"
                +"  System.out.println(\"END\"); \n"
                +"}}"
                ,"/$A/tt/A.jml:5: JML postcondition is false"
                ,"END"
                );
        
    }
    
    @Test public void testStaticInvariant() {
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ static invariant i == 0; \n "
                +"static void m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int i = 0;  \n "
                +"static void m() { i = 1-i; }  \n "
                +"public static void main(String[] args) { \n"
                +"m(); "
                +"System.out.println(\"MID\"); "
                +"m(); "
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:3: JML invariant is false on leaving method"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"MID"
                ,"/tt/A.java:3: JML invariant is false on entering method"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"END"
                );
    }

    @Test public void testStaticInvariant2() { 
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ static invariant i == 0; \n "
                +"void m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int i = 0;  \n "
                +"void m() { i = 1-i; }  \n "
                +"public static void main(String[] args) { \n"
                +"new A().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"new A().m(); i = 5; \n"
                +"System.out.println(\"MID\"); \n"
                +"new A().m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:3: JML invariant is false on leaving method"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"MID"
                ,"/tt/A.java:3: JML invariant is false on entering method"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"MID"
                ,"/tt/A.java:3: JML invariant is false on entering method"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on leaving method"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"END"
                ,"/tt/A.java:4: JML invariant is false on leaving method"
                ,"/$A/tt/A.jml:2: Associated declaration"
                );
    }

    @Test public void testInvariant() { 
        main.addOptions("-noRacSource=false");
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ invariant i == 0; \n "
                +"void m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"int i = 0;  \n "
                +"void m() { i = 1-i; }  \n "
                +"public static void main(String[] args) { \n"
                +"new A().m(); "
                +"System.out.println(\"MID\"); "
                +"new A().m(); "
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:3: JML invariant is false on leaving method"
                ," void m() { i = 1-i; }  "
                ,"      ^"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"//@ invariant i == 0; "
                ,"    ^"
                ,"MID"
                ,"/tt/A.java:3: JML invariant is false on leaving method"
                ," void m() { i = 1-i; }  "
                ,"      ^"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"//@ invariant i == 0; "
                ,"    ^"
                ,"END"
                );
    }

    @Test public void testInitially() {
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ initially i == 1; \n "
                +"//@ initially j == 1; \n "
                +"void m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"int i = 0;  \n "
                +"static int j = 0;  \n "
                +"A() { i++; j++; }  \n "
                +"void m() { i++; j++; }  \n "
                +"public static void main(String[] args) { \n"
                +"new A().m(); "
                +"System.out.println(\"MID\"); "
                +"new A().m(); "
                +"System.out.println(\"END\"); "
                +"}}"
                ,"MID"
                ,"/$A/tt/A.jml:3: JML initially is false"
                ,"END"
                );
    }


    @Test public void testConstraint() {
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ constraint i == \\old(i)+1; \n "
                +"void m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"int i = 1;  \n "
                +"void m() { i *= 2; }  \n "
                +"public static void main(String[] args) { \n"
                +"A a = new A();"
                +"System.out.println(\"START\"); "
                +"a.m(); "
                +"System.out.println(\"MID\"); "
                +"a.m(); "
                +"System.out.println(\"END\"); "
                +"}}"
                ,"START"
                ,"MID"
                ,"/tt/A.java:3: JML constraint clause is false on leaving method"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"END"
                );
    }

    @Test public void testHelper() {
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ invariant i == 0; \n "
                +"/*@ helper */ void m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"int i = 0;  \n "
                +"void m() { i = 1-i; }  \n "
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
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int j = 5; \n"
                +"//@ static model int i; \n"
                +"//@ static represents i \\such_that i == j+1; \n"
                +"public static void main(String[] args) { \n"
                +"System.out.println(\"END\"); "
                +"}"
                +"}"
                ,"/tt/A.java:4: Note: Not implemented for runtime assertion checking: relational represents clauses (\\such_that)",12
                ,"/tt/A.java:3: warning: JML model field is not implemented: i",22
                ,"END"
                );

    }
    
    @Test public void testModelField() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int j = 5; \n "
                +"//@ static model int i; \n "
                +"//@ static represents i = j+1; \n "
                +"public static void main(String[] args) { \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
                +" j = 10; \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
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
        main.addOptions("-keys=DEBUG");
        expectedNotes = 0;
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int j = 5; \n "
                +"//@ static model int i; \n "
                +"//@ static represents i \\such_that i==j+1; \n "
                +"//@ static represents i =j+1; \n "
                +"public static void main(String[] args) { \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
                +" j = 10; \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
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
        main.addOptions("-keys=DEBUG");
        continueAnyway = true;
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int j = 5; \n "
                +"//@ static model int i; \n "
                +"//@ static represents i = j+1; \n "
                +"//@ static represents i = j; \n "
                +"public static void main(String[] args) { \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
                +" j = 10; \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
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
        continueAnyway = true;
        print = true;
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.PA","package tt; public class PA extends PB { \n"
                +" int j = 5; \n "
                +"//@  represents i = j+1; \n "
                +"public static void main(String[] args) { \n"
                +"PA a = new PA();\n"
                +"PB b = new PB();\n"
                +"//@ debug System.out.println(\"A \" + a.i); \n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"b = new PA();\n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); "
                +"}} class PB { //@ model  int i; \n}"
                ,"/tt/PA.java:11: warning: JML model field is not implemented: i",57
                ,"A 6"
                ,"B 0"
                ,"B 6"
                ,"END"
                );

    }

    /** Using a model field in a field access */
    @Test public void testModelField1a() {
        continueAnyway = true;
        print = true;
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.PA","package tt; public class PA { \n"
                +" static int j = 5; \n "
                +"//@  model int i; represents i = j; \n"
                +"public static void main(String[] args) { \n"
                +"PA a = new PA();\n"
                +"//@ debug System.out.println(\"A \" + a.i); \n"
                +"PB b = new PB();\n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); "
                +"}} class PB { //@ model  int i; represents i = PA.j+1; \n\n}"
                ,"A 5"
                ,"B 6"
                ,"END"
                );

    }

    /** Represents with super model field */
    @Test public void testModelField3a() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.PA","package tt; public class PA extends PB { \n"
                +" int j = 5; \n "
                +"//@  represents super.i = j+1; \n "
                +"public static void main(String[] args) { \n"
                +"PA a = new PA();\n"
                +"PB b = new PB();\n"
                +"//@ debug System.out.println(\"A \" + a.i); \n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"b = new PA();\n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); \n"
                +"}} class PB { //@ model protected int i; }\n"
                ,"/tt/PA.java:12: warning: JML model field is not implemented: i",39
                ,"A 6"
                ,"B 0"
                ,"B 6"
                ,"END"
                );

    }


    /** Represents with super model field */
    @Test public void testModelField4() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.QA","package tt; public class QA extends QB { \n"
                +" int j = 5; \n "
                +"public static void main(String[] args) { \n"
                +"QA a = new QA();\n"
                +"QB b = new QB();\n"
                +"//@ debug System.out.println(\"A \" + a.i); \n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"b = new QA();\n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); \n"
                +"}} class QB { //@ model  int i; \n}"
                ,"/tt/QA.java:11: warning: JML model field is not implemented: i",30
                ,"A 0"
                ,"B 0"
                ,"B 0"
                ,"END"
                );

    }

    /** Model field with no represents */
    @Test public void testModelField2() {
        main.addOptions("-keys=DEBUG");
        expectedExit = 0;
        continueAnyway = true;
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int j = 5; \n"
                +"//@ static model int i; \n"
                +"public static void main(String[] args) { \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:3: warning: JML model field is not implemented: i",22
                ,"A 0"
                ,"END"
        );
    }
    
    /** Forall, exists quantifier */
    @Test public void testForallQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost boolean n = (\\forall int i; 0<=i && i<=5; i >= 2); \n "
                +"//@ ghost boolean nn = (\\exists int i; 0<=i && i<=5; i >= 2); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A false true"
                ,"END"
        );
    }
    
    /** Forall, exists quantifier */
    @Test public void testForallQuantifier2() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost boolean n = (\\forall int i; 0<=i && i<=5; i >= 0); \n "
                +"//@ ghost boolean nn = (\\exists int i; 0<=i && i<=5; i >= 6); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A true false"
                ,"END"
        );
    }
    
    /** Forall, exists quantifier */
    @Test public void testForallQuantifier3() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost boolean n = (\\forall int i; ; i >= 0); \n "
                +"//@ ghost boolean nn = (\\exists int i; i == 4; i >= 6); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:3: Note: Runtime assertion checking is not implemented for this type or number of declarations in a quantified expression",25
                ,"/tt/A.java:4: Note: Runtime assertion checking is not implemented for this type or number of declarations in a quantified expression",26
                ,"A false false"
                ,"END"
        );
    }
    
    @Test public void testForallQuantifier4() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost boolean n = (\\forall int i; 0<i && i<=5; (\\exists int j; 0<=j && j < 5; j<i)); \n "
                +"//@ ghost boolean nn = (\\forall int i; 0<=i && i<=5; (\\exists int j; 0<=j && j < 5; j<i)); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A true false"
                ,"END"
        );
    }
    
    /** Numof quantifier */
    @Test public void testCountQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n1 = (\\num_of int i; 0 <= i && i <= 5; true); \n "
                +"//@ ghost long n2 = (\\num_of int i; 0 < i && i < 5; true); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 6 4"
                ,"END"
        );
    }
    
    /** Numof quantifier */
    @Test public void testCountQuantifier3() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n = (\\num_of int i; 0 <= i && i < 5; i >= 2); \n "
                +"//@ ghost long nn = (\\num_of int i; 0 <= i && i < 5; false); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 3 0"
                ,"END"
        );
    }
    
    /** Numof quantifier */
    @Test public void testCountQuantifierExt() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static int m = 2;\n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int nnn = new org.jmlspecs.utils.Utils.ValueInt() { public int value(final Object[] args) { int count = 0; int lo = (Integer)(args[0]); int hi = (Integer)(args[1]); int i = lo; while (i <= hi) { if (i>=lo && i<=hi) count++; i++; } return count; }}.value(new Object[]{0,5});\n"
                +"//@ ghost int n = (\\num_of int i; 0 <= i && i < 5; i >= m); \n "
                +"//@ ghost int nn = (\\num_of int i; 0 <= i && i < 5; m > 0); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn ); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 3 5"
                ,"END"
        );
    }
    
    /** Numof quantifier */
    @Test public void testCountQuantifierExtE() {
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static int m = 2;\n"
                +"//@ ensures (\\num_of int i; 0 <= i && i < 5; i >= m) == 3;\n"
                +"//@ ensures (\\num_of int i; 0 <= i && i < 5; i >= m) == 4;\n"
                +"public static void main(String[] argv) { \n "
                +"System.out.println(\"END\"); "
                +"}}"
                ,"END"
                ,"/tt/A.java:5: JML postcondition is false"
                ,"/tt/A.java:4: Associated declaration"
        );
    }
    
    // FIXME - quantifiers witrh multiple declarations
    /** Numof quantifier */
    @Test public void testCountTwo() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n1 = (\\num_of int i,j; 0 <= i && i <= 5 && 0 <= j && j < i; true); \n "
                +"//@ debug System.out.println(\"A \" + n1); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:3: Note: Runtime assertion checking is not implemented for this type or number of declarations in a quantified expression",23
                ,"A 0"
                ,"END"
        );
    }
    
    /** Sum quantifier */
    @Test public void testSumQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\sum int i; 0<i && i<=5; i+1); \n "
                +"//@ ghost int nn = (\\sum int i; 0<i && i<0; i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 20 0"
                ,"END"
        );
    }
    
    /** Sum quantifier */
    @Test public void testProdQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\product int i; 0<i && i<=5; i+1); \n "
                +"//@ ghost int nn = (\\product int i; 0<i && i<0; i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 720 1"
                ,"END"
        );
    }
    
    /** Max quantifier */
    @Test public void testMaxQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\max int i; 0<=i && i<=5 && (i%2)==0; i+1); \n "
                +"//@ ghost int nn = (\\max int i; 0<i && i<0; i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 0"
                ,"END"
        );
    }
    
    /** Max quantifier, with function call */
    @Test public void testMaxQuantifier2() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"  public static int inc(int i) { return i + 10; }\n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\max int i; 0<=i && i<=5 && (i%2)==0; inc(i)); \n "
                +"//@ ghost int nn = (\\max int i; -9<=i && i<=5 ; Math.abs(i)); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 14 9"
                ,"END"
        );
    }
    
    /**  quantifier over short */
    @Test public void testShortQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost short n1 = (\\max int i; 0<=i && i<=5; (short)(i+10)); \n "
                +"//@ ghost short n2 = (\\min int i; 0<=i && i<=5; (short)(i+10)); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15 10"
                ,"END"
        );
    }
    
    /**  quantifier over short */
    @Test public void testShortQuantifierB() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost short n1 = (\\max short i; 2<=i && i<=5; i); \n "
                +"//@ ghost short n2 = (\\min short i; 2<=i && i<=5; i); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 2"
                ,"END"
        );
    }
    
    /**  quantifier over byte */
    @Test public void testByteQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost byte n1 = (\\max int i; 2<=i && i<=5; (byte)i); \n "
                +"//@ ghost byte n2 = (\\min int i; 2<=i && i<=5; (byte)i); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 2"
                ,"END"
        );
    }
    
    /**  quantifier over byte */
    @Test public void testByteQuantifierB() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost byte n1 = (\\max byte i; 2<=i && i<=5; i); \n "
                +"//@ ghost byte n2 = (\\min byte i; 2<=i && i<=5; i); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 2"
                ,"END"
        );
    }
    
    /**  quantifier over long */
    @Test public void testLongQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n1 = (\\max int i; 0<=i && i<=5; (i+10L)); \n "
                +"//@ ghost long n2 = (\\min int i; 0<=i && i<=5; (i+10L)); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15 10"
                ,"END"
        );
    }
    
    /**  quantifier over long */
    @Test public void testLongQuantifierB() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n1 = (\\max long i; 0<=i && i<=5; (i+10L)); \n "
                +"//@ ghost long n2 = (\\min long i; 0<=i && i<=5; (i+10L)); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15 10"
                ,"END"
        );
    }
    
    /**  quantifier over double */
    @Test public void testDoubleQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost double n1 = (\\max int i; 0<=i && i<=5; (double)(i+10.5)); \n "
                +"//@ ghost double n2 = (\\min int i; 0<=i && i<=5; (double)(i+10.5)); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15.5 10.5"
                ,"END"
        );
    }
    
    /**  quantifier over float */
    @Test public void testFloatQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost float n1 = (\\max int i; 0<=i && i<=5; (float)(i+10.5)); \n "
                +"//@ ghost float n2 = (\\min int i; 0<=i && i<=5; (float)(i+10.5)); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15.5 10.5"
                ,"END"
        );
    }
    
    /**  quantifier over char */
    @Test public void testCharQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost char n1 = (\\max int i; 'a'<i && i<='q'; (char)i); \n "
                +"//@ ghost char n2 = (\\min int i; 'a'<i && i<='q'; (char)i); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A q b"
                ,"END"
        );
    }
    
    /**  quantifier over char */
    @Test public void testCharQuantifierB() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost char n1 = (\\max char i; 'a'<i && i<='q'; i); \n "
                +"//@ ghost char n2 = (\\min char i; 'a'<i && i<='q'; i); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A q b"
                ,"END"
        );
    }
    
    /** Min quantifier */
    @Test public void testMinQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\min int i; 0<=i && i<=5 && (i%2)==1; i+1); \n "
                +"//@ ghost int nn = (\\min int i; 0<i && i<0; i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 2 0"
                ,"END"
        );
    }
    
    /** Max quantifier */
    @Test public void testMaxLongQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n = (\\max int i; 0<=i && i<=5 && (i%2)==0; (long)i+1); \n "
                +"//@ ghost long nn = (\\max int i; 0<i && i<0; i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 0"
                ,"END"
        );
    }
    
    /** Min quantifier */
    @Test public void testMinLongQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n = (\\min int i; 0<=i && i<=5 && (i%2)==1; (long)i+1); \n "
                +"//@ ghost long nn = (\\min int i; 0<i && i<0; i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 2 0"
                ,"END"
        );
    }
    
    /** Max quantifier */
    @Test public void testMaxDoubleQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost double n = (\\max int i; 0<=i && i<=5 && (i%2)==0; (double)i+1); \n "
                +"//@ ghost double nn = (\\max int i; 0<i && i<0; i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5.0 0.0"
                ,"END"
        );
    }
    
    /** double quantifier */
    @Test public void testMinDoubleQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost double n = (\\min int i; 0<=i && i<=5 && (i%2)==1; (double)i+1); \n "
                +"//@ ghost double nn = (\\min int i; 0<i && i<0; (double)i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 2.0 0.0"
                ,"END"
        );
    }
    
    /** boolean quantifier */
    @Test public void testBooleanQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +" boolean bb = true;"
                +"//@ ghost int n = (\\sum boolean i; bb; (i?2:5)); \n "
                +"//@ ghost int nn = (\\sum boolean i; !i; (i?2:5)); \n "
                +"//@ ghost int nnn = (\\sum boolean i; i; (i?2:5)); \n "
                +"//@ ghost int nnnn = (\\sum boolean i; false; (i?2:5)); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn + \" \" + nnn + \" \" + nnnn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 7 5 2 0"
                ,"END"
        );
    }
    
    /** Object quantifier */
    @Test public void testObjectQuantifier() {
        expectedNotes = 0;
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; import java.util.*; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +" List<Object> list = new LinkedList<Object>();\n"
                +"//@ ghost int n = (\\num_of Object o; list.contains(o); true); \n "
                +" Object oo = new Object(); list.add(new Object());\n"
                +"//@ ghost int nn = (\\num_of Object o; list.contains(o) && true; true); \n "
                +" list.add(oo);\n"
                +"//@ ghost int nnn = (\\num_of Object o; list.contains(o) && o == oo; true); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn + \" \" + nnn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 0 1 1"
                ,"END"
        );
    }
    
//    /** Represents with super model field */
//    @Test public void testModelField5() {
//        print = true;
//        addMockFile("$A/tt/B.java","package tt; class B{ //@ model int i; \n}");
//        helpTCX("tt.A","package tt; public class A extends tt.B { \n"
//                +" int j = 5; \n "
//                +"public static void main(String[] args) { \n"
//                +"A a = new A();\n"
//                +"tt.B b = new tt.B();\n"
//                +"//@ debug System.out.println(\"A \" + a.i); \n"
//                +"//@ debug System.out.println(\"B \" + b.i); \n"
//                +"b = new A();\n"
//                +"//@ debug System.out.println(\"B \" + b.i); \n"
//                +"System.out.println(\"END\"); "
//                +"}}"
//                ,"A 0"
//                ,"END"
//                );
//
//    }

    @Test public void testNullAssignment() {
        helpTCX("tt.A","package tt; import org.jmlspecs.annotation.*; @NullableByDefault public class A  { \n"
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
                );

    }

    @Test public void testNullAssignment2() {
        helpTCX("tt.A","package tt; import org.jmlspecs.annotation.*; @NullableByDefault public class A  { \n"
                +"/*@non_null*/ static Object o,oo; static Object ooo;\n"
                +"public static void main(String[] args) { \n"
                +"   A.oo = null;\n"
                +"   A.ooo = null;\n"
                +"System.out.println(\"END\"); "
                +"}} class B { //@ model  int i; represents i = 0; \n}"
                ,"/tt/A.java:4: JML assignment of null to a non_null variable"
                ,"END"
                );

    }

    @Test public void testNullInitialization() {
//        noCollectDiagnostics = true;
//        print = true;
        helpTCX("tt.A","package tt; /*@nullable_by_default*/ public class A  { \n"
                +"/*@non_null*/ static Object o,oo = null; \n"
                +"static String ooo = null;\n"
                +"//@ non_null ghost static Object oooo = null;\n"
                +"public static void main(String[] args) { \n"
                +"   /*@ non_null*/ String local = ooo;\n"
                +"   //@ ghost non_null String loc = null; \n"
                +"System.out.println(\"END\"); "
                +"}} class B {  \n}"
                ,"/tt/A.java:2: JML null initialization of non_null field oo"
                ,"/tt/A.java:4: JML null initialization of non_null field oooo"
                ,"/tt/A.java:6: JML null initialization of non_null field local"
                ,"/tt/A.java:7: JML null initialization of non_null field loc"
                ,"END"
                );
    }
    
    @Test public void testNullDefault() {
        helpTCX("tt.A","package tt; public class A  { \n"
                +"/*@nullable*/ static Object o,oo = null; \n"
                +"static Object ooo = null;\n"
                +"//@ nullable ghost static Object oooo = null;\n"
                +"public static void main(String[] args) { \n"
                +"   /*@ nullable*/ String local = (String)ooo;\n"
                +"   //@ ghost String loc = null; \n"
                +"System.out.println(\"END\"); "
                +"}} class B { \n}"
                ,"/tt/A.java:3: JML null initialization of non_null field ooo"
                ,"/tt/A.java:7: JML null initialization of non_null field loc"
                ,"END"
                );
    }
    
    // FIXME - duplicate errors for constraint (one per method)
    // check readable, writable, monitors for
    // check modifiers?
    // check more method clauses
    // check other expression types
    // what about assignable
    // check any problems with grouped clauses
    @Test public void testNotImplemented() {
        // FIXME - fix the debug statement, fix duplication and reseting of messages
        main.addOptions("-keys=DEBUG");
        //print = true;
        expectedExit = 1;
        helpTCX("tt.A","package tt; public class A  { \n"
                +"//@ axiom true;\n"
                +"//@ invariant \\duration(true) == 0;\n"
                +"//@ model long i;\n"
                +"//@ represents i =  \\duration(true);\n"
                +"//@ constraint \\duration(true) == 0;\n"
                +"//@ initially \\duration(true) == 0;\n"
                +"public static void main(String[] args) { \n"
                +"    //@ hence_by true; \n"
                +"    //@ assert \\duration(true) == 0;\n"
                +"    //@ assume \\duration(true) == 0;\n"
                +"    //@ ghost long k = \\duration(true);\n"
                +"    //@ set k = \\duration(true);\n"
                +"    //@ debug k = \\duration(true);\n" 
                +"    System.out.println(\"END\"); "
                +"}\n"
                +"//@ ghost long z = \\duration(true);\n"
                +"//@ ghost long[] zz = { \\duration(true) } ;\n"
                +"/*@ requires \\duration(true) == 0;*/"
                +"int ma() { return 0; }\n"
                +"//@ ensures \\duration(true) == 0;\n"
                +"//@ signals (Exception ex) \\duration(true) == 0;\n" // Line 20
                +"//@ signals_only RuntimeException;\n"
                +"//@ diverges \\duration(true) == 0;\n"
                +"//@ duration  \\duration(true);\n"
                +"//@ working_space \\duration(true);\n"
                +"int mb() { return 0; }\n"
                +"}"
                ,"/tt/A.java:2: Note: Not implemented for runtime assertion checking: axiom clause",5
//                ,"/tt/A.java:7: Note: Not implemented for runtime assertion checking: initially clause containing \\duration",15
//                ,"/tt/A.java:5: Note: Not implemented for runtime assertion checking: represents clause containing \\duration",5
                ,"/tt/A.java:9: Note: Not implemented for runtime assertion checking: hence_by statement",9
                ,"/tt/A.java:10: Note: Not implemented for runtime assertion checking: assert statement containing \\duration",25
                ,"/tt/A.java:11: Note: Not implemented for runtime assertion checking: assume statement containing \\duration",25
                ,"/tt/A.java:12: Note: Not implemented for runtime assertion checking: ghost declaration containing \\duration",33
                ,"/tt/A.java:13: Note: Not implemented for runtime assertion checking: set statement containing \\duration",26
                ,"/tt/A.java:14: Note: Not implemented for runtime assertion checking: debug statement containing \\duration",28
                ,"/tt/A.java:3: Note: Not implemented for runtime assertion checking: invariant clause containing \\duration",24
                ,"/tt/A.java:18: Note: Not implemented for runtime assertion checking: requires clause containing \\duration",23
                ,"/tt/A.java:6: Note: Not implemented for runtime assertion checking: constraint clause containing \\duration",25
                ,"/tt/A.java:19: Note: Not implemented for runtime assertion checking: ensures clause containing \\duration",22
                ,"/tt/A.java:20: Note: Not implemented for runtime assertion checking: signals clause containing \\duration",37
                ,"/tt/A.java:22: Note: Not implemented for runtime assertion checking: diverges clause containing \\duration",23
                ,"/tt/A.java:23: Note: Not implemented for runtime assertion checking: duration clause containing \\duration",24
                ,"/tt/A.java:24: Note: Not implemented for runtime assertion checking: working_space clause containing \\duration",28
                ,"/tt/A.java:16: Note: Not implemented for runtime assertion checking: ghost declaration containing \\duration",29
                ,"/tt/A.java:17: Note: Not implemented for runtime assertion checking: ghost declaration containing \\duration",34
                ,"/tt/A.java:5: Note: Not implemented for runtime assertion checking: method (or represents clause) containing \\duration",30
                ,"/tt/A.java:5: Unrecoverable situation: Unimplemented construct in a method or model method or represents clause",30
                ,"END"
                );

    }
    
    @Test public void testNotImplemented2() {
        helpTCX("tt.A","package tt; public class A  { \n"
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
     // FIXME - does not do inherited invariant checking when super classes are not public
    @Test public void testSuperInvariant() {
        //print = true; main.addUndocOption("-showrac");
        helpTCX("tt.A","package tt; public class A  extends B { \n"
                +" public void m() {} //@ invariant i == 1; \n"
                +"public static void main(String[] args) { \n"
                +"   new A().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"   new B().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"   new C().m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                +"class B extends C { //@ invariant i == 2; \n}\n"
                +"class C { Object o = this; int i=0; public void m() {} //@ invariant i == 3; \n}\n"
                ,"/tt/A.java:13: JML invariant is false"  // invariant in A - after C constructor, after B constructor, after A constructor, before and after m
                ,"/tt/A.java:11: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
              //  ,"/tt/A.java:13: JML invariant is false" // entering A.m
               // ,"/tt/A.java:11: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
               // ,"/tt/A.java:13: JML invariant is false" // leaving A.m
               // ,"/tt/A.java:11: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"MID"
                ,"/tt/A.java:13: JML invariant is false"  // invariant in B - after C constructor, after B constructor, before and after m
                ,"/tt/A.java:11: JML invariant is false"
                ,"/tt/A.java:13: JML invariant is false"
                ,"/tt/A.java:13: JML invariant is false"
                ,"MID"
                ,"/tt/A.java:13: JML invariant is false" // invariant in C - once after constructor, then before and after m
                ,"/tt/A.java:13: JML invariant is false"
                ,"/tt/A.java:13: JML invariant is false"
                ,"END"
                );
    }

    // FIXME - does not do inherited invariant checking
    @Test public void testSuperInvariantB() {
        //print = true; main.addUndocOption("-showrac");
        addMockFile("$A/tt/B.java","package tt; public class B extends tt.C { \n"
                +"//@  invariant i == 2; \n"
                +"}\n"
                );
        addMockFile("$A/tt/C.java","package tt; public class C { \n"
                +"Object o = this; int i=0; public void m() {} \n"
                +"//@  invariant i == 3; \n"
                +"}\n"
                );
        helpTCX("tt.A","package tt; public class A  extends B { \n"
                +" public void m() {} //@ invariant i == 1; \n"
                +"public static void main(String[] args) { \n"
                +"   new A().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"   new B().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"   new C().m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                ,"/$A/tt/C.java:3: JML invariant is false"  // C constructor
                ,"/$A/tt/C.java:3: JML invariant is false" // after B constructor
                ,"/$A/tt/B.java:2: JML invariant is false"
                ,"/$A/tt/C.java:3: JML invariant is false" // after A constructor
                ,"/$A/tt/B.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/$A/tt/C.java:3: JML invariant is false" // entering A.m
                ,"/$A/tt/B.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/$A/tt/C.java:3: JML invariant is false" // leaving A.m
                ,"/$A/tt/B.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"MID"
                ,"/$A/tt/C.java:3: JML invariant is false" // after C constructor
                ,"/$A/tt/C.java:3: JML invariant is false" // after B constructor
                ,"/$A/tt/B.java:2: JML invariant is false"
                ,"/$A/tt/C.java:3: JML invariant is false" // entering B.m (C.m)
                ,"/$A/tt/C.java:3: JML invariant is false" // leaving B.m (C.m)
                ,"MID"
                ,"/$A/tt/C.java:3: JML invariant is false" // after C constructor
                ,"/$A/tt/C.java:3: JML invariant is false" // entering C.m
                ,"/$A/tt/C.java:3: JML invariant is false" // leaving C.m
                ,"END"
                );
    }

    @Test public void testStaticInhInvariant() {
        addMockFile("$A/tt/B.java","package tt; public class B extends tt.C { \n"
                +"//@ static invariant i == 2; \n"
                +"}\n"
                );
        addMockFile("$A/tt/C.java","package tt; public class C { \n"
                +"Object o = this; static int i=0; static public void m() {} \n"
                +"//@ static invariant i == 3; \n"
                +"}\n"
                );
        helpTCX("tt.A","package tt; public class A  extends tt.B { \n"
                +" //@ static invariant i == 1; \n"
                +" static public void m() {}\n"
                +"public static void main(String[] args) { \n"
                +"System.out.println(\"A\"); \n"
                +"   A.m(); \n"  // m is in tt.C
                +"System.out.println(\"B\"); \n"
                +"   tt.B.m(); \n"  // m is in tt.C
                +"System.out.println(\"C\"); \n"
                +"   tt.C.m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                ,"/$A/tt/C.java:3: JML static invariant is false"
                ,"/$A/tt/B.java:2: JML static invariant is false"
                ,"/tt/A.java:2: JML static invariant is false" // checking invariant on main
                ,"A"
                ,"/$A/tt/C.java:3: JML static invariant is false" // entering A.m
                ,"/$A/tt/B.java:2: JML static invariant is false"
                ,"/tt/A.java:2: JML static invariant is false"
                ,"/$A/tt/C.java:3: JML static invariant is false" // leaving A.m
                ,"/$A/tt/B.java:2: JML static invariant is false"
                ,"/tt/A.java:2: JML static invariant is false"
                ,"B"
                ,"/$A/tt/C.java:3: JML static invariant is false" // entering C.m
                ,"/$A/tt/C.java:3: JML static invariant is false" // leaving C.m
                ,"C"
                ,"/$A/tt/C.java:3: JML static invariant is false" // entering C.m
                ,"/$A/tt/C.java:3: JML static invariant is false" // leaving C.m
                ,"END"
                ,"/$A/tt/C.java:3: JML static invariant is false" // leaving main
                ,"/$A/tt/B.java:2: JML static invariant is false"
                ,"/tt/A.java:2: JML static invariant is false" // checking invariant on main
                );
    }
    
    @Test public void testAssignable() {
        helpTCX("tt.A","package tt; public class A {\n"
                +"  static int j=0,k;\n"
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
                ,"/tt/A.java:3: Associated declaration"
                ,"/tt/A.java:3: JML precondition is false"
                ,"/tt/A.java:10: JML postcondition is false"
                ,"/tt/A.java:9: Associated declaration"
        );
    }
    
    @Test public void testAssignable2() {
        helpTCX("tt.A","package tt; public class A {\n"
                +"  static int j=0,k;\n"
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
                ,"/tt/A.java:3: Associated declaration"
                ,"/tt/A.java:3: JML precondition is false"
                ,"/tt/A.java:10: JML postcondition is false"
                ,"/tt/A.java:9: Associated declaration"
        );
    }
    
    @Test public void testAssignable3() {
        helpTCX("tt.A","package tt; public class A {\n"
                +"  static int j=0,k;\n"
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
                ,"/tt/A.java:7: JML An item is assigned that is not in the assignable statement"
                ,"/tt/A.java:4: Associated declaration" // FIXME - this does not make sense
        );
    }
    
    @Test public void testLabelledStatement() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { new A().m(); }\n public void m() { int i=5; \n outer: while (i > 0)  { --i; } \n /*@ assert i == 0; */ \n System.out.println(\"END\"); }}"
                ,"END");
    }

    @Test public void testLabelledStatement2() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { new A().m(); }\n public void m() { int i=5; \n outer: while (i > 0)  { --i; } \n /*@ assert i == -1; */ }}"
                ,"/tt/A.java:4: JML assertion is false"
                );
    }

    @Test public void testInitializer() {
        helpTCX("tt.A","package tt; public class A { public static void main(String[] args) {  }\n { //@ assert false; \n } " +
                "}"
                ); // The assert is not executed
    }

    @Test public void testInitializer2() {
        helpTCX("tt.A","package tt; public class A { public static void main(String[] args) { A a = new A(); System.out.println(\"END\"); }\n {  //@ assert false; \n  \n } " +
                "}"
                ,"/tt/A.java:2: JML assertion is false"
                ,"END");
    }

    @Test public void testInitializer2a() {
        helpTCX("tt.A","package tt; public class A { public static void main(String[] args) { A a = new A(); System.out.println(\"END\"); }\n  " +
                "}"
                ,"END");
    }

    @Test public void testInitializer3() {
        helpTCX("tt.A","package tt; public class A { public static void main(String[] args) {  }\n static { //@ assert false; \n } " +
                "}"
                ,"/tt/A.java:2: JML assertion is false");
    }


}
