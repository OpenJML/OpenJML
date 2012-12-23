package tests;

import org.jmlspecs.openjml.Utils;
import org.junit.Ignore;
import org.junit.Test;

/** These tests exercise the RAC checking.  They compile a test class 
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
public class racnew2 extends RacBase {

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
        options.put("-newesc", "");
        options.put("-showNotImplemented", "");
        options.put("-noPurityCheck",""); // System specs have a lot of purity errors, so turn this off for now
        options.put("-noInternalSpecs",   ""); // Faster with this option; should work either way
        options.put("-showrac", "");
        //options.put("-verboseness",   "4");
        expectedNotes = 0;
    }

    /** Tests type test and type cast expressions */
    @Test public void testTypeCast() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  Integer i = new Integer(10); \n" +
                "  Object o = i; \n" +
                "  Integer ii = (Integer)o; \n" +
                "  System.out.println(ii); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"10"
                ,"END"
        );        
    }

    /** Tests a bad cast */
    @Test public void testTypeCast2() {
        expectedRACExit = 1;
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  Boolean i = Boolean.TRUE; \n" +
                "  Object o = i; \n" +
                "  Integer ii = (Integer)o;\n" +
                "  System.out.println(ii); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"/tt/TestJava.java:4: JML A cast is invalid - from java.lang.Object to java.lang.Integer"
                ,"  Integer ii = (Integer)o;"
                ,"               ^"
                ,"Exception in thread \"main\" java.lang.ClassCastException: java.lang.Boolean cannot be cast to java.lang.Integer"
                ,"\tat tt.TestJava.main(TestJava.java:4)"
        );        
    }

    /** Tests a type test with a cast */
    @Test public void testTypeCast3() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  Boolean b = Boolean.TRUE; \n" +
                "  Integer i = new Integer(10); /*@ nullable */Integer ii = null; \n" +
                "  Object o = i; \n" +
                "  if (o instanceof Integer) { ii = (Integer)o; }\n" +
                "  o = b; \n" +
                "  if (o instanceof Integer) { ii = (Integer)o; }\n" +
                "  System.out.println(ii); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"10"
                ,"END"
        );        
    }


    /** Tests the JML lbl lblpos and lblneg expressions */
    @Test public void testLbl() {
        options.put("-noRacSource", "");
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
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
                "//@ assert (\\lbl CHAR (char)(i+60)) != 0; \n" +
                "//@ assert (\\lbl BOOLEAN (i == 0)) ; \n" +
                "//@ assert (\\lbl OBJECT o) == null; \n" +
                "//@ assert (\\lbl NULL null) == null; \n" +
                "//@ assert (\\lbl STRING \"abc\") != null; \n" +
                "//@ assert (\\lblpos POST (i!=0)); \n" +
                "//@ assert !(\\lblpos POSF (i==0)); \n" +
                "//@ assert (\\lblneg NEGT (i!=0)); \n" +
                "//@ assert !(\\lblneg NEGF (i==0)); \n" +
                "//@ assert !(\\lblpos POST (i!=0)); \n" +
                "//@ assert (\\lblneg NEGF (i==0)); \n" +
                "} " +
                "}"
                ,"LABEL STRING = def"
                ,"LABEL SHORT = 1"
                ,"LABEL LONG = 2"
                ,"LABEL BYTE = 3"
                ,"LABEL INT = 4"
                ,"LABEL FLOAT = 5.0"
                ,"LABEL DOUBLE = 6.0"
                ,"LABEL CHAR = B"
                ,"LABEL BOOLEAN = false"
                ,"/tt/TestJava.java:14: JML assertion is false"
                ,"LABEL OBJECT = null"
                ,"LABEL NULL = null"
                ,"LABEL STRING = abc"
                ,"LABEL POST = true"
                ,"LABEL NEGF = false"
                ,"LABEL POST = true"
                ,"/tt/TestJava.java:22: JML assertion is false"
                ,"LABEL NEGF = false"
                ,"/tt/TestJava.java:23: JML assertion is false"
                ,"END"
                );
        
    }
    
    /** Tests the JML lbl expression when the argument is a literal */
    // FIXME - This is failing to print many cases at present 
    @Test public void testLblConst() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null); \n" +
                "System.out.println(\"END\"); } static int i = 0; \n" +
                " static void m(/*@nullable*/ Object o) { \n" +
                "//@ assert (\\lbl OBJECT null) == null; \n" + // const null arguments get optimized away
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
    
    /** A misc early test case for lbl expressions */
    @Test public void testLabel() {
        helpTCX("tt.TestJava","package tt; public class TestJava { /*@ assignable \\everything; */ public static void main(String[] args) { \n" +
                " m(1); m(0); \n" +
                " System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ assignable \\everything; ensures (\\lbl ENS k == 1); */ \n" +
                " static void m(int i) { System.out.println(\"i = \" + i ); k = i; } " +
                "}"
                ,"i = 1"
                ,"i = 0"
                ,"LABEL ENS = true"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:1: JML postcondition is false"
                ,"END"
        );        
    }
    
    /** A misc early test case for lbl expressions */
    @Test public void testLabel2() {
        //options.put("-noRacSource", "");
        helpTCX("tt.TestJava","package tt; public class TestJava { /*@ assignable \\everything; */ public static void main(String[] args) { \n" +
                " m(1); m(0); \n" +
                " System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ assignable \\everything; ensures (\\lblneg ENS (\\lbl RES k) == 1); */ \n" +
                " static void m(int i) { k = i; return; } " +
                "}"
                ,"LABEL RES = 1"
                ,"LABEL RES = 1"
                ,"LABEL RES = 0"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:5: JML postcondition is false"  // FIXME - no source
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"LABEL RES = 0"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"END"
        );        
    }
    


}
