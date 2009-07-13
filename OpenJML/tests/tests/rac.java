package tests;

/** These tests exercise the RAC checking.  They compile a test class 
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
public class rac extends RacBase {

    /** Sets the classpath used for these tests.  The bin in the classpath
     * brings in the currently compiled runtime classes (so we don't have
     * to build jmlruntime.jar)
     */
    String[] ordrac = new String[]{jdk, "-classpath","bin"+z+"bin-runtime"+z+"testdata",null};

    protected void setUp() throws Exception {
        rac = ordrac;
        jdkrac = false;
        //noCollectDiagnostics = true;
        super.setUp();
        options.put("-noPurityCheck",""); // System specs have a lot of purity errors, so turn this off for now
        options.put("-noInternalSpecs",   ""); // Faster with this option; should work either way
//        options.put("-jmldebug",   "");
        //print = true;
    }

    /** Basic Hello World test, with no RAC tests triggered */
    public void testJava() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { System.out.println(\"HELLO WORLD\"); }}"
                ,"HELLO WORLD"
                );
    }

    /** Simple test of output from a JML set statement */
    public void testJML() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ ghost int i = 0; \n //@ set i = 1; \n //@ set System.out.println(i); \n System.out.println(\"END\"); }}"
                ,"1"
                ,"END"
                );
    }

    /** JML assert statement failure */
    public void testAssertion() {
        helpTCX("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { //@ assert false; \n System.out.println(\"END\"); }}"
                ,"/tt/TestAssert.java:1: JML assertion is false"
                ,"END"
                );
    }

    /** JML labeled assert statement failure */
    public void testAssertion2() {
        helpTCX("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { //@ assert false: \"ABC\"; \n System.out.println(\"END\"); }}"
                ,"/tt/TestAssert.java:1: JML assertion is false (ABC)"
                ,"END"
                );
    }

    // FIXME - need to put in type conversion
//    public void testAssertion3() {
//        helpTCX("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { //@ assert false: args.length; \n System.out.println(\"END\"); }}"
//                ,"/tt/TestAssert.java:1: JML assertion is false"
//                ,"END"
//                );
//    }

    /** Assumption failure */
    public void testAssumption() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ assume false; \n System.out.println(\"END\"); }}"
                ,"/tt/TestJava.java:1: JML assumption is false"
                ,"END"
                );
    }

    /** Labeled assumption failure */
    public void testAssumption2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ assume false: \"DEF\"; \n System.out.println(\"END\"); }}"
                ,"/tt/TestJava.java:1: JML assumption is false (DEF)"
                ,"END"
                );
    }

    /** Failed unreachable statement */
    public void testUnreachable() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ unreachable; \n System.out.println(\"END\"); }}"
                ,"/tt/TestJava.java:1: JML unreachable statement reached"
                ,"END"
                );
    }

    /** Successful precondition */
    public void testPrecondition() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(0); System.out.println(\"END\"); }\n" +
                " /*@ requires i == 0; */ static void m(int i) {} " +
                "}"
                ,"END"
                );
    }
    
    /** Failed precondition */
    public void testPrecondition2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(0); System.out.println(\"END\"); }\n" +
                " /*@ requires i != 0; */ static void m(int i) {} " +
                "}"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"END"
                );
    }
    
    public void testNonnullPrecondition() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(null,1); System.out.println(\"END\"); }\n" +
                " /*@ requires true; */ \nstatic void m(/*@non_null*/ Object o, int i) {} " +
                "}"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"END"
                );
    }
    
    public void testNonnullPrecondition2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(null,1); System.out.println(\"END\"); }\n" +
                " static void m(/*@non_null*/ Object o, int i) {} " +
                "}"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"END"
                );
    }
    
    public void testNonnullPostcondition() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(null,1); System.out.println(\"END\"); }\n" +
                " static /*@non_null*/Object m( /*@nullable*/Object o, int i) { return null; } " +
                "}"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"END"
                );
    }
    
    // TODO need multiple requires, multiple spec cases

    public void testPostcondition() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures k == i; */ static int m(int i) { k = i; return 13; } " +
                "}"
                ,"END"
                );
    }

    public void testPostcondition1() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures k == 0; */ \nstatic int m(int i) { k = i; return 13; } " +
                "}"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"END"
                );
    }

    public void testPostcondition2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ requires true; \nalso \nrequires false; \nensures k == 0; */ static void m(int i) { k = i; } " +
                "}"
                ,"END"
                );
    }

    public void testPostcondition3() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ requires true; \nensures true; \nalso \nrequires false; \nensures k == 0; */ static void m(int i) { k = i; } " +
                "}"
                ,"END"
                );
    }

    public void testPostcondition4() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ requires true; \nensures k != i; \nalso \nrequires true; \nensures k == 0; */ static void m(int i) { k = i; } " +
                "}"
                ,"/tt/TestJava.java:3: JML postcondition is false"
                ,"/tt/TestJava.java:6: JML postcondition is false"
                ,"END"
                );
    }
    
    public void testPostcondition5() {
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
                ,"Exception in thread \"main\" org.jmlspecs.utils.Utils$JmlAssertionError: /tt/TestJava.java:10: JML postcondition is false"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailure(Utils.java:38)"
                ,"\tat tt.TestJava.m(TestJava.java:10)"
                ,"\tat tt.TestJava.main(TestJava.java:5)"
                );
    }
    
    public void testSignals() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \nsignals (java.io.FileNotFoundException e) e == null; */\n"
                +"static void m(int i) throws java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"/tt/TestJava.java:7: JML signals condition is false"
                ,"END"
                );
    }

    public void testSignals2() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \nsignals (java.io.FileNotFoundException e) e == null; */\n"
                +"static void m(int i) throws Exception, java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"/tt/TestJava.java:7: JML signals condition is false"
                ,"END"
                );
    }
    
    public void testSignalsOnly() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \nsignals_only \\nothing; */\n"
                +"static void m(int i) throws Exception, java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"/tt/TestJava.java:7: JML signals_only condition is false"
                ,"END"
                );
    }

    public void testSignalsOnly1() {
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

    public void testSignalsOnly2() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \nsignals_only java.io.FileNotFoundException; */\n"
                +"static void m(int i) throws Exception, java.io.FileNotFoundException { throw new Exception(); } "
                +"}"
                ,"/tt/TestJava.java:7: JML signals_only condition is false"
                ,"END"
                );
    }

    public void testSignalsOnlyDefault() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \n*/\n"
                +"static void m(int i) throws java.io.FileNotFoundException { throw new RuntimeException(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML unexpected exception"
                ,"END"
                );
    }

    public void testSignalsOnlyDefault1() {
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

    public void testResult() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures \\result == 4; */ static int m(int i) { return 4; } " +
                "}"
                ,"END"
        );
    }

    public void testResult1() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures \\result == 4; */ static int m(int i) { return 5; } " +
                "}"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"END"
        );
    }
    
    public void testLabel() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures (\\lblneg ENS \\result == 1); */ static int m(int i) { return i; } " +
                "}"
                ,"LABEL ENS = true"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"END"
        );        
    }
    
    public void testLabel2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures (\\lblneg ENS (\\lbl RES \\result) == 1); */ static int m(int i) { return i; } " +
                "}"
                ,"LABEL RES = 1"
                ,"LABEL ENS = true"
                ,"LABEL RES = 0"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"END"
        );        
    }
    
    public void testOld() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures (\\lbl ENS \\old(k)) == k; */ static int m(int i) { k=i; return i; } " +
                "}"
                ,"LABEL ENS = 0"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"LABEL ENS = 1"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"END"
        );        
    }
    
    public void testOld2() {
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
    
    public void testInformal() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " static int m(int i) { System.out.println(i); //@ assert (i==0) <==> (* informal *); \n return i; } " +
                "}"
                ,"1"
                ,"/tt/TestJava.java:2: JML assertion is false"
                ,"0"
                ,"END"
                );
    }

    public void testElemtype() {
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
    

    public void testTypeOf() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(new Object()); m(new String()); m(Boolean.TRUE); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i).erasure()) == Object.class; \n" +
                " static void m(/*@nullable*/Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"LABEL CLS = class java.lang.Object"
                ,"CLASS class java.lang.Object"
                ,"LABEL CLS = class java.lang.String"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.lang.String"
                ,"LABEL CLS = class java.lang.Boolean"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.lang.Boolean"
                ,"END"
                );
        
    }
    
    public void testTypeOf1() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(new Object[1]); m(new String[2]); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i)) == \\type(Object); \n" +
                " static void m(/*@nullable*/Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"LABEL CLS = class [Ljava.lang.Object;"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class [Ljava.lang.Object;"
                ,"LABEL CLS = class [Ljava.lang.String;"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class [Ljava.lang.String;"
                ,"END"
                );
        
    }
    
    public void testTypeOf2() {
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
    
    public void testTypeOf3() {
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
    
    public void testNonnullelement() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "String[] s2null = new String[]{null,\"B\"}; \n" +
                "String[] s2 = new String[]{\"A\",\"B\"}; \n" +
                "m(new Object[]{}); \n" +
                "m(new String[]{\"A\"}); \n" +
                "m(s2); \n" +
                "m(s2null); \n" +
                "//@ assert \\nonnullelements(s2,s2null); \n" +
                "//@ assert \\nonnullelements(s2,s2); \n" +
                        // Tests shortcut evaluation
                "//@ assert \\nonnullelements(s2null,new Integer[]{5/0}); \n" +
                "System.out.println(\"END\"); } \n" +
                " static void m(Object[] o) { \n" +
                "//@ assert (\\lblpos ELEM \\nonnullelements(o)); \n" +
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
    
    public void testNonnullelement2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null); \n" +
                "System.out.println(\"END\"); } \n" +
                " static void m(/*@nullable*/Object[] o) { \n" +
                "//@ assert (\\lblpos ELEM \\nonnullelements((\\lbl O o))); \n" +
                "} " +
                "}"
                ,"LABEL O = null"
                ,"LABEL ELEM = false"
                ,"/tt/TestJava.java:5: JML assertion is false"
                ,"END"
                );
        
    }
    
    public void testLbl() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null); \n" +
                "org.jmlspecs.utils.Utils.printValues();\n"+
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
                ,"/tt/TestJava.java:15: JML assertion is false"
                ,"LABEL OBJECT = null"
                ,"LABEL STRING = abc"
                ,"END"
                );
        
    }
    
    public void testLblConst() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null); \n" +
                "org.jmlspecs.utils.Utils.printValues();\n"+
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
                "} " +
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
                ,"LABEL TYP1 = class java.lang.Class"
                ,"LABEL TYP2 = class java.lang.Class"
                ,"END"
                );
        
    }
    
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
                "//@ set c = o.getClass() <: o.getClass(); \n" + // Object <: Object
                "//@ set c = (\\lblpos TYP1 c); \n" +
                "//@ set c = \\typeof(o) <: \\typeof(o); \n" +  // Object <: Object
                "//@ set c = (\\lblpos TYP2 c); \n" +
                "//@ set c = \\typeof(o) <: \\typeof(oo); \n" + // Object <: String
                "//@ set c = (\\lblpos TYP3 c); \n" +
                "//@ set c = \\typeof(oo) <: \\typeof(o); \n" + // String <: Object
                "//@ set c = (\\lblpos TYP4 c); \n" +
                "//@ set c = \\typeof(ob) <: \\typeof(oo); \n" + // Boolean <: String
                "//@ set c = (\\lblpos TYP5 c); \n" +
                "}\n" +
                " static void mm() { \n" +
                "//@ ghost boolean c; \n" +
                "//@ set c = s.getClass() <: b.getClass(); \n" + // String <: Boolean
                "//@ set c = (\\lblpos TYP1 c); \n" +
                "//@ set c = \\typeof(s) <: \\typeof(b); \n" +  // String <: Boolean
                "//@ set c = (\\lblpos TYP2 c); \n" +
                "//@ set c = \\type(int) <: \\typeof(o); \n" + // int <: Object
                "//@ set c = (\\lblpos TYP3 c); \n" +
                "//@ set c = \\type(int) <: \\type(int); \n" + // int <: int  // false
                "//@ set c = (\\lblpos TYP4 c); \n" +
                "//@ set c = \\type(int) <: \\type(boolean); \n" + // int <: boolean
                "//@ set c = (\\lblpos TYP5 c); \n" +
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

    public void testUndefined() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); m(1); System.out.println(\"END\"); } \n" +
                " //@ requires 10/i == 0; \n" +
                " //@ ensures 10/i == 0; \n" +
                " static void m(int i) { \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:3: JML precondition is undefined - exception thrown"
                ,"/tt/TestJava.java:4: JML postcondition is undefined - exception thrown"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"END"
                );
        
    }
    
    public void testUndefined2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); m(1); System.out.println(\"END\"); } \n" +
                " //@ requires i != 0; \n" +
                " //@ requires 10/i == 10; \n" +
                " static void m(int i) { \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:5: JML precondition is false"
                ,"END"
                );
        
    }
    
    public void testForLoop2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(); System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "    //@ loop_invariant i <9 ; \n" +
                "    //@ decreases 10-i; \n" +
                "    for (int i=0; i<10; i++) ; \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:4: JML loop invariant is false"
                ,"/tt/TestJava.java:4: JML loop invariant is false"
                ,"END"
                );
    }

    public void testForLoop() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(); System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "    //@ loop_invariant i <= 10 ; \n" +
                "    //@ decreases 7-i; \n" +
                "    for (int i=0; i<10; i++) ; \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:5: JML loop variant is less than 0"
                ,"/tt/TestJava.java:5: JML loop variant is less than 0"
                ,"/tt/TestJava.java:5: JML loop variant is less than 0"
                ,"END"
                );
    }

    public void testForEachLoop() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(); System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "    int[] a = new int[10];\n" +
                "    //@ ghost int i = 0; \n" +
                "    //@ loop_invariant i <= a.length ; \n" +
                "    //@ decreases a.length-i; \n" +
                "    for (int j: a) { \n" +
                "       //@ set i = i + 1;\n" +
                "    }\n" +
                "} " +
                "}"
                ,"END"
                );
    }
    public void testForEachLoop2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(); System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "    int[] a = new int[10];\n" +
                "    //@ ghost int i = 0; \n" +
                "    //@ loop_invariant i < a.length ; \n" +
                "    //@ decreases a.length-i-2; \n" +
                "    for (int j: a) { \n" +
                "       //@ set i = i + 1;\n" +
                "    }\n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:7: JML loop variant is less than 0"
                ,"/tt/TestJava.java:6: JML loop invariant is false"
                ,"/tt/TestJava.java:7: JML loop variant is less than 0"
                ,"END"
                );
    }

    
    public void testLoop() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(5); m(0); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "    //@ loop_invariant i>= 0; \n" +
                "    //@ decreases i; \n" +
                "    while (i>0) --i; \n" +
                "} " +
                "}"
                ,"END"
                );
    }

    
    public void testLoop2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(5); m(0); m(-1); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "    System.out.println(\"VALUE \" + i); \n" +
                "    //@ loop_invariant i>= 0; \n" +
                "    //@ decreases i; \n" +
                "    while (i>=0) --i; \n" +
                "} " +
                "}"
                ,"VALUE 5"
                ,"/tt/TestJava.java:5: JML loop invariant is false"
                ,"/tt/TestJava.java:6: JML loop variant is less than 0"
                ,"VALUE 0"
                ,"/tt/TestJava.java:5: JML loop invariant is false"
                ,"/tt/TestJava.java:6: JML loop variant is less than 0"
                ,"VALUE -1"
                ,"/tt/TestJava.java:5: JML loop invariant is false"
                ,"/tt/TestJava.java:6: JML loop variant is less than 0"
                ,"END"
                );
    }

    
    public void testDoLoop() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(5); m(1); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "    //@ loop_invariant i>= 0; \n" +
                "    //@ decreases i; \n" +
                "    do { --i; } while (i>0); \n" +
                "} " +
                "}"
                ,"END"
                );
    }

    
    public void testDoLoop2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(5); m(0); m(-1); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "    System.out.println(\"VALUE \" + i); \n" +
                "    //@ loop_invariant i>= 0; \n" +
                "    //@ decreases i; \n" +
                "    do { --i; } while (i>=0); \n" +
                "} " +
                "}"
                ,"VALUE 5"
                ,"/tt/TestJava.java:5: JML loop invariant is false"
                ,"/tt/TestJava.java:6: JML loop variant is less than 0"
                ,"VALUE 0"
                ,"/tt/TestJava.java:5: JML loop invariant is false"
                ,"/tt/TestJava.java:6: JML loop variant is less than 0"
                ,"VALUE -1"
                ,"/tt/TestJava.java:5: JML loop invariant is false"
                ,"/tt/TestJava.java:6: JML loop variant is less than 0"
                ,"/tt/TestJava.java:5: JML loop invariant is false"
                ,"/tt/TestJava.java:6: JML loop variant is less than 0"
                ,"END"
                );
    }

    public void testSpecFile() {
        addMockFile("$A/tt/A.spec","package tt; public class A { //@ ghost static int i = 0;\n  //@ invariant i == 0; \n //@ requires i == 1;\n static int m(); }");
        helpTCX("tt.A","package tt; public class A { static int m() { return 0; }  \n public static void main(String[] args) { m(); System.out.println(\"END\"); }}"
                ,"/$A/tt/A.spec:3: JML precondition is false"
                ,"END"
                );
        
    }

    public void testSpecFile2() {
        addMockFile("$A/tt/A.spec","package tt; public class A { //@ ghost static int i = 0;\n  //@ invariant i == 0; \n //@ ensures i == 1;\n static int m(); }");
        helpTCX("tt.A","package tt; public class A { static int m() { //@ set i = 1; \n return 0; }  \n public static void main(String[] args) { m(); System.out.println(\"END\"); }}"
                ,"END"
                );
        
    }

    public void testSpecModelMethod() {
        addMockFile("$A/tt/A.spec","package tt; public class A { " 
                +"/*@ model static pure int mm() { return 5; } */ "
                +"//@ ghost static int i = 0;\n  "
                +"//@ invariant i == 0; \n //@ ensures i == 1;\n static int m(); "
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { static int m() { //@ set i = mm(); \n return 0; }  \n public static void main(String[] args) { m(); System.out.println(\"END\"); }}"
                ,"/$A/tt/A.spec:3: JML postcondition is false"
                ,"END"
                );
        
    }

    public void testSpecModelClass() {
        addMockFile("$A/tt/A.spec","package tt; public class A { \n" 
                +"/*@ model static class AA { static int mm() { return 5; }} */ \n"
                +"//@ ghost static int i = 0;\n  "
                +"//@ invariant i == 0; \n "
                +"//@ ensures i == 1;\n "
                +"static int m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int m() { //@ set i = AA.mm(); \n return 0; }  \n "
                +"public static void main(String[] args) { \n"
                +"m(); "
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/$A/tt/A.spec:5: JML postcondition is false"
                ,"END"
                );
        
    }
    
    public void testStaticInvariant() {
        addMockFile("$A/tt/A.spec","package tt; public class A { \n" 
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
                ,"/$A/tt/A.spec:2: JML static invariant is false"
                ,"MID"
                ,"/$A/tt/A.spec:2: JML static invariant is false"
                ,"END"
                );
    }

    public void testStaticInvariant2() {
        addMockFile("$A/tt/A.spec","package tt; public class A { \n" 
                +"//@ static invariant i == 0; \n "
                +"void m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int i = 0;  \n "
                +"void m() { i = 1-i; }  \n "
                +"public static void main(String[] args) { \n"
                +"new A().m(); "
                +"System.out.println(\"MID\"); "
                +"new A().m(); "
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/$A/tt/A.spec:2: JML static invariant is false"
                ,"MID"
                ,"/$A/tt/A.spec:2: JML static invariant is false"
                ,"/$A/tt/A.spec:2: JML static invariant is false"
                ,"END"
                );
    }

    public void testInvariant() {
        addMockFile("$A/tt/A.spec","package tt; public class A { \n" 
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
                ,"/$A/tt/A.spec:2: JML invariant is false"
                ,"MID"
                ,"/$A/tt/A.spec:2: JML invariant is false"
                ,"END"
                );
    }

    public void testInitially() {
        addMockFile("$A/tt/A.spec","package tt; public class A { \n" 
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
                ,"/$A/tt/A.spec:3: JML initially is false"
                ,"END"
                );
    }


    public void testConstraint() {
        addMockFile("$A/tt/A.spec","package tt; public class A { \n" 
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
                ,"/$A/tt/A.spec:2: JML constraint is false"
                ,"END"
                );
    }

    public void testHelper() {
        addMockFile("$A/tt/A.spec","package tt; public class A { \n" 
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

    public void testSuchThat() {
        expectedErrors = 1;
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int j = 5; \n "
                +"//@ static model int i; \n "
                +"//@ static represents i \\such_that i == j+1; \n "
                +"public static void main(String[] args) { \n"
                +"System.out.println(\"END\"); "
                +"}"
                +"}"
                ,"/tt/A.java:4: warning: Not implemented for runtime assertion checking: relational represents clauses (\\such_that)",13
                ,"END"
                );

    }
    
    public void testModelField() {
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
    
    /** Duplicate represents */
    public void testModelField1() {
        expectedExit = 1;
        expectedErrors = 1;
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
                ,"/tt/A.java:5: Duplicate represents clause - only the first is used for RAC",13
                );

    }
    
    // TODO - the following two tests fail when the compile policy is
    // SIMPLE instead of BY_TODO - for some reason the principal class
    // file (PA or QA) does not get written.
    
    /** Represents with super model field */
    public void testModelField3() {
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
                ,"A 6"
                ,"/tt/PA.java:11: JML model field is not implemented: i"
                ,"B 0"
                ,"B 6"
                ,"END"
                );

    }

    /** Represents with super model field */
    public void testModelField4() {
        helpTCX("tt.QA","package tt; public class QA extends QB { \n"
                +" int j = 5; \n "
                +"public static void main(String[] args) { \n"
                +"QA a = new QA();\n"
                +"QB b = new QB();\n"
                +"//@ debug System.out.println(\"A \" + a.i); \n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"b = new QA();\n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); "
                +"}} class QB { //@ model  int i; \n}"
                ,"/tt/QA.java:10: JML model field is not implemented: i"
                ,"A 0"
                ,"/tt/QA.java:10: JML model field is not implemented: i"
                ,"B 0"
                ,"/tt/QA.java:10: JML model field is not implemented: i"
                ,"B 0"
                ,"END"
                );

    }

    /** Model field with no represents */
    public void testModelField2() {
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int j = 5; \n "
                +"//@ static model int i; \n "
                +"public static void main(String[] args) { \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:3: JML model field is not implemented: i"
                ,"A 0"
                ,"END"
        );
    }
    
//    /** Represents with super model field */
//    public void testModelField5() {
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

    public void testNullAssignment() {
        helpTCX("tt.A","package tt; import org.jmlspecs.annotations.*; @NullableByDefault public class A  { \n"
                +"/*@non_null*/ static String o=\"\",oo=\"\"; static Object ooo;\n"
                +"public static void main(String[] args) { \n"
                +"   oo = null;\n"
                +"   ooo = null;\n"
                +"   /*@ non_null*/ String local = \"\";\n"
                +"   local = (String)ooo;"
                +"System.out.println(\"END\"); "
                +"}} class B { //@ model  int i; \n}"
                ,"/tt/A.java:4: JML assignment of null to non_null"
                ,"/tt/A.java:7: JML assignment of null to non_null"
                ,"END"
                );

    }

    public void testNullAssignment2() {
        helpTCX("tt.A","package tt; import org.jmlspecs.annotations.*; @NullableByDefault public class A  { \n"
                +"/*@non_null*/ static Object o,oo; static Object ooo;\n"
                +"public static void main(String[] args) { \n"
                +"   A.oo = null;\n"
                +"   A.ooo = null;\n"
                +"System.out.println(\"END\"); "
                +"}} class B { //@ model  int i; \n}"
                ,"/tt/A.java:4: JML assignment of null to non_null"
                ,"END"
                );

    }

    public void testNullInitialization() {
//        noCollectDiagnostics = true;
//        print = true;
        helpTCX("tt.A","package tt; /*@nullable_by_default*/ public class A  { \n"
                +"/*@non_null*/ static Object o,oo = null; \n"
                +"static Object ooo = null;\n"
                +"//@ non_null ghost static Object oooo = null;\n"
                +"public static void main(String[] args) { \n"
                +"   /*@ non_null*/ String local = (String)ooo;\n"
                +"   //@ ghost non_null String loc = null; \n"
                +"System.out.println(\"END\"); "
                +"}} class B { //@ model  int i; \n}"
                ,"/tt/A.java:2: JML null initialization of non_null variable oo"
                ,"/tt/A.java:4: JML null initialization of non_null variable oooo"
                ,"/tt/A.java:6: JML null initialization of non_null variable local"
                ,"/tt/A.java:7: JML null initialization of non_null variable loc"
                ,"END"
                );

    }
    
    public void testNullDefault() {
        helpTCX("tt.A","package tt; public class A  { \n"
                +"/*@nullable*/ static Object o,oo = null; \n"
                +"static Object ooo = null;\n"
                +"//@ nullable ghost static Object oooo = null;\n"
                +"public static void main(String[] args) { \n"
                +"   /*@ nullable*/ String local = (String)ooo;\n"
                +"   //@ ghost String loc = null; \n"
                +"System.out.println(\"END\"); "
                +"}} class B { //@ model  int i; \n}"
                ,"/tt/A.java:3: JML null initialization of non_null variable ooo"
                ,"/tt/A.java:7: JML null initialization of non_null variable loc"
                ,"END"
                );

    }
    
    // FIXME - disabled
    public void _testSuperInvariant() {
        print = true;
        helpTCX("tt.A","package tt; public class A  extends B { \n"
                +" //@ invariant i == 1; \n"
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
                ,"/tt/A.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"END"
                );
    }

    // FIXME - disabled
    public void _testStaticInhInvariant() {
        print = true;
        addMockFile("$A/tt/B.java","package tt; public class B extends tt.C { \n"
                +"//@ static invariant i == 2; \n"
                +"}\n"
                );
        addMockFile("$A/tt/C.java","package tt; public class tt.C { Object o = this; static int i=0; static public void m() {} \n"
                +"//@ static invariant i == 3; \n"
                +"}\n"
                );
        helpTCX(new String[]{"tt.A","tt.B","tt.C"},"package tt; public class A  extends tt.B { \n"
                +" //@ static invariant i == 1; \n"
                +"public static void main(String[] args) { \n"
                +"System.out.println(\"A\"); \n"
                +"   A.m(); \n"
                +"System.out.println(\"B\"); \n"
                +"   tt.B.m(); \n"
                +"System.out.println(\"C\"); \n"
                +"   tt.C.m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"/tt/A.java:2: JML invariant is false"
                ,"END"
                );
    }

}
