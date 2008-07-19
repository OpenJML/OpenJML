package tests;


public class rac extends RacBase {

    String[] ordrac = new String[]{"C:/Apps/jdk1.6.0/bin/java", "-classpath","bin;testdata",null};

    protected void setUp() throws Exception {
        rac = ordrac;
        jdkrac = false;
        //noCollectDiagnostics = true;
        super.setUp();
        //options.put("-jmlverbose",   "");
        //options.put("-noInternalSpecs",   "");
    }

    public void testJava() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { System.out.println(\"HELLO WORLD\"); }}"
                ,"HELLO WORLD"
                );
    }

    public void testJML() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ ghost int i = 0; \n //@ set i = 1; \n //@ set System.out.println(i); \n System.out.println(\"END\"); }}"
                ,"1"
                ,"END"
                );
    }

    public void testAssertion() {
        helpTCX("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { //@ assert false; \n System.out.println(\"END\"); }}"
                ,"/tt/TestAssert.java:1: JML assertion is false"
                ,"END"
                );
    }

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

    public void testAssumption() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ assume false; \n System.out.println(\"END\"); }}"
                ,"/tt/TestJava.java:1: JML assumption is false"
                ,"END"
                );
    }

    public void testAssumption2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ assume false: \"DEF\"; \n System.out.println(\"END\"); }}"
                ,"/tt/TestJava.java:1: JML assumption is false (DEF)"
                ,"END"
                );
    }

    public void testUnreachable() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ unreachable; \n System.out.println(\"END\"); }}"
                ,"/tt/TestJava.java:1: JML unreachable statement reached"
                ,"END"
                );
    }

    public void testPrecondition() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(0); System.out.println(\"END\"); }\n" +
                " /*@ requires i == 0; */ static void m(int i) {} " +
                "}"
                ,"END"
                );
    }
    
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
                ,"/tt/TestJava.java:1: JML precondition is false"
                ,"END"
                );
    }
    
    public void testNonnullPostcondition() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(null,1); System.out.println(\"END\"); }\n" +
                " static /*@non_null*/Object m( Object o, int i) { return null; } " +
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
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { org.jmlspecs.utils.Utils.useExceptions = true; m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ requires true; \nensures k != i; \nalso \nrequires true; \nensures k == 0; */ static void m(int i) { k = i; } " +
                "}"
                ,"Exception in thread \"main\" org.jmlspecs.utils.Utils$JmlAssertionFailure: /tt/TestJava.java:3: JML postcondition is false"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailure(Utils.java:29)"
                ,"\tat tt.TestJava.m(TestJava.java from TestJavaFileObject:1)"
                ,"\tat tt.TestJava.main(TestJava.java from TestJavaFileObject:1)"
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
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"LABEL ENS = false"
                ,"END"
        );        
    }
    
    public void testLabel2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures (\\lblneg ENS (\\lblpos RES \\result) == 1); */ static int m(int i) { return i; } " +
                "}"
                ,"LABEL RES = 1"
                ,"LABEL ENS = true"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"LABEL RES = 0"
                ,"LABEL ENS = false"
                ,"END"
        );        
    }
    
    public void testOld() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures (\\lblneg ENS \\old(k)) == k; */ static int m(int i) { k=i; return i; } " +
                "}"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"LABEL ENS = 0"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"LABEL ENS = 1"
                ,"END"
        );        
    }
    
    public void testOld2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " static int m(int i) { //@ assert (\\lblneg AST \\old(k)) == 0; \n k=i; //@ assert (\\lblneg AST2 \\old(k)) == 0;\n //@ assert (\\lblneg AST3 k) == 0; \n return i; } " +
                "}"
                ,"/tt/TestJava.java:4: JML assertion is false"
                ,"LABEL AST = 0"
                ,"LABEL AST3 = 1"
                ,"LABEL AST2 = 0"
                ,"/tt/TestJava.java:2: JML assertion is false"
                ,"/tt/TestJava.java:3: JML assertion is false"
                ,"LABEL AST = 1"
                ,"LABEL AST3 = 0"
                ,"LABEL AST2 = 1"
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
                +"//@ ghost nullable java.lang.Class t; \n"
                +"//@ set t = (\\lblpos A \\elemtype(\\typeof(o)));\n"
                +"//@ set t = (\\lblpos B \\elemtype(\\typeof(oo)));\n"
                +"//@ set t = (\\lblpos C \\elemtype(\\typeof(o3)));\n"
                +"//@ set t = (\\lblpos D \\elemtype(java.lang.Class.class));\n"
                +"//@ set t = (\\lblpos E \\elemtype(java.lang.Boolean[].class));\n"
                +"System.out.println(\"END\"); } \n"
                +"}"
                ,"END"
                ,"LABEL D = null"
                ,"LABEL E = class java.lang.Boolean"
                ,"LABEL A = class java.lang.String"
                ,"LABEL B = int"
                ,"LABEL C = null"
                );
        
    }
    

    public void testTypeOf() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(new Object()); m(new String()); m(Boolean.TRUE); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lblpos CLS \\typeof(i)) == Object.class; \n" +
                " static void m(Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"CLASS class java.lang.Object"
                ,"LABEL CLS = class java.lang.Object"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.lang.String"
                ,"LABEL CLS = class java.lang.String"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.lang.Boolean"
                ,"LABEL CLS = class java.lang.Boolean"
                ,"END"
                );
        
    }
    
    public void testTypeOf1() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(new Object[1]); m(new String[2]); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lblpos CLS \\typeof(i)) == Object.class; \n" +
                " static void m(Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class [Ljava.lang.Object;"
                ,"LABEL CLS = class [Ljava.lang.Object;"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class [Ljava.lang.String;"
                ,"LABEL CLS = class [Ljava.lang.String;"
                ,"END"
                );
        
    }
    
    public void testTypeOf2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lblpos CLS \\typeof(i)) == Object.class; \n" +
                " static void m(int i) { \n" +
                "//@ assert (\\lblpos AST \\typeof(true)) != null; \n" +
                "//@ assert (\\lblpos AST2 \\typeof((short)0)) != null; \n" +
                "//@ assert (\\lblpos AST3 \\typeof((long)0)) != null; \n" +
                "//@ assert (\\lblpos AST4 \\typeof((byte)0)) != null; \n" +
                "//@ assert (\\lblpos AST5 \\typeof('c')) != null; \n" +
                "//@ assert (\\lblpos AST6 \\typeof(\"c\")) != null; \n" +
                "//@ assert (\\lblpos AST7 \\typeof((float)0)) != null; \n" +
                "//@ assert (\\lblpos AST8 \\typeof((double)0)) != null; \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"LABEL CLS = int"
                ,"LABEL AST = boolean"
                ,"LABEL AST7 = float"
                ,"LABEL AST6 = class java.lang.String"
                ,"LABEL AST8 = double"
                ,"LABEL AST3 = long"
                ,"LABEL AST2 = short"
                ,"LABEL AST5 = char"
                ,"LABEL AST4 = byte"
                ,"END"
                );
        
    }
    
    public void testTypeOf3() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "//@ assert (\\lblpos AST9 \\typeof(5/0)) != null; \n" +
                "//@ assert (\\lblpos AST10 \\typeof(5.0/0.0)) != null; \n" +
                "} " +
                "}"
                ,"LABEL AST10 = double"
                ,"LABEL AST9 = int"
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
                ,"/tt/TestJava.java:13: JML assertion is false"
                ,"LABEL ELEM = false"
                ,"/tt/TestJava.java:8: JML assertion is false"
                ,"/tt/TestJava.java:10: JML assertion is false"
                ,"END"
                );
        
    }
    
    public void testNonnullelement2() {
        expectedRACExit = 1;
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null); \n" +
                "System.out.println(\"END\"); } \n" +
                " static void m(Object[] o) { \n" +
                "//@ assert (\\lblpos ELEM \\nonnullelements(o)); \n" +
                "} " +
                "}"
                ,"Exception in thread \"main\" java.lang.NullPointerException"
                ,"\tat org.jmlspecs.utils.Utils.nonnullElementCheck(Utils.java:58)"
                ,"\tat tt.TestJava.m(TestJava.java from TestJavaFileObject:5)"
                ,"\tat tt.TestJava.main(TestJava.java from TestJavaFileObject:2)"
                );
        
    }
    
    public void testTypelc() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(); mm(); ma(); mg(); \n" +
                "System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "//@ ghost Class c; \n" +
                "//@ set c = \\type(int); \n" +
                "//@ set c = (\\lblpos TYP1 c); \n" +
                "//@ set c = \\type(boolean); \n" +
                "//@ set c = (\\lblpos TYP2 c); \n" +
                "}\n" +
                " static void mm() { \n" +
                "//@ ghost Class c; \n" +
                "//@ set c = \\type(java.lang.Object); \n" +
                "//@ set c = (\\lblpos TYP1 c); \n" +
                "//@ set c = \\type(Object); \n" +
                "//@ set c = (\\lblpos TYP2 c); \n" +
                "//@ set c = \\type(java.lang.String); \n" +
                "//@ set c = (\\lblpos TYP3 c); \n" +
                "//@ set c = \\type(String); \n" +
                "//@ set c = (\\lblpos TYP4 c); \n" +
                "}\n" +
                " static void ma() { \n" +
                "//@ ghost Class c; \n" +
                "//@ set c = \\type(java.lang.String[]); \n" +
                "//@ set c = (\\lblpos TYP1 c); \n" +
                "//@ set c = \\type(String[]); \n" +
                "//@ set c = (\\lblpos TYP2 c); \n" +
                "//@ set c = \\type(java.lang.String[][]); \n" +
                "//@ set c = (\\lblpos TYP3 c); \n" +
                "//@ set c = \\type(String[][]); \n" +
                "//@ set c = (\\lblpos TYP4 c); \n" +
                "} " +
                " static void mg() { \n" +
                "//@ ghost Class c; \n" +
                "//@ set c = \\type(java.lang.Class<Integer>); \n" +
                "//@ set c = (\\lblpos TYP1 c); \n" +
                "//@ set c = \\type(Class<?>); \n" +
                "//@ set c = (\\lblpos TYP2 c); \n" +
                "} " +
                "}"
                ,"LABEL TYP2 = boolean"
                ,"LABEL TYP1 = int"
                ,"LABEL TYP2 = class java.lang.Object"
                ,"LABEL TYP1 = class java.lang.Object"
                ,"LABEL TYP4 = class java.lang.String"
                ,"LABEL TYP3 = class java.lang.String"
                ,"LABEL TYP2 = class [Ljava.lang.String;"
                ,"LABEL TYP1 = class [Ljava.lang.String;"
                ,"LABEL TYP4 = class [[Ljava.lang.String;"
                ,"LABEL TYP3 = class [[Ljava.lang.String;"
                ,"LABEL TYP2 = class java.lang.Class"
                ,"LABEL TYP1 = class java.lang.Class"
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
                ,"LABEL TYP2 = true"
                ,"LABEL TYP1 = true"
                ,"LABEL TYP4 = true"
                ,"LABEL TYP3 = false"
                ,"LABEL TYP5 = false"
                ,"LABEL TYP2 = false"
                ,"LABEL TYP1 = false"
                ,"LABEL TYP4 = true"
                ,"LABEL TYP3 = false"
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
    
    /** Represents with super model field */
    public void testModelField3() {
        helpTCX("tt.A","package tt; public class A extends B { \n"
                +" int j = 5; \n "
                +"//@  represents i = j+1; \n "
                +"public static void main(String[] args) { \n"
                +"A a = new A();\n"
                +"B b = new B();\n"
                +"//@ debug System.out.println(\"A \" + a.i); \n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"b = new A();\n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); "
                +"}} class B { //@ model  int i; \n}"
                ,"A 6"
                ,"/tt/A.java:11: JML model field is not implemented: i"
                ,"B 0"
                ,"B 6"
                ,"END"
                );

    }

    /** Represents with super model field */
    public void testModelField4() {
        helpTCX("tt.A","package tt; public class A extends B { \n"
                +" int j = 5; \n "
                +"public static void main(String[] args) { \n"
                +"A a = new A();\n"
                +"B b = new B();\n"
                +"//@ debug System.out.println(\"A \" + a.i); \n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"b = new A();\n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); "
                +"}} class B { //@ model  int i; \n}"
                ,"/tt/A.java:10: JML model field is not implemented: i"
                ,"A 0"
                ,"/tt/A.java:10: JML model field is not implemented: i"
                ,"B 0"
                ,"/tt/A.java:10: JML model field is not implemented: i"
                ,"B 0"
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
        helpTCX("tt.A","package tt; /*@nullable_by_default*/ public class A  { \n"
                +"/*@non_null*/ static Object o,oo = null; \n"
                +"static Object ooo = null;\n"
                +"//@ non_null ghost static Object oooo = null;\n"
                +"public static void main(String[] args) { \n"
                +"   /*@ non_null*/ String local = (String)ooo;\n"
                +"   //@ ghost non_null String loc = null; \n"
                +"System.out.println(\"END\"); "
                +"}} class B { //@ model  int i; \n}"
                ,"/tt/A.java:2: JML null initialization of non_null variable"
                ,"/tt/A.java:4: JML null initialization of non_null variable"
                ,"/tt/A.java:6: JML null initialization of non_null variable"
                ,"/tt/A.java:7: JML null initialization of non_null variable"
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
                ,"/tt/A.java:3: JML null initialization of non_null variable"
                ,"/tt/A.java:7: JML null initialization of non_null variable"
                ,"END"
                );

    }
    
    // FIXME
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

}
