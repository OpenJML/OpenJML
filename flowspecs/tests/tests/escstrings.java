package tests;

import java.util.Collection;

import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class escstrings extends EscBase {
    
    public escstrings(String option, String solver) {
        super(option,solver);
    }
    
    @Parameters
    static public  Collection<String[]> datax() {
        java.util.List<String> ss = new java.util.LinkedList<String>();
        ss.addAll(solvers);
        ss.remove("cvc4"); // FIXME - hangs up on CVC4 - fix the long proof times
        ss.remove("yices2"); // FIXME - yices2 does not support quantifiers and so works poorly with strings
        return makeData(ss);
    }
    

    @Override
    public void setUp() throws Exception {
        super.setUp();
    }
    
    /** This String declaration and assignment */
    @Test
    public void testSimpleString() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m1(String s) {\n"
                +"       String ss = s;\n"
                +"       //@ assert s != null;\n"
                +"       //@ assert s == ss;\n"
                +"  }\n"
                
                
                +"}"
                );
    }
    
    /** Tests String equality  */
    @Test
    public void testStringEquals() {
        main.addOptions("-method=m");
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       /*@ nullable */ String sss = null;\n"
                +"       //@ assert s.equals(ss);\n"
                +"       //@ assert !s.equals(sss);\n"
                +"       //@ assert !sss.equals(ss);\n" // Null error
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",23
                
                );
    }
    
    /** Tests String equality */
    @Test
    public void testStringEqualsNoSpecs1a() {
        main.addOptions("-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       /*@ nullable */ String sss = null;\n"
                +"       //@ assert s.equals(ss);\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }
   
    /** Tests String equality */
    @Test
    public void testStringEqualsNoSpecs1() {
        main.addOptions("-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       /*@ nullable */ String sss = null;\n"
                +"       boolean b = s.equals(ss); //@ assert b;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m",38
                );
    }
   
    /** Tests String equality */
    @Test
    public void testStringEqualsNoSpecs2() {
        main.addOptions("-internalSpecs=false");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       /*@ nullable */ String sss = null;\n"
                +"       boolean b = !s.equals(sss); //@ assert b;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m",40
                );
    }
   
    /** Tests String equality */
    @Test
    public void testStringEqualsNoSpecs3() {
        main.addOptions("-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       /*@ nullable */ String sss = null;\n"
                +"       //@ assert  !sss.equals(ss);\n" // Null error
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",24
                );
    }
   
    /** Tests String concatenation */
    @Test
    public void testStringConcatNoSpecs1() {
        main.addOptions("-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       boolean b = (s + ss) != null; //@ assert b;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",42
                );
    }
   
    /** Tests String concatenation */
    @Test
    public void testStringConcatNoSpecs1a() {
        main.addOptions("-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert (s + ss) != null;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }
   
    /** Tests String concatenation */
    @Test
    public void testStringConcatNoSpecs2() {
        main.addOptions("-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       boolean b = (s+ss).equals(s+ss); //@ assert b;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",-45
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m",26
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",-45
                );
    }
   
    /** Tests String concatenation */
    @Test
    public void testStringConcatNoSpecs2a() {
        main.addOptions("-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert (s+ss).equals(s+ss);\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",-25
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",-25
                );
    }
   
    /** Tests String concatenation */
    @Test
    public void testStringConcatNoSpecs3() {
        main.addOptions("-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       boolean b = (s + ss) == (s + ss); //@ assert b;\n" // Should not hold necessarily
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",46
                );
    }
   
    /** Tests String concatenation */
    @Test
    public void testStringConcatNoSpecs3a() {
        main.addOptions("-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert (s + ss) == (s + ss); \n" // Should not hold necessarily
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }
   
    /** Tests String concatenation - whether the result in Java is non-null. */
    @Test
    public void testStringConcat1() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       String sss =  (s + ss);\n"
                +"       //@ assert sss != null;\n"
                +"  }\n"
                
                +"}"
                ,!"yices2".equals(solver)?null: // FIXME because yices2 cannot do quantifiers
                    "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    /** Tests String concatenation - whether the result, computed in JML, is non-null*/
    @Test
    public void testStringConcat1a() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert (s + ss) != null;\n"
                +"  }\n"
                
                +"}"
                ,!"yices2".equals(solver)?null: // because yices2 cannot do quantifiers
                    "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    /** Tests String concatenation */
    @Test @Ignore
    public void testStringConcat2() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       String sss = s + ss;\n"
                +"       String s4 = s + ss;\n"
                +"       //@ assert sss.equals(s4);\n"
                +"  }\n"
                
                +"}"  // FIXME - need more semantics of concat and equals
                ,!"yices2".equals(solver)?null:// FIXME because yices2 cannot do quantifiers
                    "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",12
                );
    }

    /** Tests String concatenation */
    @Test @Ignore
    public void testStringConcat2a() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert (s+ss).equals(s+ss);\n"
                +"  }\n"
                
                +"}"  // FIXME - need more semantics of concat and equals
                ,!"yices2".equals(solver)?null:// because yices2 cannot do quantifiers
                    "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",19
                );
    }

    /** Tests String concatenation */
    @Test
    public void testStringConcat3() {
        main.addOptions("-escMaxWarnings=1");
        main.addOptions("-method=m");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       boolean b = (s + ss) == (s + ss); //@ assert b;\n" // Should not hold necessarily
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",46
                );
    }

    /** Tests String concatenation */
    @Test
    public void testStringConcat3a() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert (s + ss) == (s + ss);\n" // Should not hold necessarily
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    /** Tests String charAt operation */
    @Test
    public void testStringCharAt1() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       //@ assert s.charAt(0) == s.charAt(0);\n"
                +"  }\n"
                
                +"}"
                );
    }

    /** Tests String charAt operation */
    @Test
    public void testStringCharAt2() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       //@ assert s.charAt(0) == ss.charAt(0);\n"
                +"  }\n"
                
                +"}"
                );
    }

    /** Tests String charAt operation */
    @Test
    public void testStringCharAt3() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert s.charAt(0) == ss.charAt(0);\n"  // should not hold since s != ss
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength1() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       boolean b = s.length() >= 0; //@ assert b;\n"
                +"  }\n"
                
                +"}"
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength1a() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       //@ assert s.length() >= 0;\n"
                +"  }\n"
                
                +"}"
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength2() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       boolean b = s.length() == ss.length(); //@ assert b;\n"
                +"  }\n"
                
                +"}"
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength2a() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       //@ assert s.length() == ss.length(); \n"
                +"  }\n"
                
                +"}"
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength3() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       boolean b = s.length() == ss.length(); //@ assert b;\n" // should not hold
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",51
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength3a() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert s.length() == ss.length(); \n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    // FIXME - also test interning
    // FIXME - check charAt(i) if i 0 or >= length

}