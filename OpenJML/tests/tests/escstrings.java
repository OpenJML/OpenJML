package tests;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(Parameterized.class)
public class escstrings extends EscBase {
    
    public escstrings(String option, String solver) {
        super(option,solver);
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
    
    /** Tests String equality without the String specs */
    @Test
    public void testStringEquals() {
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
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m",20
                
                );
    }
    
    /** Tests String equality */
    @Test
    public void testStringEqualsNoSpecs1() {
        main.addOptions("-noInternalSpecs");
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
    public void testStringEqualsNoSpecs2() {
        main.addOptions("-noInternalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       /*@ nullable */ String sss = null;\n"
                +"       //@ assert !s.equals(sss);\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }
   
    /** Tests String equality */
    @Test
    public void testStringEqualsNoSpecs3() {
        main.addOptions("-noInternalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       /*@ nullable */ String sss = null;\n"
                +"       //@ assert !sss.equals(ss);\n" // Null error
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m",20
                );
    }
   
    /** Tests String concatenation */
    @Test
    public void testStringConcatNoSpecs1() {
        main.addOptions("-noInternalSpecs");
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
                ,!"yices2".equals(solver)?null:// FIXME because yices2 cannot do quantifiers
                    "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }
   
    /** Tests String concatenation */
    @Test
    public void testStringConcatNoSpecs2() {
        main.addOptions("-noInternalSpecs");
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
                ,!"yices2".equals(solver)?null:// FIXME because yices2 cannot do quantifiers
                    "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m",19
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }
   
    /** Tests String concatenation */
    @Test
    public void testStringConcatNoSpecs3() {
        main.addOptions("-noInternalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert (s + ss) == (s + ss);\n" // FIXME Should not hold necessarily
                +"  }\n"
                
                +"}"
// FIXME                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }
   
    /** Tests String concatenation */
    @Test
    public void testStringConcat1() {
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
                ,!"yices2".equals(solver)?null: // FIXME because yices2 cannot do quantifiers
                    "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    /** Tests String concatenation */
    @Test
    public void testStringConcat2() {
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
                ,!"yices2".equals(solver)?null:// FIXME because yices2 cannot do quantifiers
                    "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m",19
                //,!"yices2".equals(solver)?null: // FIXME because yices2 cannot do quantifiers
                //    "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    /** Tests String concatenation */
    @Test
    public void testStringConcat3() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert (s + ss) == (s + ss);\n" // FIXME - Should not hold necessarily
                +"  }\n"
                
                +"}"
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
                +"       //@ assert s.charAt(0) == ss.charAt(0);\n"  // FIXME - should not hold
                +"  }\n"
                
                +"}"
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
                +"       //@ assert s.length() >= 0;\n"
                +"  }\n"
                
                +"}"
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength1a() {
        main.addOptions("-noInternalSpecs");
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
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
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
                +"       //@ assert s.length() == ss.length();\n"
                +"  }\n"
                
                +"}"
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength2a() {
        main.addOptions("-noInternalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       //@ assert s.length() == ss.length();\n"
                +"  }\n"
                
                +"}" // FIXME - determinism should fix this
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m",12
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
                +"       //@ assert s.length() == ss.length();\n" // FIXME - should not hold
                +"  }\n"
                
                +"}"
//                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength3a() {
        main.addOptions("-noInternalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert s.length() == ss.length();\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    // FIXME - also test interning
    // FIXME - check charAt(i) if i 0 or >= length

}