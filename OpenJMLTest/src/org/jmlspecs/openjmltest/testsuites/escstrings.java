package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escstrings extends EscBase {
    
    /** This String declaration and assignment */
    @Test
    public void testSimpleString() {
        helpEsc("tt.TestJava","package tt; \n"
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
                +"  //@ public normal_behavior ensures t != null;\n"
                +" public TestJava() { t = new TestJava(); }\n"
                +"}"
                );
    }
    
    /** Tests String equality  */
    @Test
    public void testStringEquals() {
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava","package tt; \n"
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
                
                +"  //@ public normal_behavior ensures t != null;\n"
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",23
                
                );
    }
    
    /** Tests String concatenation - whether the result in Java is non-null. */
    @Test
    public void testStringConcat1() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assume s.length() + ss.length() <= Integer.MAX_VALUE;\n"
                +"       String sss =  (s + ss);\n"
                +"       //@ assert sss != null;\n"
                +"  }\n"
                
                +"  //@ public normal_behavior ensures t != null;\n"
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                );
    }

    /** Tests String concatenation - whether the result, computed in JML, is non-null*/
    @Test
    public void testStringConcat1a() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assume s.length() + ss.length() <= Integer.MAX_VALUE;\n"
                +"       //@ assert (s + ss) != null;\n"
                +"  }\n"
                
                +"  //@ public normal_behavior ensures t != null;\n"
                +" public TestJava() { t = new TestJava(); }\n"
                
                +"}"
                );
    }

    /** Tests String concatenation */
    @Test
    public void testStringConcat2() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assume s.length() + ss.length() <= Integer.MAX_VALUE;\n"
                +"       String sss = s + ss;\n"
                +"       String s4 = s + ss;\n"
                +"       //@ assert sss.equals(s4);\n"
                +"  }\n"
                
                +"}" 
                );
    }

    /** Tests String concatenation */
    @Test
    public void testStringConcat2a() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assume s.length() + ss.length() <= Integer.MAX_VALUE;\n"
                +"       // @ assert s.concat(ss).equals(s.concat(ss));\n"  // FIXME - not allowed by purity
                +"       //@ assert (s+ss).equals(s+ss);\n"                 // but then, why is this one
                +"  }\n"
                
                +"}" 
                );
    }

    /** Tests String concatenation */
    @Test
    public void testStringConcat3() {
        addOptions("-escMaxWarnings=1");
        addOptions("-method=m");
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  \n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assume s.length() + ss.length() <= Integer.MAX_VALUE;\n"
                +"       boolean b = (s + ss) == (s + ss); //@ assert b;\n" // Should not hold necessarily
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m",46
                );
    }

    /** Tests String concatenation */
    @Test
    public void testStringConcat3a() {
        addOptions("-escMaxWarnings=1");
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assume s.length() + ss.length() <= Integer.MAX_VALUE;\n"
                +"       //@ assert (s + ss) == (s + ss);\n" // Should not hold necessarily
                +"  }\n"
                
                +"  //@ public normal_behavior ensures t != null;\n"
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    /** Tests String charAt operation */
    @Test
    public void testStringCharAt1q() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                                
                +"  //@ requires s.length() > 0; \n"
                +"  public void m(String s) {\n"
                +"       //@ assert s.charAt(0) == s.charAt(0);\n"
                +"  }\n"
                
                +"}"
                );
    }
    
    /** Tests String charAt operation */
    @Test
    public void testStringCharAt1() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       //@ assert s.charAt(0) == s.charAt(0);\n"
                +"  }\n"
                
                +"  //@ public normal_behavior ensures t != null;\n"
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m",27
                ,"$SPECS/java/lang/String.jml:288: verify: Associated declaration",39
                ,optional(seq("$SPECS/java/lang/CharSequence.jml:65: verify: Precondition conjunct is false: 0 <= index < chars.length",34))
                );
    }

    /** Tests String charAt operation */
    @Test
    public void testStringCharAt2() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  //@ requires s.length() > 0; \n"
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       //@ assert s.charAt(0) == ss.charAt(0);\n"
                +"  }\n"
                
                +"  //@ public normal_behavior ensures t != null;\n"
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                );
    }

    /** Tests String charAt operation */
    @Test
    public void testStringCharAt3() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  //@ requires s.length() > 0;\n"
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert s.charAt(0) == ss.charAt(0);\n"  // should not hold since s != ss
                +"  }\n"
                
                +"}"
                ,anyorder(
                        seq("/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m",12)
                        ,seq("/tt/TestJava.java:6: verify: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m",43
                             ,"$SPECS/java/lang/String.jml:288: verify: Associated declaration",39
                             //,"$SPECS/java/lang/CharSequence.jml:62: verify: Precondition conjunct is false: 0 <= index < chars.length",34
                            )
                                		
                        )
                );
    }

    /** Tests String charAt operation */
    @Test
    public void testStringCharAt3a() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  //@ requires s.length() > 0 && ss.length() > 0;\n"
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert s.charAt(0) == ss.charAt(0);\n"  // should not hold since s != ss
                +"  }\n"
                
                +"  //@ public normal_behavior ensures t != null;\n"
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength1() {
    	addOptions("-method=m");
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
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
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
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
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
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
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
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
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       boolean b = s.length() == ss.length(); //@ assert b;\n" // should not hold
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m",51
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength3a() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert s.length() == ss.length(); \n" // ERROR - not necessarily same length
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    // FIXME - also test interning

}