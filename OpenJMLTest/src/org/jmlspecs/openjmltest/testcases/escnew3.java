package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.ParameterizedWithNames;
import org.junit.runners.Parameterized.Parameters;

@RunWith(ParameterizedWithNames.class)
public class escnew3 extends EscBase {

    public escnew3(String options, String solver) {
        super(options,solver);
    }
    
    // Test well-definedness within the implicit old
    @Test
    public void testNonNullElements() {
        Assume.assumeTrue(!"z3_4_3".equals(solver));
        Assume.assumeTrue(!"cvc4".equals(solver));
        Assume.assumeTrue(!"yices2".equals(solver)); // TODO: yices2 cannot handle quantifiers - better error message
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1x(/*@ non_null */ Object[] a) {\n"
                +"    //@ assume \\nonnullelements(a);\n"
                +"    //@ assume a.length > 1;\n"
                +"    //@ assert a[0] != null;\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m11(Object[] a) {\n"
                +"    //@ assume \\nonnullelements(a);\n"
                +"    //@ assert a != null;\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m11a(Object[] a) {\n"
                +"    //@ assume \\nonnullelements(a);\n"
                +"    //@ assert a == null;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1a(Object[] a) {\n"
                +"    //@ assume a != null && a.length > 1;\n"
                +"    //@ assert a[0] != null;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m2(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 0;\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m22(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 0;\n"
                +"    //@ assert (\\forall int i; 0<=i && i<a.length; a[i] != null);\n" // OK
                +"  }\n"
                
                +"  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                +"  public void m3(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 1;\n"
                +"    a[0] = new Object();" // No return so as not to bollix the line numbers in the error messages
                +"    //@ assert a[0] != null;\n" // OK
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m33(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 1;\n"
                +"    //@ assume a[0] != null;\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                +"  public void m4(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 2;\n"
                +"    a[0] = new Object();\n"
                +"    a[1] = new Object();\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m44(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 2;\n"
                +"    //@ assume a[0] != null;\n"
                +"    //@ assume a[1] != null;\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                +"  public void m4a(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 3;\n"
                +"    a[0] = new Object();\n"
                +"    a[1] = new Object();\n"
                +"    //@ assert \\nonnullelements(a);\n" // BAD
                +"  }\n"
                
                +"  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                +"  public void m5(Object[] a) {\n"
                +"    //@ assume \\nonnullelements(a) && a.length == 3;\n"
                +"    a[0] = new Object();\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                +"  public void m5a(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 3;\n" // Line 75
                +"    a[0] = null;\n"
                +"    //@ assert \\nonnullelements(a);\n" // BAD
                +"  }\n"
                
                +"  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                +"  public void m5b(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 3;\n"
                +"    //@ assume \\nonnullelements(a);\n" 
                +"    a[0] = null;\n"
                +"    //@ assert \\nonnullelements(a);\n" // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m5c(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 0;\n"
                +"    //@ assert \\nonnullelements(a);\n"
                +"  }\n"
                
                 
                +"}"
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method m11a",9
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (Assert) in method m1a",9
                ,"/tt/TestJava.java:65: warning: The prover cannot establish an assertion (Assert) in method m4a",9
                ,"/tt/TestJava.java:77: warning: The prover cannot establish an assertion (Assert) in method m5a",9
                ,"/tt/TestJava.java:84: warning: The prover cannot establish an assertion (Assert) in method m5b",9
                );
    }
    
    @Test
    public void testNotModified() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires i == 5;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m1(int i) {\n"
                +"    i = 5;\n"
                +"    //@ assert \\not_modified(i);\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1a(int i) {\n"
                +"    i = 5;\n"
                +"    //@ assert \\not_modified(i);\n"  // BAD
                +"  }\n"
                
                +"  public int i;\n"
                +"  public static int si;\n"
                +"  //@ ghost public int gi;\n"
                
                +"  //@ requires i == 5;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m2() {\n"
                +"    i = 5;\n"
                +"    //@ assert \\not_modified(i);\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m2a() {\n"
                +"    i = 5;\n"
                +"    //@ assert \\not_modified(i);\n"  // BAD
                +"  }\n"
                
                +"  //@ requires si == 5;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m3() {\n"
                +"    si = 5;\n"
                +"    //@ assert \\not_modified(si);\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m3a() {\n"
                +"    si = 5;\n"
                +"    //@ assert \\not_modified(si);\n"  // BAD
                +"  }\n"
                
                +"  //@ requires gi == 5;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m4() {\n"
                +"    //@ set gi = 5;\n"
                +"    //@ assert \\not_modified(gi);\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m4a() {\n"
                +"    //@ set gi = 5;\n"
                +"    //@ assert \\not_modified(gi);\n"  // BAD
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method m1a",9
                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Assert) in method m2a",9
                ,"/tt/TestJava.java:37: warning: The prover cannot establish an assertion (Assert) in method m3a",9
                ,"/tt/TestJava.java:48: warning: The prover cannot establish an assertion (Assert) in method m4a",9
                );
    }
    
    // Test well-definedness within the implicit old
    @Test
    public void testNotModified2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int i;\n"
                +"  public static /*@ nullable */ TestJava t;\n"
                
                +"  //@ requires t != null;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m0() {\n"
                +"    //@ assert \\not_modified(t.i);\n"  // OK
                +"  }\n"
                
                +"  //@ requires t != null;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m1a() {\n"
                +"    t = null;\n"
                +"    //@ assert \\not_modified(t.i) ? true: true;\n"  // BAD
                +"  }\n"
                
                +"  //@ requires t == null;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m1b() {\n"
                +"    t = new TestJava();\n"
                +"    //@ assert \\not_modified(t.i) ? true: true;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1c() {\n"
                +"    //@ assert \\not_modified(t.i) ? true: true;\n"  // BAD
                +"  }\n"
                
                 
                +"}"
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1a",31
                ,"/tt/TestJava.java:20: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1b",31
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1c",31
                );
    }
    
    @Test
    public void testCast() {
        main.addOptions("-code-math=safe","-spec-math=safe");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public static long l;\n"
                +"  public static int i;\n"
                +"  public static short s;\n"
                +"  public static char c;\n"
                +"  public static byte b;\n"
                
                +"  //@ requires i == 6;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m0() {\n"
                +"    s = (short)i;\n"
                +"    //@ assert s == i;\n"  // OK
                +"    b = (byte)i;\n"
                +"    //@ assert b == i;\n"  // OK
                +"    c = (char)i;\n"
                +"    //@ assert c == i;\n"  // OK
                +"    l = (long)i;\n"
                +"    //@ assert l == i;\n"  // OK 
                +"    int ii = (int)i;\n"
                +"    //@ assert ii == i;\n"  // OK
                
                +"    //@ assert i == (short)i;\n"
                +"    //@ assert i == (long)i;\n"
                +"    //@ assert i == (char)i;\n"
                +"    //@ assert i == (byte)i;\n"
                +"    //@ assert i == (int)i;\n"
                +"  }\n"
                 
                +"  //@ requires i == 100000;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m0bad() {\n"
                +"    s = (short)i;\n"  // Line 30
                +"    //@ assert s == i;\n" 
                +"  }\n"
                 
                +"  //@ requires i == 100000;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m0badx() {\n"
                +"    //@ assert i == (short)i;\n" // BAD
                +"  }\n"
                 
                +"  //@ requires i == 100000;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m1badx() {\n"
                +"    //@ assert i == (byte)i;\n" 
                +"  }\n"
                 
                +"  //@ requires i == 100000;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m2badx() {\n"
                +"    //@ assert i == (char)i;\n" 
                +"  }\n"
                 
                +"  //@ requires i == 100000;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m1bad() {\n"
                +"    b = (byte)i;\n"
                +"    //@ assert b == i;\n"
                +"  }\n"
                 
                +"  //@ requires i == 100000;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m2bad() {\n"
                +"    c = (char)i;\n"
                +"    //@ assert c == i;\n"
                +"  }\n"
                 
                +"}"
                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m0bad",9
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m0badx",21
                ,"/tt/TestJava.java:41: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m1badx",21
                ,"/tt/TestJava.java:46: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m2badx",21
                ,"/tt/TestJava.java:51: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m1bad",9
                ,"/tt/TestJava.java:57: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m2bad",9
                );
    }
    
    @Test
    public void testCast1() {
        main.addOptions("-escMaxWarnings=1");  // FIXME - issues very many warnings - lots of nearly identical paths?
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m0() {\n"
                +"    {/*@ nullable */ Short s = null;\n"
                +"    short ss = (short)s;\n"  
                +"    //@ assert 0 == (short)s;\n}"  
                +"  }\n"
                                  
                +"  //@ modifies \\everything;\n"
                +"  public void m1() {\n"
                +"    {/*@ nullable */ Integer s = null;\n"
                +"    int ss = (int)s;\n"  
                +"    //@ assert 0 == (int)s;\n}"  
                +"  }\n"
                                  
                +"  //@ modifies \\everything;\n"
                +"  public void m2() {\n"
                +"    {/*@ nullable */ Long s = null;\n"
                +"    long ss = (long)s;\n"  
                +"    //@ assert 0L == (long)s;\n}"  
                +"  }\n"
                                  
                +"  //@ modifies \\everything;\n"
                +"  public void m3() {\n"
                +"    {/*@ nullable */ Byte s = null;\n"
                +"    byte ss = (byte)s;\n"  
                +"    //@ assert 0 == (byte)s;\n}"  
                +"  }\n"
                                  
                +"  //@ modifies \\everything;\n"
                +"  public void m4() {\n"
                +"    {/*@ nullable */ Character s = null;\n"
                +"    char ss = (char)s;\n"  
                +"    //@ assert 0 == (char)s;\n}"  
                +"  }\n"
                                  
                +"  //@ modifies \\everything;\n"
                +"  public void m7() {\n"
                +"    {/*@ nullable */ Boolean s = null;\n"
                +"    boolean ss = (boolean)s;\n"  
                +"    //@ assert (boolean)s;\n}"  
                +"  }\n"
                                  
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m0",16
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m1",14
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m2",15
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m3",15
                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m4",15
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m7",18
                );
    }
    
    @Test
    public void testCast1real() {
        Assume.assumeTrue(runLongTests || !"z3_4_3".equals(solver));
        main.addOptions("-logic=AUFLIRA","-escMaxWarnings=1");  // FIXME - issues very many warnings - lots of nearly identical paths?
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m5() {\n"
                +"    {/*@ nullable */ Double s = null;\n"
                +"    double ss = (double)s;\n"  
                +"    //@ assert 0 == (double)s;\n}"  
                +"  }\n"
                                  
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m5",17
                );
    }
    
    @Test
    public void testCast1realb() {
        Assume.assumeTrue(runLongTests || !"z3_4_3".equals(solver));
        main.addOptions("-logic=AUFLIRA","-escMaxWarnings=1");  // FIXME - issues very many warnings - lots of nearly identical paths?
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m6() {\n"
                +"    {/*@ nullable */ Float s = null;\n"
                +"    float ss = (float)s;\n"  
                +"    //@ assert 0.0 == (float)s;\n}"  
                +"  }\n"
                                  
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m6",16
                );
    }
    
    // TODO - test not_modified and old nested in each other; remember to test definedness            

    @Test
    public void testAssignableConstructor0() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private int i;\n"
                +"  //@ assignable \\everything;\n"
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor1() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private int i;\n"
                +"  //@ assignable i;\n"
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                ,"/tt/TestJava.java:4: An identifier with private visibility may not be used in a assignable clause with public visibility",18
                );
    }

    @Test
    public void testAssignableConstructor2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private int i;\n"
                +"  //@ assignable \\nothing;\n"
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assignable) in method TestJava:  i",25
//                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignableConstructor3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private int i;\n"
                +"  \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assignable) in method TestJava:  i",25
//                ,"/tt/TestJava.java:5: warning: Associated declaration",10
                );
    }

    @Test
    public void testAssignableConstructor3a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private int i;\n"
                +"  //@ requires true; \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assignable) in method TestJava:  i",25
//                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignableConstructor3ae() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private int i;\n"
                +"  //@ requires true; assignable this.*; \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assignable) in method TestJava:  i",25
//                ,"/tt/TestJava.java:4: warning: Associated declaration",22
                );
    }

    @Test
    public void testAssignableConstructor3e() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private int i;\n"
                +"  //@ assignable this.*; \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assignable) in method TestJava:  i",25
//                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignableConstructor4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { //@ public nullable model Object state;\n"
                +"  private int i; //@ in state;\n"
                +"  \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor4e() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { //@ public nullable model Object state;\n"
                +"  private int i; //@ in state;\n"
                +"  //@ assignable this.*; \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor4a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { //@ public nullable model Object state;\n"
                +"  private int i; //@ in state;\n"
                +"  //@ requires true;\n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor4ae() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { //@ public nullable model Object state;\n"
                +"  private int i; //@ in state;\n"
                +"  //@ requires true; assignable this.*; \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor5() {
    	//main.addOptions("-jmldebug");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { //@ public nullable model Object state;\n"
                +"  private int i; //@ in state;\n"
                +"  //@ assignable state; \n"
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor5s() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { //@ public nullable model Object state;\n"
                +"  private int i; //@ in state;\n"
                +"  //@ assignable this.state; \n"
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor6() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava {\n"
                +"  /*@ spec_public */ private int i;\n"
                +"  \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor6a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava {\n"
                +"  /*@ spec_public */ private int i;\n"
                +"  //@ requires true; \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor6e() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava {\n"
                +"  /*@ spec_public */ private int i;\n"
                +"  //@ assignable this.*; \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor6ae() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava {\n"
                +"  /*@ spec_public */ private int i;\n"
                +"  //@ requires true; assignable this.*; \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor7() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  /*@ spec_public */ private int i; \n"
                +"  //@ assignable i; \n"
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor7s() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  /*@ spec_public */ private int i; \n"
                +"  //@ assignable this.i; \n"
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testVarargs() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ nullable_by_default */ public class TestJava { \n"
                +"  //@ ensures \\result == ints.length;\n"
                +"  //@ pure \n"
                +"  public static int m(Integer ... ints) { \n"
                +"    //@ assert ints != null; \n"
                +"    return ints.length; }\n"
                
                +"  public static void n(/*@ non_null*/Integer[] args) { \n"
                +"    int i = m(args); \n"
                +"    //@ assert i == args.length; \n"
                +"    }\n"
                
                +"  public static void n0() { \n"
                +"    int i = m(); \n"
                +"    //@ assert i == 0; \n"
                +"    }\n"
                
                +"  public static void n1() { \n"
                +"    int i = m(1); \n"
                +"    //@ assert i == 1; \n"
                +"    }\n"
                
                +"  public static void n2() { \n"
                +"    int i = m(1,1); \n"
                +"    //@ assert i == 2; \n"
                +"    }\n"
                +"}"
                );
    }

    @Test
    public void testVarargs2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ ensures \\result == (ints.length > 0 ? ints[0] : ints.length);\n"
                +"  //@ pure \n"
                +"  public static int m(int ... ints) { \n"
                +"    //@ assert ints != null; \n"
                +"    if (ints.length > 0) return ints[0]; else return ints.length; }\n"
                
                +"  public static void n0() { \n"
                +"    int i = m(); \n"
                +"    //@ assert i == 0; \n"
                +"    }\n"
                
                +"  public static void n1() { \n"
                +"    int i = m(2); \n"
                +"    //@ assert i == 2; \n"
                +"    }\n"
                
                +"  public static void n2() { \n"
                +"    int i = m(5,6); \n"
                +"    //@ assert i == 5; \n"
                +"    }\n"
                +"}"
                );
    }

    @Test
    public void testVarargs3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires ints.length == 0 || ints[0] != null;\n"
                +"  //@ ensures \\result == (ints.length > 0 ? ints[0] : ints.length);\n"
                +"  //@ pure \n"
                +"  public static int m(Integer ... ints) { \n"
                +"    //@ assert ints != null; \n"
                +"    if (ints.length > 0) return ints[0]; else return ints.length; }\n"
                
                +"  public static void n0() { \n"
                +"    int i = m(); \n"
                +"    //@ assert i == 0; \n"
                +"    }\n"
                
                +"  public static void n1() { \n"
                +"    int i = m(2); \n"
                +"    //@ assert i == 2; \n"
                +"    }\n"
                
                +"  public static void n2() { \n"
                +"    int i = m(5,6); \n"
                +"    //@ assert i == 5; \n"
                +"    }\n"
                +"}"
                );
    }


    @Test
    public void testBits() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m() {\n"
                +"     boolean b = true;\n"
                +"     boolean bb = false;\n"
                +"     //@ assert !(b & bb);\n"
                +"     //@ assert (b | bb);\n"
                +"     //@ assert (b ^ bb);\n"
                +"     //@ assert (b & bb);\n" // FALSE
                +"    }\n"
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m",10
                );
    
    }
    
    @Test
    public void testLabels() {
    	main.addOptions("-show","-method=m");
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava { \n"
                + "  //@ requires i == 10;\n"
                + "  public void m(int i) {\n"
                + "     a:{};\n"
                + "     i = 12;\n"
                + "     b:{};\n"
                + "     i = 14;\n"
                + "     //@ assert \\old(i) == 10;\n"
                + "     //@ assert \\old(i,a) == 10;\n"
                + "     //@ assert \\old(i,b) == 12;\n"
                + "     //@ assert i == 14;\n"
                + "    }\n"
                + "}"
                 );
        
    }

    @Test
    public void testLabels2() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava { \n"
                + "  public int k;\n"
                + "  /*@ ensures \\result == k; */ public int mm() { return k; }\n"
                + "  //@ requires k == 10;\n"
                + "  public void m() {\n"
                + "     a:{}\n"
                + "     k = 12;\n"
                + "     b:{}\n"
                + "     k = 14;\n"
                + "     //@ assert \\old(mm()) == 10;\n"
                + "     //@ assert \\old(mm(),a) == 10;\n"
                + "     //@ assert \\old(mm(),b) == 12;\n"
                + "     //@ assert mm() == 14;\n"
                + "    }\n"
                + "}"
                 );
        
    }
    
    @Test
    public void testOldClause() {
    	main.addOptions("-escMaxWarnings=1","-subexpressions","-show","-method=m");
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava { \n"
                + "  static public int k = 5;\n"
                + "  //@ old int kk = k; requires k == 5 && i > kk && i < 100 && i > -100; assignable k; ensures k == i+1; ensures kk == 5;\n"
                + "  //@ also\n"
                + "  //@ old int kk = k+1; requires k == 5 && i < kk && i < 100 && i > -100; assignable k; ensures k == i-1; ensures kk == 6;\n"
                + "  static public void m(int i) {\n"
                + "     if (i>k) k = i+1; else k = i-1;\n"
                + "  }\n"
                + "}"
                 );
        
    }
    
    @Ignore // FIXME - fix up label scoping
    @Test
    public void testBadLabel() {
        helpTCX("tt.TestJava",
                                "package tt; \n"
                              + "public class TestJava { \n"
                              + "  public int k;\n"
                              + "  public void m() {\n"
                              + "     //@ assert \\old(k,a) == 10;\n"
                              + "     a:{}\n"
                              + "     k = 12;\n"
                              + "     while(k > 10) {  a:{} k--; }\n"
                              + "     while(k > 6) {  b:{ b:{} } k--; }\n"
                              + "     while(k > 5) {  b:{} b:{} k--; }\n"
                              + "     while(k > 0) {  c:{} k--;}\n"
                              + "     k = 14;\n"
                              + "     //@ assert \\old(k,c) == 12;\n"
                              + "    }\n"
                              + "}"
                               );
                      
        
    }

    @Test
    public void testIfNoBrace() {
        helpTCX("tt.TestJava",
                                "package tt; \n"
                              + "public class TestJava { \n"
                              + "  //@ requires i > -10 && i < 10;\n"
                              + "  public void m(int i) {\n"
                              + "     if (i < 0) \n"
                              + "        //@ assert i < 0;\n" // OK
                              + "        i = -i; \n"
                              + "     //@ assert i >= 0;\n" // OK
                              + "    }\n"
                              + "}"
                               );
                      
        
    }

    @Test @Ignore
    public void testIfNoBrace2() {
        helpTCX("tt.TestJava",
                                "package tt; \n"
                              + "public class TestJava { \n"
                              + "  //@ requires i > -10 && i < 10;\n"
                              + "  public void m(int i) {\n"
                              + "     if (i < 0) \n"
                              + "        i = -i; \n"
                              + "        //@ assert i < 0;\n"  // false, since not in if
                              + "     //@ assert i >= 0;\n"
                              + "    }\n"
                              + "}"
                              ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m", 13
                               );
                      
        
    }

    @Test
    public void testIfNoBrace3() {
        helpTCX("tt.TestJava",
                                "package tt; \n"
                              + "public class TestJava { \n"
                              + "  //@ requires i > -10 && i < 10;\n"
                              + "  public void m(int i) {\n"
                              + "     if (i < 0) \n"
                              + "        i = -i; \n"
                              + "        //@ assert i > 0;\n"  // false, since not in if
                              + "     //@ assert i >= 0;\n"
                              + "    }\n"
                              + "}"
                              ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m", 13
                               );
                      
        
    }

    @Test
    public void testOldClause2() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  static public int k = 5;\n"
                + "  //@ old int kk = k;\n"
                + "  //@ {| requires i < 10 && i > kk; assignable k; ensures k == i+1; \n"
                + "  //@ also\n"
                + "  //@    requires i > -10 && i < kk; assignable k; ensures k == i-1; \n"
                + "  //@ |}\n"
                + "  static public void m(int i) {\n"
                + "     if (i>k) k = i+1; else k = i-1;\n"
                + "  }\n"
                + "}"
                 );
        
    }
    

    // Problem from Michael Coblenz - git issue #504
    @Test
    public void testSimpleClone() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  public String y = \"\";\n"
                + " \n"
                + "  public int[] foo() {\n"
                + "     int[] result1 = new int[]{1};\n"
                + "     int[] result2 = result1.clone();\n"
                + "     return result2;\n"
                + "  }\n"
                + "}"
                 );
        
    }
    

}
