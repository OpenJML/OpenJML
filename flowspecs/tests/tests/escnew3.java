package tests;

import java.util.Collection;

import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class escnew3 extends EscBase {

    public escnew3(String option, String solver) {
        super(option,solver);
    }
    
    // Test well-definedness within the implicit old
    @Test
    public void testNonNullElements() {
        if ("yices2".equals(solver)) return; // TODO: yices2 cannot handle quantifiers - better error message
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
                
                +"  //@ modifies \\everything;\n"
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
                
                +"  //@ modifies \\everything;\n"
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
                
                +"  //@ modifies \\everything;\n"
                +"  public void m4a(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 3;\n"
                +"    a[0] = new Object();\n"
                +"    a[1] = new Object();\n"
                +"    //@ assert \\nonnullelements(a);\n" // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m5(Object[] a) {\n"
                +"    //@ assume \\nonnullelements(a) && a.length == 3;\n"
                +"    a[0] = new Object();\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m5a(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 3;\n" // Line 75
                +"    a[0] = null;\n"
                +"    //@ assert \\nonnullelements(a);\n" // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
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
    
    // TODO - test not_modified and old nested in each other; remember to test definedness            


}
