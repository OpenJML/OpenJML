package tests;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(Parameterized.class)
public class escConstantFields extends EscBase {

    public escConstantFields(String option, String solver) {
        super(option,solver);
    }
    
    @Test
    public void testBasic() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final static int I = 1;\n"
                +"  public final static int J = 1 + I;\n"
                +"  //@ ensures J == 2;\n"
                +"  public TestJava() {  }\n"
                +"  //@ ensures J == 2;\n"
                +"  public void m() {}\n"
                +"  //@ ensures J == 2;\n"
                +"  static public void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testGhost() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ ghost public final static int I = 1;\n"
                +"  //@ ghost public final static int J = 1 + I;\n"
                +"  //@ ensures J == 2;\n"
                +"  public TestJava() {  }\n"
                +"  //@ ensures J == 2;\n"
                +"  public void m() {}\n"
                +"  //@ ensures J == 2;\n"
                +"  static public void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testFields() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final static int I = 1;\n"
                +"  //@ ghost public final static int J = 1 + I;\n"
                // Does not need the invariant
                
                +"  public TestJava() { \n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n" // final variables are not affected by assignable \everything
                +"     //@ assert I == 1 && J == 2;\n"
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n" // final variables are not affected by assignable \everything
                +"     //@ assert I == 1 && J == 2;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  static public void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testFieldsNotFinal() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static int I = 1;\n"
                +"  //@ ghost public static int J = 1 + I;\n"
                +"  //@ public static invariant I == 1 && J == 2;\n"

                +"  public TestJava() { \n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n" // reestablishes the static invariant
                +"     //@ assert I == 1 && J == 2;\n"
                +"  }\n"

                +"  //@ ensures J == 2;\n"
                +"  public void m() {\n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n" // reestablished the static invariant
                +"     //@ assert I == 1 && J == 2;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  static public void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testFieldsNotConstant() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final static int I = z();\n"  // FIXME - static initialization check should fail
                +"  //@ ghost public final static int J = 1 + I;\n"
                +"  //@ public static invariant I == 10 && J == 11;\n"

                +"  public TestJava() { \n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"     n();\n" // reestablished the static invariant
                +"     //@ assert I == 10 && J == 11;\n"
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"     n();\n" // reestablished the static invariant
                +"     //@ assert I == 10 && J == 11;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  static public void n() {}\n"
                +"  static public int z() { return 10; }\n"
                +"}"
                );
    }

    @Test
    public void testFieldsNotConstantWithHelper() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final static int I = z();\n"  // FIXME - static initialization check should fail
                +"  //@ ghost public final static int J = 1 + I;\n"
                +"  //@ public static invariant I == 10 && J == 11;\n"

                +"  public TestJava() { \n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"     n();\n" // reestablished the static invariant
                +"     //@ assert I == 10 && J == 11;\n"
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"     n();\n" // reestablished the static invariant
                +"     //@ assert I == 10 && J == 11;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  static public void n() {}\n"
                +"  /*@ helper */ static private int z() { return 10; }\n"
                +"}"
                );
    }

    @Test
    public void testIFields() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final int I = 1;\n"
                +"  //@ ghost public final int J = 1 + I;\n"
                
                +"  public TestJava() { \n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  public void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testIFieldsS() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final int I = 1;\n"
                +"  //@ ghost public final int J = 1 + I;\n"
                // Does not need the invariant
                
                +"  public TestJava() { \n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n" // does not reestablish instance invariants
                +"     //@ assert I == 1 && J == 2;\n" // but OK because final constant fields are not modified by \everything
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n" // does not reestablish instance invariants
                +"     //@ assert I == 1 && J == 2;\n" // but OK because final fields are not modified by \everything
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  static public void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testIFieldsNotFinal() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public int I = 1;\n"
                +"  //@ ghost public int J = 1 + I;\n"
                +"  //@ public invariant I == 1 && J == 2;\n"

                +"  public TestJava() { \n"
                +"     //@ assert I == 1 && J == 2;\n" // OK
                +"     n();\n"
                +"     //@ assert I == 1 && J == 2;\n" // Should be OK because of invariant on n()
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 1 && J == 2;\n" // OK because of invariant
                +"     n();\n"
                +"     //@ assert I == 1 && J == 2;\n" // Should be OK because of invariant on n()
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  public void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testIFieldsNotFinalS() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public int I = 1;\n"
                +"  //@ ghost public int J = 1 + I;\n"
                +"  //@ public invariant I == 1 && J == 2;\n"

                +"  public TestJava() { \n"
                +"     //@ assert I == 1 && J == 2;\n" // OK
                +"     n();\n"
                +"     //@ assert I == 1 && J == 2;\n" // Fails because n is static and so does not establish the invariant
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 1 && J == 2;\n" // OK because of invariant
                +"     n();\n"
                +"     //@ assert I == 1 && J == 2;\n" // Fails because n is static and so does not establish the invariant
                +"  }\n"
                
                +"  //@ public normal_behavior assignable \\everything;\n"
                +"  static public void n() {}\n"
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method <init>",10
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (InvariantReenterCaller) in method m",7
                ,"/tt/TestJava.java:5: warning: Associated declaration: /tt/TestJava.java:13: ",14
                );
    }

    @Test
    public void testIFieldsNotConstant() {
        main.addOptions("-show","-method=TestJava");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final int I = z();\n"
                +"  //@ ghost public final int J = 1 + I;\n"
                +"  //@ public invariant I == 10 && J == 11;\n" // FIXME - check that this is required

                +"  public TestJava() { \n"
                +"     //@ assert I == 10 && J == 11;\n" // OK because of invariant
                +"     n();\n"
                +"     //@ assert I == 10 && J == 11;\n" // Should be OK because of invariant on n()
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 10 && J == 11;\n" // OK because of invariant
                +"     n();\n"
                +"     //@ assert I == 10 && J == 11;\n" // Should be OK because of invariant on n()
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  public void n() {}\n"
                
                +"  //@ public normal_behavior ensures \\result == 10;\n"
                +"  static public int z() { return 10; }\n"
                +"}"
                );
    }

    @Test
    public void testIFieldsNotConstantS() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final int I = z();\n"
                +"  //@ ghost public final int J = 1 + I;\n"
                +"  //@ public invariant I == 10 && J == 11;\n"

                +"  public TestJava() { \n"
                +"     //@ assert I == 10 && J == 11;\n" // OK because of invariant
                +"     n();\n"
                +"     //@ assert I == 10 && J == 11;\n" // Should be OK because final fields are not modified
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 10 && J == 11;\n" // OK because of invariant
                +"     n();\n"
                +"     //@ assert I == 10 && J == 11;\n" // Should be OK because final fields are not modified
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  static public void n() {}\n"
                
                +"  //@ public normal_behavior ensures \\result == 10;\n"
                +"  static public int z() { return 10; }\n"
                +"}"
                );
    }

    @Test
    public void testIFieldsNotConstantWithHelper() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final int I = z();\n"
                +"  //@ ghost public final int J = 1 + I;\n"
                +"  //@ public invariant I == 10 && J == 11;\n"

                +"  public TestJava() { \n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"     n();\n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"     n();\n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  public void n() {}\n"
                
                +"  //@ private normal_behavior ensures \\result == 10;\n"
                +"  /*@ helper */ static private int z() { return 10; }\n"
                +"}"
                );
    }

   }
