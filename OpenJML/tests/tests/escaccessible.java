package tests;

import java.util.Collection;

import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class escaccessible extends EscBase {

    public escaccessible(String option, String solver) {
        super(option,solver);
    }
    
    @Test @Ignore
    public void testBasic() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  public void m() {}\n"
                +"}"
                );
    }

    @Test @Ignore
    public void testConstructor() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public TestJava() {}\n"
                +"}"
                );
    }

    @Test @Ignore
    public void testConstructor2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible this.*;\n"
                +"  public TestJava() { i = 1; }\n"
                +"  public int i;\n"
                +"}"
                );
    }

    @Test @Ignore
    public void testAccessibleReturn() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  int m() { return i; }\n"
                +"  int i;\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Accessible) in method m",20
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

    @Test @Ignore
    public void testAccessibleReturn2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  int m() { int i = 0; return i; }\n" // OK
                +"}"
                );
    }

    @Test @Ignore
    public void testAccessibleReturn3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return i; }\n" // OK
                +"  int i;\n"
                +"}"
                );
    }

    @Test @Ignore
    public void testAccessibleReturn4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible this.i;\n"
                +"  int m() { return i; }\n" // OK
                +"  static int i;\n"
                +"}"
                );
    }

    @Test @Ignore
    public void testAccessibleReturn5() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible j;\n"
                +"  int m() { return i; }\n"
                +"  int i,j;\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Accessible) in method m",20
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

    @Test @Ignore
    public void testAccessibleFA() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible a,a.i;\n"
                +"  int m() { return a.i; }\n"
                +"  int i,j;\n"
                +"  TestJava a;\n"
                +"}"
                );
    }

    @Test @Ignore
    public void testAccessibleFA2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible a,a.j;\n"
                +"  int m() { return a.i; }\n"
                +"  int i,j;\n"
                +"  TestJava a;\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Accessible) in method m",21
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

    @Test @Ignore
    public void testAccessibleFA3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b == a;\n"
                +"  //@ accessible b.i,a;\n"
                +"  int m() { return a.i; }\n"
                +"  int i,j;\n"
                +"  TestJava a,b;\n"
                +"}"
                );
    }

    @Test @Ignore
    public void testAccessibleFA4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible a,b.i;\n"
                +"  int m() { return a.i; }\n"
                +"  int i,j;\n"
                +"  TestJava a,b;\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Accessible) in method m",21
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

    @Test @Ignore
    public void testAccessibleAA1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires a != null && 0 <= i && i < a.length;\n"
                +"  //@ accessible a,i,a[*];\n"
                +"  int m() { return a[i]; }\n"
                +"  int i,j;\n"
                +"  int[] a; int[] b;\n"
                +"}"
                );
    }

    @Test @Ignore
    public void testAccessibleAA2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires a != null && 0 <= i && i < a.length;\n"
                +"  //@ accessible \\everything;\n"
                +"  int m() { return a[i]; }\n"
                +"  int i,j;\n"
                +"  int[] a; int[] b;\n"
                +"}"
                );
    }

    @Test @Ignore
    public void testAccessibleAA3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires a != null && 0 <= i && i < a.length;\n"
                +"  //@ accessible a,i;\n"
                +"  int m() { return a[i]; }\n"
                +"  int i,j;\n"
                +"  int[] a; int[] b;\n"
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Accessible) in method m",21
                ,"/tt/TestJava.java:4: warning: Associated declaration: /tt/TestJava.java:5: ",7
                );
    }

    @Test @Ignore
    public void testAccessibleCall1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return n(); }\n"
                +"  //@ accessible i;\n"
                +"  int n() { return i; }\n"
                +"  int i,j;\n"
                +"}"
                );
    }

    @Test @Ignore
    public void testAccessibleCall2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return n(); }\n"
                +"  \n"
                +"  int n() { return i; }\n"
                +"  int i,j;\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Accessible) in method m",21
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

    @Test @Ignore
    public void testAccessibleCall3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return n(); }\n"
                +"  //@ accessible \\nothing;\n"
                +"  int n() { return 0; }\n"
                +"  int i,j;\n"
                +"}"
                );
    }

    @Test @Ignore
    public void testAccessibleCall4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return n(); }\n"
                +"  //@ accessible \\everything;\n"
                +"  int n() { return 0; }\n"
                +"  int i,j;\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Accessible) in method m",21
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

    @Test @Ignore
    public void testAccessibleThisType() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  boolean m() { return this instanceof TestJava; }\n"
                +"  int i,j;\n"
                +"}"
                );
    }

    @Test @Ignore
    public void testAccessibleConditional() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ accessible i;\n"
                +"  //@ also requires !b;\n"
                +"  //@ accessible j;\n"
                +"  int m(boolean b) { return b ? i : j; }\n"
                +"  int i,j;\n"
                +"}"
                );
    }

    @Test @Ignore
    public void testAccessibleConditional2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i,j;\n"
                +"  int m(boolean b) { return b ? i : j; }\n"
                +"  int i,j;\n"
                +"}"
                );
    }

    @Test @Ignore
    public void testAccessibleConditional3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ accessible i;\n"
                +"  //@ also requires !b;\n"
                +"  //@ accessible i;\n"
                +"  int m(boolean b) { return b ? i : j; }\n"
                +"  int i,j;\n"
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Accessible) in method m",37
                ,"/tt/TestJava.java:6: warning: Associated declaration: /tt/TestJava.java:7: ",7
                );
    }



}
