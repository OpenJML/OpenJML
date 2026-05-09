package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escaccessible extends EscBase {

    @Before @Override
    public void setUp() throws Exception {
        super.setUp();
        captureOutput = false; // FIXME - why doesn't the 'verification failures' line end up in diagnostics, like it seems the erros and warnings lines do 
        addOptions("--check-accessible");
        addOptions("-no-jmltesting");  // Keeps location information in verify messages
    }

    protected void helpEsc(String classname, String s, Object... expectedResults) {
        if (expectedResults.length > 0) expectedExit = 6;
        super.helpEsc(classname,  s,  expectedResults);
        // FIXME - the verification failures message is not captured
        //org.junit.Assert.assertEquals(output(),expectedResults.length == 0?"":(expectedResults.length/2 + " verification failures\n"));
    }

    @Test
    public void testAccessibleNothing() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  public void m() {}\n"
                +"}"
                );
    }

    @Test
    public void testConstructor() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public TestJava() {}\n"
                +"}"
                );
    }

    @Test
    public void testConstructor2() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  public TestJava() { i = 1; }\n"
                +"  public int i;\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleNoCheck() {
        addOptions("--no-check-accessible");
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  int m() { return i; }\n"
                +"  int i;\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleDefault() { // Default setting for --check-accessible is on
        addOptions("--check-accessible=");
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  int m() { return i; }\n"
                +"  int i;\n"
                +"}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: i",20
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleReturn() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  int m() { return i; }\n"
                +"  int i;\n"
                +"}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: i",20
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleReturn2() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  int m() { int i = 0; return i; }\n" // OK
                +"}"
                );
    }

    @Test
    public void testAccessibleReturn3() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return i; }\n" // OK
                +"  int i;\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleReturn4() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible this.i;\n"
                +"  int m() { return i; }\n" // OK
                +"  static int i;\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleReturn5() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible j;\n"
                +"  int m() { return i; }\n"
                +"  int i,j;\n"
                +"}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: i",20
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleFA() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible a,a.i;\n"
                +"  int m() { return a.i; }\n"
                +"  int i,j;\n"
                +"  TestJava a; TestJava() { a = new TestJava(); } \n"
                +"}"
                );
    }

    @Test
    public void testAccessibleFA2() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible a,a.j;\n"
                +"  int m() { return a.i; }\n"
                +"  int i,j;\n"
                +"  TestJava a; TestJava() { a = new TestJava(); } \n"
                +"}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: a.i",21
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleFA3() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b == a;\n"
                +"  //@ accessible b.i,a;\n"
                +"  int m() { return a.i; }\n"
                +"  int i,j;\n"
                +"  TestJava a, b; TestJava() { a = b = new TestJava(); } \n"
                +"}"
                );
    }

    @Test
    public void testAccessibleFA4() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible a,b.i;\n"
                +"  int m() { return a.i; }\n"
                +"  int i,j;\n"
                +"  TestJava a, b; TestJava() { a = b = new TestJava(); } \n"
                +"}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: a.i",21
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleAA1() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires a != null && 0 <= i && i < a.length;\n"
                +"  //@ accessible a,i,a[*];\n"
                +"  int m() { return a[i]; }\n"
                +"  int i,j;\n"
                +"  int[] a; int[] b; TestJava() { a = b = new int[1]; } \n"
                +"}"
                );
    }

    @Test
    public void testAccessibleAA2() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires a != null && 0 <= i && i < a.length;\n"
                +"  //@ accessible \\everything;\n"
                +"  int m() { return a[i]; }\n"
                +"  int i,j;\n"
                +"  int[] a; int[] b; TestJava() { a = b = new int[1]; } \n"
                +"}"
                );
    }

    @Test
    public void testAccessibleAA3() {
        expectedExit = 6;
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires a != null && 0 <= i && i < a.length;\n"
                +"  //@ accessible a,i;\n"
                +"  int m() { return a[i]; }\n"
                +"  int i,j;\n"
                +"  int[] a; int[] b; TestJava() { a = b = new int[1]; } \n"
                +"}"
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:4:) in method m: a[i]",21
                ,"/tt/TestJava.java:4: verify: Associated declaration: /tt/TestJava.java:5:",7
                );
    }

    @Test
    public void testAccessibleCall1() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return n(); }\n"
                +"  //@ accessible i;\n"
                +"  int n() { return i; }\n"
                +"  int i,j;\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleCall2() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return n(); }\n"  // Should FAIL
                +"  \n"
                +"  int n() { return i; }\n"  // Default accessible is \everything
                +"  int i,j;\n"
                +"}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: \\everything",21
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleCall3() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return n(); }\n"
                +"  //@ accessible \\nothing;\n"
                +"  int n() { return 0; }\n"
                +"  int i,j;\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleCall4() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return n(); }\n"
                +"  //@ accessible \\everything;\n"
                +"  int n() { return 0; }\n"
                +"  int i,j;\n"
                +"}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: \\everything",21
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleThisType() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  boolean m() { return this instanceof TestJava; }\n"
                +"  int i,j;\n"
                +"}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: this",24
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleConditional() {
        helpEsc("tt.TestJava","package tt; \n"
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

    @Test
    public void testAccessibleConditional2() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i,j;\n"
                +"  int m(boolean b) { return b ? i : j; }\n"
                +"  int i,j;\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleConditional3() {
    	//addOptions("-show","-method=m");
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ accessible i;\n"
                +"  //@ also requires !b;\n"
                +"  //@ accessible i;\n"
                +"  int m(boolean b) { return b ? i : j; }\n"
                +"  int i,j;\n"
                +"}"
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:6:) in method m: j",37
                ,"/tt/TestJava.java:6: verify: Associated declaration: /tt/TestJava.java:7:",7
                );
    }
}
