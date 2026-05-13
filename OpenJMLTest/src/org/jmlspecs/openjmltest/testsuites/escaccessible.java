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
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible \\nothing;
                  public void m() {}
                }
                """
                );
    }

    @Test
    public void testConstructor() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public TestJava() {}
                }
                """
                );
    }

    @Test
    public void testConstructor2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible \\nothing;
                  public TestJava() { i = 1; }
                  public int i;
                }
                """
                );
    }

    @Test
    public void testAccessibleNoCheck() {
        addOptions("--no-check-accessible");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible \\nothing;
                  int m() { return i; }
                  int i;
                }
                """
                );
    }

    @Test
    public void testAccessibleDefault() { // Default setting for --check-accessible is on
        addOptions("--check-accessible=");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible \\nothing;
                  int m() { return i; }
                  int i;
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: i",20
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleReturn() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible \\nothing;
                  int m() { return i; }
                  int i;
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: i",20
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleReturn2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible \\nothing;
                  int m() { int i = 0; return i; }
                }
                """
                );
    }

    @Test
    public void testAccessibleReturn3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible i;
                  int m() { return i; }
                  int i;
                }
                """
                );
    }

    @Test
    public void testAccessibleReturn4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible this.i;
                  int m() { return i; }
                  static int i;
                }
                """
                );
    }

    @Test
    public void testAccessibleReturn5() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible j;
                  int m() { return i; }
                  int i,j;
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: i",20
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleFA() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible a,a.i;
                  int m() { return a.i; }
                  int i,j;
                  TestJava a; TestJava() { a = new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAccessibleFA2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible a,a.j;
                  int m() { return a.i; }
                  int i,j;
                  TestJava a; TestJava() { a = new TestJava(); }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: a.i",21
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleFA3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires b == a;
                  //@ accessible b.i,a;
                  int m() { return a.i; }
                  int i,j;
                  TestJava a, b; TestJava() { a = b = new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAccessibleFA4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible a,b.i;
                  int m() { return a.i; }
                  int i,j;
                  TestJava a, b; TestJava() { a = b = new TestJava(); }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: a.i",21
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleAA1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a != null && 0 <= i && i < a.length;
                  //@ accessible a,i,a[*];
                  int m() { return a[i]; }
                  int i,j;
                  int[] a; int[] b; TestJava() { a = b = new int[1]; }
                }
                """
                );
    }

    @Test
    public void testAccessibleAA2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a != null && 0 <= i && i < a.length;
                  //@ accessible \\everything;
                  int m() { return a[i]; }
                  int i,j;
                  int[] a; int[] b; TestJava() { a = b = new int[1]; }
                }
                """
                );
    }

    @Test
    public void testAccessibleAA3() {
        expectedExit = 6;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a != null && 0 <= i && i < a.length;
                  //@ accessible a,i;
                  int m() { return a[i]; }
                  int i,j;
                  int[] a; int[] b; TestJava() { a = b = new int[1]; }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:4:) in method m: a[i]",21
                ,"/tt/TestJava.java:4: verify: Associated declaration: /tt/TestJava.java:5:",7
                );
    }

    @Test
    public void testAccessibleCall1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible i;
                  int m() { return n(); }
                  //@ accessible i;
                  int n() { return i; }
                  int i,j;
                }
                """
                );
    }

    @Test
    public void testAccessibleCall2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible i;
                  int m() { return n(); }

                  int n() { return i; }
                  int i,j;
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: \\everything",21
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleCall3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible i;
                  int m() { return n(); }
                  //@ accessible \\nothing;
                  int n() { return 0; }
                  int i,j;
                }
                """
                );
    }

    @Test
    public void testAccessibleCall4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible i;
                  int m() { return n(); }
                  //@ accessible \\everything;
                  int n() { return 0; }
                  int i,j;
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: \\everything",21
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleThisType() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible \\nothing;
                  boolean m() { return this instanceof TestJava; }
                  int i,j;
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3:) in method m: this",24
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:",7
                );
    }

    @Test
    public void testAccessibleConditional() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires b;
                  //@ accessible i;
                  //@ also requires !b;
                  //@ accessible j;
                  int m(boolean b) { return b ? i : j; }
                  int i,j;
                }
                """
                );
    }

    @Test
    public void testAccessibleConditional2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible i,j;
                  int m(boolean b) { return b ? i : j; }
                  int i,j;
                }
                """
                );
    }

    @Test
    public void testAccessibleConditional3() {
    	//addOptions("-show","-method=m");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires b;
                  //@ accessible i;
                  //@ also requires !b;
                  //@ accessible i;
                  int m(boolean b) { return b ? i : j; }
                  int i,j;
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:6:) in method m: j",37
                ,"/tt/TestJava.java:6: verify: Associated declaration: /tt/TestJava.java:7:",7
                );
    }
}
