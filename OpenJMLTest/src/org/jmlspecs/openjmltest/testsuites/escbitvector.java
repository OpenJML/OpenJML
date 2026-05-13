package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

//FIXME _ need to test when inline body is in separate file
//FIXME _ need to test when inline body is in separate file that is not parsed on the command-line
// FIXME - need to test when inline is in .jml
// FIXME - need to test when inline is in .jml for a binary class

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escbitvector extends EscBase {

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }

    // auto BV, with precondition
    @Test
    public void testBV2() {
        addOptions("--esc-bv=auto");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires n <= 0x7ffffff0;
                  //@ ensures n <= \\result <= n+15;
                  //@ ensures (\\result&15) == 0;
                  //@ pure
                //@ code_java_math spec_java_math
                  public int m1(int n) {
                    return n + ((-n) & 0x0f);
                  }
                }
                """
                );
    }

    // BV true, with precondition (sometimes times out)
    @Test
    public void testBV2a() {
        addOptions("--esc-bv=true","-solver-seed=42");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires n <= 0x7ffffff0;
                  //@ ensures n <= \\result;
                  //@ ensures \\result <= n+15;
                  //@ ensures (\\result&15) == 0;
                  //@ pure
                //@ code_java_math spec_java_math
                  public int m1(int n) {
                    return n + ((-n) & 0x0f);
                  }
                }
                """
                );
    }

    // BV true, with precondition and modulo operation
    @Test // non-deterministically times out
    public void testBV2b_int() {
        Assume.assumeTrue(runLongTests);
        addOptions("--esc-bv=true");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires n <= 0x7ffffff0;
                  //@ ensures n <= \\result <= n+15;
                  //@ ensures (\\result%16) == 0;
                  //@ pure
                //@ code_java_math spec_java_math
                  public int m1(int n) {
                    return n + ((-n) & 0x0f);
                  }
                }
                """
                );
    }

    // BV true, with precondition and modulo operation
    @Test
    public void testBV2b_short() {
        Assume.assumeTrue(runLongTests);
        addOptions("--esc-bv=true");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires n <= 0x7ff0;
                  //@ ensures n <= \\result <= n+15;
                  //@ ensures (\\result%16) == 0;
                  //@ pure
                //@ code_java_math spec_java_math
                  public int m1(short n) {
                    return n + ((-n) & 0x0f);
                  }
                }
                """
                );
    }

    // default BV, no precondition
    @Test
    public void testBV1() {
        Assume.assumeTrue(runLongTests);
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures n <= \\result <= n+15;
                  //@ ensures (\\result&15) == 0;
                  //@ pure
                //@ code_java_math spec_java_math
                  public int m1(int n) {
                    return n + ((-n) & 0x0f);
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Postcondition) in method m1",5
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }

    // BV off
    @Test
    public void testBV1b() {
        expectedExit = 0;
        addOptions("--esc-bv=false");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires n <= Integer.MAX_VALUE-15;
                  //@ ensures n <= \\result <= n+15;
                  //@ ensures (\\result&15) == 0;
                  //@ pure
                //@ code_java_math spec_java_math
                  public int m1(int n) {
                    return n + ((-n) & 0x0f);
                  }
                }
                """
                );
    }

    // incorrect escBV option
    @Test
    public void testBVe1() {
        addOptions("--esc-bv","--normal"); // Testing incorrect use of -escBV
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires true;
                  //@ code_java_math spec_java_math
                  public int m1(int n) {
                    return 0;
                  }
                }
                """
                ,"warning: Command-line argument error: Expected 'auto', 'true' or 'false' for --esc-bv: --normal",-1
          );
    }

    // incorrect escBV option
    @Test
    public void testBVe2() {
        addOptions("--esc-bv=xx");  // This should cause an error
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires true;
                  //@ code_java_math spec_java_math
                  public int m1(int n) {
                    return 0;
                  }
                }
                """
                ,"warning: Command-line argument error: Expected 'auto', 'true' or 'false' for --esc-bv: xx",-1
         );
    }

    // OK option, with precondition
    @Test
    public void testBVe3() {
        addOptions("--esc-bv=");  // Should revert to auto
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires n <= 0x7ffffff0;
                  //@ ensures n <= \\result <= n+15;
                  //@ ensures (\\result&15) == 0;
                  //@ pure
                //@ code_java_math spec_java_math
                  public int m1(int n) {
                    return n + ((-n) & 0x0f);
                  }
                }
                """
          );
    }

    // another incorrect use of escBV option
    @Test
    public void testBVe4() {
        expectedExit = 0;
        addOptions("--esc-bv");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires n <= 0x7ffffff0;
                  //@ ensures n <= \\result <= n+15;
                  //@ ensures (\\result&15) == 0;
                  //@ pure
                  //@ code_java_math spec_java_math
                  public int m1(int n) {
                    return n + ((-n) & 0x0f);
                  }
                }
                """
                ,"warning: The last command-line option expects a parameter: --esc-bv",-1
          );
    }

    // Simple use of explicit BV auto
    @Test
    public void testBVauto() {
        // This test first tries SMT translation without BV, which fails, and then it tries with, and succeeds.
        expectedExit = 0;
        addOptions("--esc-bv=auto","--method=m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                 class A {
                   //@ requires (i&5) == 1;
                   //@ pure
                   public static boolean mm(int i) { return true; }
                }
                 public class TestJava {
                  //@ requires A.mm(1);
                  public void m1() {
                  }
                }
                """
          );
    }

    // Simple use of explicit BV false
    @Test
    public void testBVauto2() {
        // This test, the same code as above, only tries SMT translation without BV, which fails.
        expectedExit = 1;
        addOptions("--esc-bv=false","--method=m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                 class A {
                   //@ requires (i&5) == 1;
                   //@ pure
                   public static boolean mm(int i) { return true; }
                }
                 public class TestJava {
                  //@ requires A.mm(1);
                  public void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:3: error: This method uses bit-vector operations and must be run with --esc-bv=true (or auto) [Bit-operation BITAND]",19
                ,optional("/tt/TestJava.java:3: error: This method uses bit-vector operations and must be run with --esc-bv=true (or auto) [Bit-operation BITAND]",19)
          );
    }

    // Simple use of explicit BV true
    @Test
    public void testBVauto3() {
        // This test, the same code as above, only tries SMT translation with BV the first time.
        expectedExit = 0;
        addOptions("--esc-bv=true","--method=m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                 class A {
                   //@ requires (i&5) == 1;
                   //@ pure
                   public static boolean mm(int i) { return true; }
                }
                 public class TestJava {
                  //@ requires A.mm(1);
                  public void m1() {
                  }
                }
                """
          );
    }

    // Test using @Options
    @Test
    public void testBVoption() {
        expectedExit = 1;
        addOptions("--esc-bv=false");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int m1(int x) {
                    return x | x;
                  }
                  @org.jmlspecs.annotation.Options("--esc-bv=true")
                  public int m2(int x) {
                    return x | x;
                  }
                }
                """
                ,"/tt/TestJava.java:4: error: This method uses bit-vector operations and must be run with --esc-bv=true (or auto) [Bit-operation BITOR]", 14
          );
    }

    @Test
    public void testBVSwitch() {
        addOptions("--esc-bv=true");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int m1(int x) {
                    return x | x;
                  }
                }
                """
          );

    }

    @Test
    public void testBVSwitch2() {
        addOptions("--esc-bv=auto");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int m1(int x) {
                    return x | x;
                  }
                }
                """
          );

    }
}
