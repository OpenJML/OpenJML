package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escConstantFields extends EscBase {

    @Test
    public void testBasic() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public final static int I = 1;
                  public final static int J = 1 + I;
                  //@ ensures J == 2;
                  public TestJava() {  }
                  //@ ensures J == 2;
                  public void m() {}
                  //@ ensures J == 2;
                  static public void n() {}
                }
                """
                );
    }

    @Test
    public void testGhost() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ghost public final static int I = 1;
                  //@ ghost public final static int J = 1 + I;
                  //@ ensures J == 2;
                  public TestJava() {  }
                  //@ ensures J == 2;
                  public void m() {}
                  //@ ensures J == 2;
                  static public void n() {}
                }
                """
                );
    }

    @Test
    public void testFields() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public final static int I = 1;
                  //@ ghost public final static int J = 1 + I;
                  public TestJava() {
                     //@ assert I == 1 && J == 2;
                     n();
                     //@ assert I == 1 && J == 2;
                  }
                  public void m() {
                     //@ assert I == 1 && J == 2;
                     n();
                     //@ assert I == 1 && J == 2;
                  }
                  //@ assignable \\everything;
                  static public void n() {}
                }
                """
                );
    }

    @Test
    public void testFieldsNotFinal() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int I = 1;
                  //@ ghost public static int J = 1 + I;
                  //@ public static invariant I == 1 && J == 2;
                  public TestJava() {
                     //@ assert I == 1 && J == 2;
                     n();
                     //@ assert I == 1 && J == 2;
                  }
                  //@ ensures J == 2;
                  public void m() {
                     //@ assert I == 1 && J == 2;
                     n();
                     //@ assert I == 1 && J == 2;
                  }
                  //@ assignable \\everything;
                  static public void n() {}
                }
                """
                );
    }

    @Test
    public void testFieldsNotConstant() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public final static int I = z();
                  //@ ghost public final static int J = 1 + I;
                  //@ public static invariant I == 10 && J == 11;
                  public TestJava() {
                     //@ assert I == 10 && J == 11;
                     n();
                     //@ assert I == 10 && J == 11;
                  }
                  public void m() {
                     //@ assert I == 10 && J == 11;
                     n();
                     //@ assert I == 10 && J == 11;
                  }
                  //@ assignable \\everything;
                  static public void n() {}
                  //@ ensures \\result == 10;
                  //@ pure
                  static public int z() { return 10; }
                }
                """
                // z() is not a helper, so it asserts the static invariant as a precondition, which does not yet hold
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (InvariantEntrance: /tt/TestJava.java:5:) in method <clinit>: (Caller: tt.TestJava.<clinit>(), Callee: tt.TestJava.z())",32
                ,"/tt/TestJava.java:5: verify: Associated declaration: /tt/TestJava.java:3:",21
                );
    }

    @Test
    public void testFieldsNotConstantNoInvariant() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public final static int I = z();
                  //@ ghost public final static int J = 1 + z();
                  public TestJava() {
                     //@ assert I == 10 && J == 11;
                  }
                  public void m() {
                     //@ assert I == 10 && J == 11;
                  }
                  //@ assignable \\everything;
                  static public void n() {}
                  //@ ensures \\result == 10;
                  //@ pure
                  static public int z() { return 10; }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method TestJava",10
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test
    public void testFieldsNotConstantWithHelper() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public final static int I = z();
                  //@ ghost public final static int J = 1 + I;
                  //@ public static invariant I == 10 && J == 11;
                  public TestJava() {
                     //@ assert I == 10 && J == 11;
                     n();
                     //@ assert I == 10 && J == 11;
                  }
                  public void m() {
                     //@ assert I == 10 && J == 11;
                     n();
                     //@ assert I == 10 && J == 11;
                  }
                  //@ assignable \\everything;
                  static public void n() {}
                  /*@ pure helper */ static private int z() { return 10; }
                }
                """
                // z() is pure with no specification: its result is unknown, and it may throw
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method <clinit>: overflow in int sum",43
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (ExceptionInInitializer) in method <clinit>",32
                ,"/tt/TestJava.java:2: verify: The prover cannot establish an assertion (InvariantExit: /tt/TestJava.java:5:) in method <clinit>",8
                ,"/tt/TestJava.java:5: verify: Associated declaration: /tt/TestJava.java:2:",21
                );
    }

    @Test
    public void testFieldsNotConstantWithHelperB() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public final static int I = z();
                  //@ ghost public final static int J = 1 + I;
                  //@ public static invariant I == 10 && J == 11;
                  public TestJava() {
                     //@ assert I == 10 && J == 11;
                     n();
                     //@ assert I == 10 && J == 11;
                  }
                  public void m() {
                     //@ assert I == 10 && J == 11;
                     n();
                     //@ assert I == 10 && J == 11;
                  }
                  //@ assignable \\everything;
                  static public void n() {}
                  //@ private normal_behavior ensures \\result == 10;
                  /*@ pure helper */ static private int z() { return 10; }
                }
                """
                );
    }

    // z() may throw (it is not normal_behavior), and static initialization must not throw (#1152)
    @Test
    public void testFieldsNotConstantWithHelperC() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public final static int I = z();
                  //@ ghost public final static int J = 1 + I;
                  //@ public static invariant I == 10 && J == 11;
                  public TestJava() {
                     //@ assert I == 10 && J == 11;
                     n();
                     //@ assert I == 10 && J == 11;
                  }
                  public void m() {
                     //@ assert I == 10 && J == 11;
                     n();
                     //@ assert I == 10 && J == 11;
                  }
                  //@ assignable \\everything;
                  static public void n() {}
                  //@ ensures \\result == 10;
                  /*@ pure helper */ static private int z() { return 10; }
                }
                """
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (ExceptionInInitializer) in method <clinit>",32
                );
    }

    @Test
    public void testIFields() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public final int I = 1;
                  //@ ghost public final int J = 1 + I;
                  public TestJava() {
                     //@ assert I == 1 && J == 2;
                     n();
                     //@ assert I == 1 && J == 2;
                  }
                  public void m() {
                     //@ assert I == 1 && J == 2;
                     n();
                     //@ assert I == 1 && J == 2;
                  }
                  //@ assignable \\everything;
                  public void n() {}
                }
                """
                );
    }

    @Test
    public void testIFieldsS() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public final int I = 1;
                  //@ ghost public final int J = 1 + I;
                  public TestJava() {
                     //@ assert I == 1 && J == 2;
                     n();
                     //@ assert I == 1 && J == 2;
                  }
                  public void m() {
                     //@ assert I == 1 && J == 2;
                     n();
                     //@ assert I == 1 && J == 2;
                  }
                  //@ assignable \\everything;
                  static public void n() {}
                }
                """
                );
    }

    @Test
    public void testIFieldsNotFinal() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int I = 1;
                  //@ ghost public int J = 1 + I;
                  //@ public invariant I == 1 && J == 2;
                  public TestJava() {
                     //@ assert I == 1 && J == 2;
                     n();
                     //@ assert I == 1 && J == 2;
                  }
                  public void m() {
                     //@ assert I == 1 && J == 2;
                     n();
                     //@ assert I == 1 && J == 2;
                  }
                  //@ assignable \\everything;
                  public void n() {}
                }
                """
                );
    }

    @Test
    public void testIFieldsNotFinalS() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int I = 1;
                  //@ ghost public int J = 1 + I;
                  //@ public invariant I == 1 && J == 2;
                  public TestJava() {
                     //@ assert I == 1 && J == 2;
                     n();
                     //@ assert I == 1 && J == 2;
                  }
                  public void m() {
                     //@ assert I == 1 && J == 2;
                     n();
                     //@ assert I == 1 && J == 2;
                  }
                  //@ public normal_behavior
                  //@   assignable \\everything;
                  static public void n() {}
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method TestJava",10
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test
    public void testIFieldsNotConstant() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public final int I = z();
                  //@ ghost public final int J = 1 + I;
                  //@ public invariant I == 10 && J == 11;
                  public TestJava() {
                     //@ assert I == 10 && J == 11;
                     n();
                     //@ assert I == 10 && J == 11;
                  }
                  public void m() {
                     //@ assert I == 10 && J == 11;
                     n();
                     //@ assert I == 10 && J == 11;
                  }
                  //@ assignable \\everything;
                  public void n() {}
                  //@ public normal_behavior
                  //@   ensures \\result == 10;
                  static public int z() { return 10; }
                }
                """
                );
    }

    @Test
    public void testIFieldsNotConstantS() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public final int I = z();
                  //@ ghost public final int J = 1 + I;
                  //@ public invariant I == 10 && J == 11;
                  public TestJava() {
                     //@ assert I == 10 && J == 11;
                     n();
                     //@ assert I == 10 && J == 11;
                  }
                  public void m() {
                     //@ assert I == 10 && J == 11;
                     n();
                     //@ assert I == 10 && J == 11;
                  }
                  //@ assignable \\everything;
                  static public void n() {}
                  //@ public normal_behavior
                  //@   ensures \\result == 10;
                  static public int z() { return 10; }
                }
                """
                );
    }

    @Test
    public void testIFieldsNotConstantWithHelper() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public final int I = z();
                  //@ ghost public final int J = 1 + I;
                  //@ public invariant I == 10 && J == 11;
                  public TestJava() {
                     //@ assert I == 10 && J == 11;
                     n();
                     //@ assert I == 10 && J == 11;
                  }
                  public void m() {
                     //@ assert I == 10 && J == 11;
                     n();
                     //@ assert I == 10 && J == 11;
                  }
                  //@ assignable \\everything;
                  public void n() {}
                  //@ private normal_behavior
                  //@   ensures \\result == 10;
                  /*@ helper */ static private int z() { return 10; }
                }
                """
                );
    }

    @Test // initialized static final in another class, no invariants
    public void testConstants() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 class H {
                   final public static int CON1 = 50;
                   final public static int CON2 = 1 + CON1;
                   final public static int CON3 = Integer.MAX_VALUE;
                 }
                public class TestJava {
                  public TestJava() {
                    //@ assert H.CON1 == 50 ;
                    //@ assert H.CON2 == 51 ;
                    //@ assert H.CON2 == H.CON1 + 1 ;
                    //@ assert H.CON3 == 0x7fffffff ;
                    meverything();
                    //@ assert H.CON1 == 50 ;
                    //@ assert H.CON2 == 51 ;
                    //@ assert H.CON2 == H.CON1 + 1 ;
                    //@ assert H.CON3 == 0x7fffffff ;
                  }
                  public void m1() {
                    //@ assert H.CON1 == 50 ;
                    //@ assert H.CON2 == 51 ;
                    //@ assert H.CON2 == H.CON1 + 1 ;
                    //@ assert H.CON3 == 0x7fffffff ;
                    meverything();
                    //@ assert H.CON1 == 50 ;
                    //@ assert H.CON2 == 51 ;
                    //@ assert H.CON2 == H.CON1 + 1 ;
                    //@ assert H.CON3 == 0x7fffffff ;
                  }
                  //@ assignable \\everything;
                  public void meverything() {
                  }
                }
                """
                );
    }

    // #1122: a non-constant static final field, with the (now removed) static-init warning on and --jmlverbose, crashed
    @Test
    public void testFieldNotConstantVerboseWarning() {
        main.addOptions("--jmlverbose");
        // Discard the verbose tracing; only the diagnostics are checked
        var discard = new java.io.PrintStream(java.io.OutputStream.nullOutputStream());
        com.sun.tools.javac.util.Log.instance(context).setWriters(new java.io.PrintWriter(discard, true));
        main.progressListener = new org.jmlspecs.openjml.Main.PrintProgressReporter(new java.io.PrintWriter(discard, true));
        org.jmlspecs.openjml.Utils.setDebugOut(discard);
        try {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public final static int I = z();
                  public void m() {
                     //@ assert I == 10;
                  }
                  //@ ensures \\result == 10;
                  //@ pure
                  static public int z() { return 10; }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m",10
                );
        } finally {
            org.jmlspecs.openjml.Utils.setDebugOut(null);
        }
    }
}
