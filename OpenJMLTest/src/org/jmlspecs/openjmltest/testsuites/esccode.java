package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class esccode extends EscBase {

    @Test
    public void testCode1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends A {
                  //@ also public normal_behavior
                  //@    ensures \\result > 0;
                  public int m() {
                    return 5;
                  }
                }
                 class A {
                  //@ public normal_behavior
                  //@    ensures \\result > 10;
                  public int m() {
                    return 20;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method m",5
                ,"/tt/TestJava.java:11: verify: Associated declaration",10
                );
    }

    @Test
    public void testCode2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends A {
                  //@ also public normal_behavior
                  //@    ensures \\result > 0;
                  public int m() {
                    return 5;
                  }
                }
                 class A {
                  //@ public code normal_behavior
                  //@    ensures \\result > 10;
                  public int m() {
                    return 20;
                  }
                }
                """
                );
    }

    @Test
    public void testCode3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends A {
                  //@ also public normal_behavior
                  //@    ensures \\result > 0;
                  public int m() {
                    return 0;
                  }
                }
                 class A {
                  //@ public code normal_behavior
                  //@    ensures \\result > 10;
                  public int m() {
                    return 20;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method m",5
                ,"/tt/TestJava.java:4: verify: Associated declaration",10
                );
    }

    @Test
    public void testCode4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends A {
                  //@ also public code normal_behavior
                  //@    ensures \\result > 0;
                  public int m() {
                    return 0;
                  }
                }
                 class A {
                  //@ public code normal_behavior
                  //@    ensures \\result > 10;
                  public int m() {
                    return 20;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method m",5
                ,"/tt/TestJava.java:4: verify: Associated declaration",10
                );
    }

    @Test
    public void testCode5() {
        main.addOptions("--method=n"); // This is part of the test, not debugging
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends A {
                  //@ public code normal_behavior
                  //@    ensures \\result > 10;
                  public int n() {
                    return m();
                  }
                  //@ also public code normal_behavior
                  //@    ensures true;
                  public int m() {
                    return 0;
                  }
                }
                 class A {
                  //@ public code normal_behavior
                  //@    ensures \\result > 10;
                  public int m() {
                    return 20;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method n",5
                ,"/tt/TestJava.java:4: verify: Associated declaration",10
                );
    }

    @Test
    public void testCode6() {
        main.addOptions("--method=n"); // This is part of the test, not debugging
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends A {
                  //@ public code normal_behavior
                  //@    ensures \\result > 10;
                  public int n() {
                    return m();
                  }
                  public int m() {
                    return 0;
                  }
                }
                 class A {
                  //@ public normal_behavior
                  //@    ensures \\result > 10;
                  public int m() {
                    return 20;
                  }
                }
                """
                );
    }


    @Test
    public void testCode7() {
        main.addOptions("--method=n"); // This is part of the test, not debugging
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends A {
                  //@ public code normal_behavior
                  //@    ensures \\result >= 10;
                  public int n() {
                    return m();
                  }
                  //@ also public code normal_behavior
                  //@    ensures \\result >= 10;
                  public int m() {
                    return 0;
                  }
                }
                 class A {
                  //@ public code normal_behavior
                  //@    ensures true;
                  public int m() {
                    return 20;
                  }
                }
                """
                );
    }

    @Test
    public void testCode8() {
        main.addOptions("--method=n"); // This is part of the test, not debugging
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends A {
                  //@ public code normal_behavior
                  //@    ensures \\result >= 10;
                  public int n() {
                    return m();
                  }
                  //@ also public normal_behavior
                  //@    ensures \\result >= 10;
                  public int m() {
                    return 0;
                  }
                }
                 class A {
                  //@ public code normal_behavior
                  //@    ensures true;
                  public int m() {
                    return 20;
                  }
                }
                """
                );
    }
    

    @Test
    public void testCode9() {
        main.addOptions("--method=n"); // This is part of the test, not debugging
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends A {
                  //@ public code normal_behavior
                  //@    ensures \\result > 10;
                  public int n() {
                    return m();
                  }
                }
                 class A {
                  //@ public code normal_behavior
                  //@    ensures \\result > 10;
                  public int m() {
                    return 20;
                  }
                }
                """
                );
    }
}
