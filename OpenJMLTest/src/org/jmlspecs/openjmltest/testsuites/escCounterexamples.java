package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjml.JmlOption;

import java.util.ArrayList;
import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

// FIXME - there is nothing checking that these give correct results

/** Tests emitting counterexample information and tracing, though the text
 * of the output is not actually checked - needs visual observation.
 * @author David Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escCounterexamples extends EscBase {

    @Override
    public void setUp() throws Exception {
        captureOutput = true;
        checkOutput = false; // Ignore counterexample output for now
        //noCollectDiagnostics = true;
        super.setUp();
        addOptions("--trace","--counterexample");
        addOptions("--code-math=java");
    }

    /** Tests an explicit assertion */
    @Test
    public void testCE1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires k > 0;
                  public void m1(int k) {
                    //@ assert k == 0;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m1",9
                );
    }

    /** Tests a postcondition */
    @Test
    public void testCE2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires k > 0;
                  //@ ensures \\result < 0;
                  public int m1(int k) {
                    return k;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method m1",5
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                );
    }

    /** Tests a called precondition and method and constructor arguments */
    @Test
    public void testCE3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public TestJava(int i) {}

                  //@ measured_by k;
                  public void m1(int k) {
                    c1(k,k!=0);
                    TestJava j = new TestJava(2+3);
                    (k==0?this:j).m1(0);
                  }

                  //@ requires k == 0;
                  public void c1(int k, boolean b) {};
                }
                """
                ,anyorder(
                 seq("/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Precondition) in method m1",7
                    ,"/tt/TestJava.java:13: verify: Associated declaration",15)
                ,seq("/tt/TestJava.java:12: verify: Precondition conjunct is false: k == 0",18
                    ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (TerminationDecreases) in method m1", 19
                    ,"/tt/TestJava.java:9: verify: Associated declaration", 21)
                )
                );
    }

    /** Tests assignments */
    @Test
    public void testCE4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int j; static public int sj; static public TestJava t;
                  public TestJava(int i) {}
                
                  //@ requires t != null; requires \\elemtype(\\typeof(c)) == \\type(Object);
                  public void m1(Object[] c) {
                    int k; boolean b;
                    //@ assume c != null && c.length == 10;
                    k = 8;
                    k += 8;
                    k += (j+=7);
                    b = k > 8;
                    c[4] = t;
                    c[0] = c[3];
                    t.j = 9;
                    t.sj = 10;
                    TestJava.sj = 11;
                    //@ assert false;
                  }
                }
                """
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (Assert) in method m1",9
                );
    }

    /** Tests if statements */
    @Test
    public void testCE5() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int j; static public int sj; static public TestJava t;
                  public TestJava(int i) {}
                  //@ requires j == 0;
                  public void m1(int j) {
                    if (j==0) j=1;
                    if (j == 2) j=7;
                    if (j == 3) j=6;
                    else if (j==4) j=7;
                    else if (j==1) j=10;
                    else j=80;
                    //@ assert false;
                  }
                }
                """
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assert) in method m1",9
                );
    }

    /** Tests loops */
    @Test
    public void testCE6() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires j > 0;
                  public void m1(int j) {
                    int n = 0;
                    //@ loop_invariant 0<=i && i <=j;
                    //@ loop_invariant n == i;
                    for (int i=0; i<j; i++) {
                        n = n+1;
                        //@ assert n != 20;
                    }
                  }
                  //@ requires j > 0;
                  public void m2(int j) {
                    int n = 0;
                    //@ loop_invariant 0<=i && i <=j;
                    //@ loop_invariant n == i;
                    for (int i=0; i<j; i++) {
                        n = n+1;
                    }
                    //@ assert n == -10;
                  }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m1",13
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Assert) in method m2",9
                );
    }

    /** Tests pure methods */
    @Test
    public void testCE7() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1() {
                      //@ assert c(2) != -2; // ERROR - c(2) can be any negative number
                  }
                  public void m2() {
                      //@ assert cc(2) != -3; // OK - we know cc(2) is -2
                  }
                  public void m3() {
                      //@ assert b(); // ERROR - b() can be anything
                  }
                  public void m4() {
                      //@ assert bb(0); // ERROR - bb(0) ncan be anything - is this any different from m3?
                  }
                  //@ normal_behavior requires z > 0; ensures \\result < 0;
                  /*@ pure */ public int c(int z) {
                      return -z;
                  }
                  //@ public normal_behavior requires z > 0; ensures \\result == -z;
                  /*@ pure */ public int cc(int z) {
                      return -z;
                  }
                  //@ normal_behavior requires true;
                  /*@ pure */ static public boolean b() {
                      return true;
                  }
                  //@ normal_behavior requires true;
                  /*@ pure */ static public boolean bb(int z) {
                      return true;
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m1",11
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m3",11
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assert) in method m4",11
                );
    }

    /** Tests alternate returns */
    @Test
    public void testCE8() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i>=0; ensures \\result==0;
                  public int m1(int i) {
                      if (i==0) return 0;
                      if (i==1) return i+20;
                      if (i==2) return 0;
                      if (i==3) return 0;
                      return 0;
                  }
                  static public int k;
                  //@ requires i>=0; ensures k == 0;
                  public void m2(int i) {
                      k = 0;
                      if (i==0) return ;
                      if (i==1) return ;
                      if (i==2) { k = 1; return ;}
                      if (i==3) return ;
                      return ;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method m1",17
                ,"/tt/TestJava.java:3: verify: Associated declaration",22
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Postcondition) in method m2",26
                ,"/tt/TestJava.java:12: verify: Associated declaration",22
                );
    }

    /** Tests switch statements */
    @Test
    public void testCE9() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i>=0; ensures \\result==0;
                  public int m1(int i) {
                      int r = 0;
                      switch (i+5) {
                        case 3: r = 0; break;
                        case 5: r = 4; break;
                        case 7: r = 0; break;
                      }
                      return r;
                  }
                  //@ requires i>=0; ensures \\result==0;
                  public int m2(int i) {
                      int r = 0;
                      switch (i+5) {
                        case 3: r = 0; break;
                        case 5: r = 4; break;
                        case 7: r = 0; break;
                        default: r = 0; break;
                      }
                      return r;
                  }
                }
                """
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Postcondition) in method m1",7
                ,"/tt/TestJava.java:3: verify: Associated declaration",22
                ,"/tt/TestJava.java:22: verify: The prover cannot establish an assertion (Postcondition) in method m2",7
                ,"/tt/TestJava.java:13: verify: Associated declaration",22
                );
    }


    /** Tests called method return */
    @Test
    public void testCE10() {
        main.addOptions(JmlOption.ESC_MAX_WARNINGS.optionName() + "=1");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ public normal_behavior requires i>=0; ensures k==0;
                  public void m1(int i) {
                      cc(i);
                  }
                  //@ requires i>=0; ensures k==1;
                  public void m2(int i) {
                      cc(i);
                  }
                  public int k;
                  //@ requires i>0;
                  //@ ensures k==0;
                  //@ signals (Exception e) false;
                  //@ also requires i==0;
                  //@ ensures false;
                  //@ signals (RuntimeException e) k==1;
                  //@ signals_only RuntimeException;
                  public void cc(int i) throws RuntimeException {
                      k=1; if (i==0) throw new RuntimeException();
                      k=0; return ;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1",9
                ,"/tt/TestJava.java:3: verify: Associated declaration",14
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Postcondition) in method m2",15
                ,"/tt/TestJava.java:7: verify: Associated declaration",22
                );
    }

    /** Tests method calls in expressions */
    @Test
    public void testCE11() {
        main.addOptions("-code-math=math");  // FIXME - bigint?
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1(int i) {
                      int k = c(i) + c(i-15);
                      //@ assert k != 9;
                  }
                  //@ signals (Exception) false;
                  public void m2(int i) {
                      int k = c(i);
                      //@ assert true;
                  }
                  //@ ensures \\result == i+10;
                  public int c(int i) throws RuntimeException {
                    return i+10;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m1",11
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m2",16
                ,"/tt/TestJava.java:7: verify: Associated declaration",7
                );
    }

    // FIXME - synchronized is not translated or reported in tracing
    /** Tests misc statements: synchronized, block */
    @Test
    public void testCE12() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1(int i) {
                      int k= 0;
                      synchronized (this) {k=1;}
                      { k = 2; k = 3+k;}
                      //@ assert false;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m1",11
                );
    }

    /** Tests initializations */
    @Test
    public void testCE13() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1(int i) {
                      int k = 0;
                      int[] a = {1,2,3,4};
                      int[][] b = new int[2][3];
                      int[][] c = new int[2][];
                      int[][] d = new int[][]{{1},{2,3}};
                      //@ assert false;
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m1",11
                );
    }

    /** Tests JML statements */
    @Test
    public void testCE14() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  int k = 98; public Object o;
                  public void m1(int i) {
                      //@ assume k == 98;
                      //@ ghost int kk = 0;
                      //@ set kk = 5;
                      //
                      k = 65;
                      //@ set kk = \\old(k) - k;
                      //@ assume (k==k) && (\\lblpos X (k == 65));
                      //@ assume o!= null && \\typeof(o) <:= \\type(Object);
                      //@ unreachable;
                  }
                   public TestJava() { o = new Object(); }
                }
                """
                ,"/tt/TestJava.java:11: verify: Label X has value true",37
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Unreachable) in method m1",11
                );
    }

    /** Tests try/catch/finally */
    @Test
    public void testCE15() {
        main.addOptions(JmlOption.ESC_MAX_WARNINGS.optionName()+"=1");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {

                  //@ ensures false;
                  public void m1(int i) {
                    int k = 9 - 9;
                    try {
                      k = 1 + 2 + 3 - 1;
                      try {
                         k = 7;
                         return;
                      } finally {
                         k = 9;
                      }
                    } finally {
                       k = 13;
                       return;
                    }
                  }

                  //@ requires i != 0; ensures false; //Line 19
                  public void m2(int i) throws Exception {
                    int k = 0;
                    try {
                      k = 5;
                      try {
                         k = 7;
                         if (i==0) throw new RuntimeException();
                         return;
                      } catch (Exception e) {
                         k = 25;
                         throw e;
                      } finally {
                         k = 9;
                      }
                    } catch (RuntimeException e) {
                       k = 27;
                    } finally {
                       k = 13;
                    }
                  }

                  //@ requires i == 0; ensures false; // Line 40
                  public void m3(int i) throws Exception {
                    int k = 0;
                    try {
                      k = 5;
                      try {
                         k = 7;
                         if (i==0) throw new RuntimeException();
                         return;
                      } catch (Exception e) {
                         k = 25;
                         throw e;
                      } finally {
                         k = 9;
                      }
                    } catch (RuntimeException e) {
                       k = 27;
                    } finally {
                       k = 13;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Postcondition) in method m1",8
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                ,"/tt/TestJava.java:29: verify: The prover cannot establish an assertion (Postcondition) in method m2",10
                ,"/tt/TestJava.java:21: verify: Associated declaration",24
                ,"/tt/TestJava.java:54: verify: The prover cannot establish an assertion (Postcondition) in method m3",10
                ,"/tt/TestJava.java:43: verify: Associated declaration",24
                );
    }

    /** Tests try/catch/finally */
    @Test
    public void testCE16() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures \\result != 10;
                  public int m1(int i) {
                    int k = i + 2 - 1;
                    return k + 5;
                    }
                  }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method m1",5
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }
}
