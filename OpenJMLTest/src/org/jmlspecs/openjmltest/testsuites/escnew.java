package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escnew extends EscBase {

    @Test
    public void testPrecondition1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {

                  public void m1bad(int i) {
                    //@ assert i>0 ;
                  }
                  //@ requires i>=0;
                  public void m2bad(int i) {
                    //@ assert i>0 ;
                  }
                  //@ requires i>0;
                  public void m1good(int i) {
                    //@ assert i>0 ;
                  }
                  //@ requires i>0;
                  public void m2good(int i) {
                    //@ assert i>=0 ;
                  }
                  //@ requires i>0;
                  //@ also
                  //@ requires i==0;
                  public void m3good(int i) {
                    //@ assert i>=0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m2bad",9
                );
    }

    @Test
    public void testPrecondition1a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {

                  public void m1bad(int i) {
                    //@ assert i>0 ;
                  }
                  //@ requires i>=0;
                  public void m2bad(int i) {
                    //@ assert i>0 ;
                  }
                  //@ requires i>0;
                  public void m1good(int i) {
                    //@ assert i>0 ;
                  }
                  //@ requires i>0;
                  public void m2good(int i) {
                    //@ assert i>=0 ;
                  }
                  //@ requires i>0;
                  //@ also
                  //@ requires i==0;
                  public void m3good(int i) {
                    //@ assert i>=0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m2bad",9
                );
    }


    @Test
    public void testPrecondition2() {
    	addOptions("--check-feasibility=precondition");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i>0;
                  //@ ensures false;
                  public void m1a(int i) {
                  }
                  //@ requires i>0;
                  //@ requires i<0;
                  //@ ensures false;
                  public void m1b(int i) {
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Postcondition) in method m1a",15
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                ,"/tt/TestJava.java:10: verify: Invariants+Preconditions appear to be contradictory in method tt.TestJava.m1b(int)",15
                );
    }

    @Test
    public void testPrecondition3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i >= 0 && a[i]>0;
                  public void m1bad(int[] a, int i) {
                  }
                  //@ requires i < a.length && a[i]>0;
                  public void m2bad(int[] a, int i) {
                  }
                  //@ requires i >= 0 && i < a.length;
                  //@ requires a[i]>0;
                  public void m1good(int[] a, int i) {
                  }
                }
                """
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m1bad",27
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m2bad",33
                );
    }

    @Test
    public void testPrecondition3a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a.length > 10 && i < 5 && a[i]>0 ;
                  public void m1bad(int[] a, int i) {
                  }
                  //@ requires i >= 0 && i < a.length;
                  //@ requires a[i]>0;
                  public void m1good(int[] a, int i) {
                  }
                }
                """
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m1bad",43
                );
    }

    @Test
    public void testPostcondition1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ signals (Exception) false;
                  public void m1bad(int[] a, int i) throws RuntimeException {
                    throw new RuntimeException();
                  }
                  //@ ensures false;
                  public void m2bad(int[] a, int i) {
                  }
                  //@ ensures false;
                  public void m3bad(int[] a, int i) {
                     return;
                  }
                  //@ ensures true;
                  //@ signals (Exception e)  false;
                  public void m1good(int[] a, int i) {
                  }
                  //@ ensures false;
                  public void m2good(int[] a, int i) throws RuntimeException {
                    throw new RuntimeException();
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",5
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Postcondition) in method m2bad",15
                ,"/tt/TestJava.java:7: verify: Associated declaration",7
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Postcondition) in method m3bad",6
                ,"/tt/TestJava.java:10: verify: Associated declaration",7
                );
    }

    @Test
    public void testPostcondition2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 0;
                  //@ ensures false;
                  //@ also
                  //@ requires i!= 0;
                  //@ ensures true;
                  public void m1bad(int[] a, int i) {
                      if (i == 0)
                         return;
                      else
                         return;
                  }
                  //@ requires i == 0;
                  //@ ensures true;
                  //@ also
                  //@ requires i!= 0;
                  //@ ensures false;
                  public void m2bad(int[] a, int i) {
                      if (i == 0)
                         return;
                      else
                         return;
                  }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",10
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Postcondition) in method m2bad",10
                ,"/tt/TestJava.java:18: verify: Associated declaration",7
                );
    }

    @Test
    public void testPostcondition3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 0;
                  //@ signals (Exception e) false;
                  //@ also
                  //@ requires i!= 0;
                  //@ signals (Exception e) true;
                  public void m1bad(int[] a, int i) throws Exception {
                      if (i == 0)
                         throw new Exception(); // Line 10
                      else
                         throw new Exception();
                  }
                  //@ requires i == 0;
                  //@ signals (Exception e) true;
                  //@ also
                  //@ requires i!= 0;
                  //@ signals (Exception e) false;
                  public void m2bad(int[] a, int i) throws Exception {
                      if (i == 0)
                         throw new Exception();
                      else
                         throw new Exception(); // Line 23
                  }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",10
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m2bad",10
                ,"/tt/TestJava.java:18: verify: Associated declaration",7
                );
    }

    // Tests use of \exception token
    @Test
    public void testPostcondition4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ signals (Exception e) \\exception == null;
                  public void m1bad(int[] a, int i) throws Exception {
                         throw new Exception();
                  }
                  //@ signals (Exception e) \\exception != null;
                  public void m1good(int[] a, int i) throws Exception {
                         throw new Exception();
                  }
                  //@ signals (Exception) \\exception != null;
                  public void m2good(int[] a, int i) throws Exception {
                         throw new Exception();
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",10
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }

    // Tests use of \old token in called methods
    @Test
    public void testPostcondition5() {
        addOptions("--code-math=java","--spec-math=java"); // Just to avoid overflow warnings
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int iii;
                  //@ public normal_behavior
                  //@   ensures iii == \\old(iii) + 3;
                  public void m1() {
                         inc();
                         inc();
                         inc();
                  }
                  //@ public normal_behavior
                  //@   ensures iii == \\old(iii) + 3;
                  public void m1bad() {
                         inc();
                         inc();
                  }
                  //@ public normal_behavior
                  //@   assignable iii;
                  //@   ensures iii == \\old(iii) + 1;
                  public void inc()  {
                         ++iii;
                  }
                }
                """
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",15
                ,"/tt/TestJava.java:12: verify: Associated declaration",9
                );
    }

    // Tests use of \old token in called methods
    @Test
    public void testPostcondition5a() {
    	addOptions("--code-math=java","--spec-math=java"); // Just to avoid overflow warnings
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int i;
                  //@ public normal_behavior
                  //@   ensures i == \\old(i) + 3;
                  public void m1() {
                         inc();
                         inc();
                         inc();
                  }
                  //@ public normal_behavior
                  //@   ensures i == \\old(i) + 3;
                  public void m1bad() {
                         inc();
                         inc();
                  }
                  // Default is assignable \\everything
                  //@ public normal_behavior
                  //@   ensures i == \\old(i) + 1;
                  public void inc()  {
                         ++i;
                  }
                }
                """
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",15
                ,"/tt/TestJava.java:12: verify: Associated declaration",9
                );
    }

    // Tests use of \old token in called methods
    @Test
    public void testPostcondition5x() {
    	addOptions("--code-math=bigint","--spec-math=bigint"); // Just to avoid overflow warnings
    	helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int iii;
                  //@ public normal_behavior
                  //@   ensures iii == \\old(iii) + 3;
                  public void m1() {
                         inc();
                         inc();
                         inc();
                  }
                  //@ public normal_behavior
                  //@   ensures iii == \\old(iii) + 3;
                  public void m1bad() {
                         inc();
                         inc();
                  }
                  //@ public normal_behavior
                  //@   assignable iii;
                  //@   ensures iii == \\old(iii) + 1;
                  public void inc()  {
                         ++iii;
                  }
                }
                """
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",15
                ,"/tt/TestJava.java:12: verify: Associated declaration",9
                );
    }
    // Tests use of \old token in called methods
    @Test
    public void testPostcondition5ax() {
    	addOptions("--code-math=bigint","--spec-math=bigint"); // Just to avoid overflow warnings
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int i;
                  //@ public normal_behavior
                  //@   ensures i == \\old(i) + 3;
                  public void m1() {
                         inc();
                         inc();
                         inc();
                  }
                  //@ public normal_behavior
                  //@   ensures i == \\old(i) + 3;
                  public void m1bad() {
                         inc();
                         inc();
                  }
                  // Default is assignable \\everything
                  //@ public normal_behavior
                  //@   ensures i == \\old(i) + 1;
                  public void inc()  {
                         ++i;
                  }
                }
                """
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",15
                ,"/tt/TestJava.java:12: verify: Associated declaration",9
                );
    }

    // FIXME - add checks on object fields, quantifier variables
    // FIXME - need attribute checks on scopes of variables
    @Test
    public void testLabeled() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 0;
                  public void m1good(int i) throws Exception {
                       int j = 0;
                       //@ assert j == 0;
                       a: j = 1; i = 1;
                       //@ assert \\old(i) == 0;
                       b: j = 2; i = 2;
                       //@ assert \\old(j,a) == 0;
                       //@ assert \\old(i,a) == 0;
                       //@ assert \\old(j,b) == 1;
                       //@ assert \\old(i,b) == 1;
                       //@ assert \\pre(i) == 0;

                  }
                }
                """
                );
    }

    @Test
    public void testBox() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures \\result == 7;
                  public int m1good()  {
                      Integer k = 7;
                      int i = k;
                      return i;
                  }
                  }
                """
                );
    }

    @Test
    public void testMethodInvocation() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  /*@ signals_only \\nothing;*/   // FIXME - this used to be part of the default if there were no spec cases at all.
                  public int z(int i)  {
                      return i;
                  }
                  public int m1bad(int k)  {
                      int i = z(k/k);
                      return i;
                  }
                  public void m2bad(int k)  {
                      z(k/k);
                  }
                  //@ requires k > 0;
                  public int m1good(int k)  {
                      int i = z(k/k);
                      return i;
                  }
                  }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1bad",18
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2bad",10

                );
    }

    // Almost duplicate of escnew  // FIXME - of what?
    @Test public void testMethodInvocation1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int z(int i)  {
                      return i;
                  }}
                """
                );
    }

    @Test
    public void testSwitch() {
        addOptions("--code-math=math"); // To avoid warnings because of overflow
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures \\result == i* 2 + 1;
                  public int m1bad(int i) throws Exception {
                      int k;
                       switch (i) {
                        case 1: k = 3; break;
                        default: k = i + i + 1; break;
                        case 2: k = 6; return k;
                       } return k;
                  }
                  //@ ensures \\result == i* 2 + 1;
                  public int m1good(int i) throws Exception {
                      int k;
                       switch (i) {
                        case 1: k = 3; break;
                        default: k = i + i + 1; break;
                        case 2: k = 5; break;
                       } return k;
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",24
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }

    @Test
    public void testTry() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures \\result == 1;
                  public int m1bad() throws Exception {
                      int k;
                       try {
                        k=1;
                       } finally {
                           k = 2;
                        }return k;
                  }
                  //@ ensures \\result == 0;
                  public int m2bad() throws Exception {
                      int k;
                       try {
                        k=1; throw new RuntimeException();
                       } catch (RuntimeException e) {
                           k = 2;
                        } return k;
                  }
                  //@ ensures \\result == 0;
                  public int m3bad() throws Exception {
                      int k;
                       try {
                        k=1; throw new RuntimeException();
                       } catch (RuntimeException e) {
                           k = 2;
                       } finally {
                           k = 3;
                        } return k;
                  }
                  //@ ensures \\result == 1;
                  public int m1good() throws Exception {
                      int k;
                       try {
                        k=1; return k;
                       } finally {
                           k = 2;
                        }
                  }
                  //@ ensures \\result == 2;
                  public int m0good() throws Exception {
                      int k;
                       try {
                        k=1;
                       } finally {
                           k = 2;
                        } return k;
                  }
                  //@ ensures \\result == 2; // Line 50
                  public int m2good() throws Exception {
                      int k;
                       try {
                        k=1; throw new RuntimeException();
                       } catch (RuntimeException e) {
                           k = 2;
                        } return k;
                  }
                  //@ ensures \\result == 3;
                  public int m3good() throws Exception {
                      int k;
                       try {
                        k=1; throw new RuntimeException();
                       } catch (RuntimeException e) {
                           k = 2;
                       } finally {
                           k = 3;
                        } return k;
                  }
                  static public int kk;
                  //@ assignable kk;
                  //@ ensures \\result == 3;
                  //@ signals (Exception e)  false;
                  public int m4good(int i ) throws Exception {
                       try {
                        kk=1; if (i == 0) throw new RuntimeException();
                       } catch (RuntimeException e) {
                           kk = 2;
                        }
                       kk = 3;
                       return kk;
                  }
                  //@ assignable kk;
                  //@ ensures \\result == 3;
                  //@ signals (Exception e)  kk == 1;
                  public int m5good(int i) throws Exception {
                       try {
                        kk=1; if (i == 0) throw new RuntimeException();
                        } finally {}
                       kk = 3;
                       return kk;
                  }
                  //@ assignable kk;
                  //@ ensures \\result == 3;
                  //@ signals (Exception e)  kk == 1;
                  public int m6good(int i) throws Exception {
                        kk=1; if (i == 0) throw new RuntimeException();
                       kk = 3;
                       return kk;
                  }
                  //@ assignable kk;
                  //@ ensures \\result == 3;
                  //@ signals (Exception e) kk == 4;
                  public int m7good(int i) throws Exception {
                       try {
                           kk=1; if (i == 0) throw new RuntimeException();
                           try {
                             kk=2; if (i == 1) throw new RuntimeException();
                           } finally { kk = 5; }
                       } finally { kk = 4; }
                       kk = 3;
                       return kk;
                  }
                  //@ assignable kk;
                  //@ ensures i==0 ==> \\result == 4;
                  //@ signals (Exception e) false;
                  public int m8good(int i) throws Exception {
                       try {
                           kk=1; if (i == 0) throw new RuntimeException();
                       } finally { if (i == 0) return 4; }
                       kk = 3;
                       return kk;
                  }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",10
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (Postcondition) in method m2bad",11
                ,"/tt/TestJava.java:12: verify: Associated declaration",7
                ,"/tt/TestJava.java:30: verify: The prover cannot establish an assertion (Postcondition) in method m3bad",11
                ,"/tt/TestJava.java:21: verify: Associated declaration",7

                );
    }

    @Test // FIXME _ needs type relationships
    public void testTry2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int kk;
                  //@ assignable kk;
                  //@ ensures \\result == 3;
                  //@ signals (Exception e)  false;
                  public int m4agood(int i ) throws Exception {
                       try {
                        kk=1; if (i == 0) throw new RuntimeException();
                       } catch (Exception e) {
                           kk = 2;
                        }
                       kk = 3;
                       return kk;
                  }
                }
                """
                );
    }

    @Test
    public void testUnreachable() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1bad(int i) {
                      if (i == 0) {
                         //@ unreachable;
                      }
                  }
                  //@ requires i != 0;
                  public void m1good(int i) {
                      if (i == 0) {
                         //@ unreachable;
                      }
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Unreachable) in method m1bad",14
                );
    }

    @Test
    public void testGhostSet() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1bad(int i) {
                      //@ ghost int k = 0;      //@ set k = 1;
                      //@ assert k == 0;
                  }
                  //@ requires i != 0;
                  public void m1good(int i) {
                      //@ ghost int k = 0;      //@ set k = 1;
                      //@ assert k == 1;
                  }
                  public void m2bad(int i) {
                      //@ ghost int k = 0;      //@ set k = 1;
                      //@ assert k == 0;
                  }
                  //@ requires i != 0;
                  public void m2good(int i) {
                      //@ ghost int k = 0;      //@ set k = 1;
                      //@ assert k == 1;
                  }
                  public void m3bad() {
                      //@ ghost boolean k = true;
                      //@ set k = (k <=!=> k);
                      //@ assert k;
                  }
                  public void m3good() {
                      //@ ghost boolean k = true;
                      //@ set k = (k <==> k);
                      //@ assert k;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m1bad",11
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Assert) in method m2bad",11
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Assert) in method m3bad",11
                );
    }

    @Test
    public void testGhostSet2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m2good(int i) {
                      //@ ghost int k = 0;      //@
                      //@ assert k == 0;
                  }
                  //@ requires i != 0;
                  public void m2bad(int i) {
                      //@ ghost int k = 0;      //@
                      //@ assert k == 1;
                  }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m2bad",11
                );
    }

    @Test
    public void testHavoc() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1good() {
                      int i = 0;
                      //@ assert i == 0;
                  }
                  public void m1bad() {
                      int i = 0;
                      //@ havoc i;
                      //@ assert i == 0;
                  }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m1bad",11
                );
    }

    @Test
    public void testHavoc2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  int i; int j;
                  public void m1a() {
                      i = 1; j = 2;
                      //@ havoc i;
                      //@ assert j == 2;
                      //@ assert i == 1; // ERROR
                  }
                  public void m1b() {
                      i = 1; j = 2;
                      TestJava g = this;
                      //@ havoc this.*;
                      //@ assert g == this;
                      //@ assert j == 2; // ERROR
                      //@ assert g.i == 1; // ERROR
                  }
                  public void m1c() {
                      i = 1; j = 2;
                      TestJava g = this;
                      //@ havoc g.i;
                      //@ assert j == 2;
                      //@ assert i == 1; // ERROR
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method m1a", 11
                ,anyorder(seq("/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Assert) in method m1b", 11)
                         ,seq("/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Assert) in method m1b",11))
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Assert) in method m1c", 11
                );
    }

    @Test
    public void testHavoc3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a.length > 5;
                  public void m1a(int[] a) {
                      a[1] = 1; a[2] = 2; var b = a;
                      //@ havoc b[2];
                      //@ assert b == a;
                      //@ assert a[1] == 1 && b[1] == 1;
                      //@ assert a[2] == 2; // ERROR
                  }
                  //@ requires a.length > 5;
                  public void m1b(int[] a) {
                      a[1] = 1; a[2] = 2; var b = a;
                      //@ havoc b[*];
                      //@ assert b == a;
                      //@ assert a[2] == 2; // ERROR
                  }
                  //@ requires a.length > 5;
                  public void m1c(int[] a) {
                      a[1] = 1; a[3] = 3; var b = a;
                      //@ havoc b[1..2];
                      //@ assert b == a;
                      //@ assert a[3] == 3;
                      //@ assert a[1] == 1; // ERROR
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m1a", 11
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Assert) in method m1b", 11
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Assert) in method m1c", 11
                );
    }

    @Test
    public void testHavoc4() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ requires a.length > 5;
                  //@ requires \\forall int i; 0 <= i < 5; a[i] != null && a[i].length == 5;
                  public void m1a(int[][] a) {
                      a[1][1] = 1;
                      int[] b = a[1];
                      //@ havoc a[1];
                      //@ assert b[1] == 1;
                      //@ assert b == a[1]; // ERROR
                  }
                  //@ requires a.length > 5;
                  //@ requires \\forall int i; 0 <= i < 5; a[i] != null && a[i].length == 5;
                  public void m1b(int[][] a) {
                      a[1][1] = 1;
                      int[] b = a[1];
                      //@ havoc a[*];
                      //@ assert a[0] != null;
                      //@ assert a.length == \\old(a.length);
                      //@ assert b[1] == 1;
                      //@ assert b == a[1]; // ERROR
                  }
                  //@ requires a.length > 5;
                  //@ requires \\forall int i; 0 <= i < 5; a[i] != null && a[i].length == 5;
                  public void m1c(int @NonNull [] @NonNull [] a) {
                      a[1][1] = 1;
                      int[] b = a[1];
                      //@ havoc a[*];
                      //@ assert a[0] != null;
                      //@ assert a.length == \\old(a.length);
                      //@ assert b[1] == 1;
                      //@ assert b == a[1]; // ERROR
                  }
                  //@ requires a.length > 5;
                  //@ requires \\forall int i; 0 <= i < 5; a[i] != null && a[i].length == 5;
                  public void m1d(int @NonNull [] @NonNull [] a) {
                      a[1][1] = 1;
                      int[] b = a[1];
                      int k = a[1].length;
                      //@ havoc a[1][*];
                      //@ assert b == a[1];
                      //@ assert k == a[1].length;
                  }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m1a", 11
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Assert) in method m1b", 11
                ,"/tt/TestJava.java:32: verify: The prover cannot establish an assertion (Assert) in method m1c", 11
                );
    }

    @Test
    public void testHavoc5() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ requires fff.length > 5;
                  //@ requires \\forall int i; 0 <= i < 5; fff[i] != null && fff[i].length == 5;
                  public void m1a(int[][] fff) {
                      int[] b = fff[1];
                      int k = fff[1].length;
                      //@ assert fff[1].length == 5;
                      //@ havoc fff[*][*];
                      //@ assert fff[1].length == 5;
                      //@ assert k == b.length;
                      //@ assert b == fff[1];
                  }
                }
                """
                );
    }

    @Test
    public void testHavoc6() {
        expectedExit = 1;
        addOptions("--normal");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void m1(int[][] a) {
                      //@ havoc a[*][1];
                  }
                  public void m2(int[][][] a) {
                      //@ havoc a[*][*][*];
                  }
                }
                """
                ,"/tt/TestJava.java:4: error: This pattern is not implemented for havoc: a[*][1]", 17
                ,"/tt/TestJava.java:7: error: This pattern is not implemented for havoc: a[*][*][*]", 17
                );
    }

    @Test
    public void testHavoc7() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void m1() {
                      int[][] a = new int[5][5];
                      a[0][2] = 42;
                      a[1][2] = 43;
                      //@ havoc a[1..2][*];
                      //@ check a[0][2] == 42;
                      //@ check a[1][2] == 43; // ERROR
                  }
                  public void m2() {
                      int[][] a = new int[5][5];
                      int k = a.length;
                      a[0][2] = 40;
                      a[0][3] = 41;
                      a[1][2] = 42;
                      a[1][3] = 43;
                      p: {}
                      //@ havoc a[1..2][3..4];
                      //@ check a[0][2] == 40;
                      //@ check a[0][3] == 41;
                      //@ check a[1][2] == 42;
                      //@ check a[1][2] == \\old(a[1][2], p);
                      //@ check a[1][3] == 43; // ERROR
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m1", 11
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Assert) in method m2", 11
                );
    }

    @Test
    public void testHavocNN() {
        expectedExit = 6;
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  Object oo = new Object();
                  @Nullable Object ooo;
                  public void m1(Object a) {
                      //@ havoc a;
                      //@ assert a != null;
                  }
                  public void m2(@Nullable Object a) {
                      //@ havoc a;
                      //@ assert a != null; // ERROR
                  }
                  public void m3() {
                      //@ havoc oo;
                      //@ assert oo != null;
                  }
                  public void m4() {
                      //@ havoc ooo;
                      //@ assert ooo != null; // ERROR
                  }
                }
                """
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method m2", 11
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (Assert) in method m4", 11
                );
    }

    @Test
    public void testHavocNN1() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ requires a.length > 5;
                  public void m0(Object[] a) {
                      //@ havoc a[*];
                      //@ assert a[1] != null;
                  }
                  //@ requires a.length > 5;
                  public void m1(@NonNull Object[] a) {
                      //@ havoc a[*];
                      //@ assert a[1] != null;
                  }
                  //@ requires a.length > 5;
                  public void m2(@Nullable Object[] a) {
                      //@ havoc a[*];
                      //@ assert a[1] != null; // ERROR
                  }
                }
                """
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Assert) in method m2", 11
                );
    }

    @Test
    public void testHavocNN2() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ requires a.length > 5;
                  //@ requires \\forall int i; 0 <= i < 5; a[i].length > 5;
                  public void m0(Object[][] a) {
                      p:;
                      //@ havoc a[1..2][3..4];
                      //@ assert a[1] == \\old(a[1],p);
                      //@ assert a[1] != null;
                  }
                  //@ requires a.length > 5;
                  //@ requires \\forall int i; 0 <= i < 5; a[i].length > 5;
                  public void m1(@NonNull Object[][] a) {
                      p:;
                      //@ havoc a[*][*];
                      //@ assert a[1] == \\old(a[1],p);
                      //@ assert a[2][3] != null;
                  }
                  //@ requires a.length > 5;
                  //@ requires \\forall int i; 0 <= i < 5; a[i].length > 5;
                  public void m2(@Nullable Object[][] a) {
                      p:;
                      //@ havoc a[*][*];
                      //@ assert a[1] == \\old(a[1],p);
                      //@ assert a[2][3] != null; // ERROR
                  }
                }
                """
                ,"/tt/TestJava.java:25: verify: The prover cannot establish an assertion (Assert) in method m2", 11
                );
    }

    @Test
    public void testHavocIsAssignable() {
        helpEsc("tt.TestJava",
                """
                package tt; //@ nullable_by_default
                public class TestJava {
                  public static int k;
                  public int i;
                  public int[] a;
                  public TestJava t;
                  //@ writes \\nothing;
                  public void m1() {
                    //@ havoc \\nothing
                  }
                  //@ writes \\nothing;
                  public void m2() {
                    //@ havoc \\everything;
                  }
                  //@ writes \\nothing;
                  public void m3() { //@ assume t != null;
                    //@ havoc k, t.k, TestJava.k, tt.TestJava.k;
                  }
                  //@ writes \\nothing;
                  public void m4() {
                    //@ havoc this.i, this.*;
                  }
                  //@ writes \\nothing;
                  public void m5() {
                    //@ assume a != null && t != null && 0 <= i && i < a.length;
                    //@ havoc i;
                  }
                  //@ writes \\nothing;
                  public void m6() {
                    //@ assume t != null;
                    //@ havoc t.i; //, t.*;
                  }
                  //@ writes \\nothing;
                  public void m7() {
                    //@ assume a != null && t != null && 0 <= i && i < a.length && 10 < a.length;
                    //@ havoc a[i], a[1..2], a[*];
                  }
                  //@ writes \\nothing;
                  public void m8() {
                    int i;
                    //@ havoc i;
                  }
                }
                """
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assignable) in method m2: \\everything", 15
                ,"/tt/TestJava.java:11: verify: Associated declaration",7
                ,anyorder(seq("/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assignable) in method m3: k", 15
                             ,"/tt/TestJava.java:15: verify: Associated declaration", 7)
                         ,seq("/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assignable) in method m3: t.k", 19
                             ,"/tt/TestJava.java:15: verify: Associated declaration", 7)
                         ,seq("/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assignable) in method m3: TestJava.k", 31
                             ,"/tt/TestJava.java:15: verify: Associated declaration", 7)
                         ,seq("/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assignable) in method m3: tt.TestJava.k", 46
                             ,"/tt/TestJava.java:15: verify: Associated declaration", 7))
                ,anyorder(seq("/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Assignable) in method m4: this.i", 19
                             ,"/tt/TestJava.java:19: verify: Associated declaration", 7)
                         ,seq("/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Assignable) in method m4: this.*", 27
                             ,"/tt/TestJava.java:19: verify: Associated declaration", 7))
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (Assignable) in method m5: i", 15
                ,"/tt/TestJava.java:23: verify: Associated declaration", 7
                ,"/tt/TestJava.java:31: verify: The prover cannot establish an assertion (Assignable) in method m6: t.i", 16
                ,"/tt/TestJava.java:28: verify: Associated declaration", 7
                ,anyorder(seq("/tt/TestJava.java:36: verify: The prover cannot establish an assertion (Assignable) in method m7: a[i]", 15
                             ,"/tt/TestJava.java:33: verify: Associated declaration", 7)
                         ,seq("/tt/TestJava.java:36: verify: The prover cannot establish an assertion (Assignable) in method m7: a[1 .. 2]", 21
                             ,"/tt/TestJava.java:33: verify: Associated declaration", 7)
                         ,seq("/tt/TestJava.java:36: verify: The prover cannot establish an assertion (Assignable) in method m7: a[*]", 30
                             ,"/tt/TestJava.java:33: verify: Associated declaration", 7))

                );
    }

    @Test
    public void testHavocIsAssignableOK() {
        helpEsc("tt.TestJava",
                """
                package tt; //@ nullable_by_default
                public class TestJava {
                  public static int k;
                  public int i;
                  public int[] a;
                  public TestJava t;
                  //@ writes \\everything;
                  public void m1() {
                    //@ havoc \\nothing
                  }
                  //@ writes \\everything;
                  public void m2() {
                    //@ havoc \\everything;
                  }
                  //@ writes \\everything;
                  public void m3() { //@ assume t != null;
                    //@ havoc k, t.k, TestJava.k, tt.TestJava.k;
                  }
                  //@ writes \\everything;
                  public void m4() {
                    //@ havoc this.i, this.*;
                  }
                  //@ writes \\everything;
                  public void m5() {
                    //@ assume a != null && t != null && 0 <= i && i < a.length;
                    //@ havoc i;
                  }
                  //@ writes \\everything;
                  public void m6() {
                    //@ assume t != null;
                    //@ havoc t.i; //, t.*;
                  }
                  //@ writes \\everything;
                  public void m7() {
                    //@ assume a != null && t != null && 0 <= i && i < a.length && 10 < a.length;
                    //@ havoc a[i], a[1..2], a[*];
                  }
                  //@ writes \\everything;
                  public void m8() {
                    int i;
                    //@ havoc i;
                  }
                }
                """
                );
    }

    // FIXME _ check that different return or throw statements are properly pointed to

    // FIXME - needs proper expansion of array accesses
    @Test
    public void testPostcondition10() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures a[i]>0;
                  public void m1bad(int[] a, int i) {
                  }
                  //@ requires i >= 0 && i < a.length;
                  //@ ensures a[i]==true || a[i]==false;
                  public void m1good(boolean[] a, int i) {
                  }
                }
                """
                ,anyorder(
                        seq("/tt/TestJava.java:3: verify: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m1bad",16
                        	,"/tt/TestJava.java:5: verify: Associated method exit",4
                        	)
                        ,seq("/tt/TestJava.java:3: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m1bad",16
                        		,"/tt/TestJava.java:5: verify: Associated method exit",4
                        		)
                        ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",15
                                ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                                )
                );
    }

    @Test
    public void testPostcondition1a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ signals (Exception) false;
                  public void m1bad(int[] a, int i) {
                    throw new RuntimeException();
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",5
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }



    // FIXME - need tests with multiple ensures and various cases

    // FIXME - test definedness in postconditions

    // FIXME - exceptional postconditions

    // FIXME - need precondition checks for calling methods
    // FIXME - need checks for ensures assumptions when calling methods
    // FIXME - complete assignables
    // FIXME - assignables for method calls

    // Just testing binary and unary
    @Test
    public void testBinaryUnary() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires true;
                  //@ ensures \\result ==4;
                  public int m1bad() {
                    return 1 + 2;
                  }
                  //@ requires true;
                  //@ ensures \\result == 3;
                  public int m1ok() {
                    return 1 + 2;
                  }
                  //@ requires x >= 0;
                  //@ ensures \\result < 0;
                  public int m2bad(int x) {
                    return -x;
                  }
                  //@ requires x >= 0;
                  //@ ensures \\result <= 0;
                  public int m2ok(int x) {
                    return -x;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                ,"/tt/TestJava.java:14: verify: Associated declaration",7
                );
    }

    @Test
    public void testIncDec() {
    	addOptions("-code-math=java","-spec-math=java"); // Just to avoid overflow warnings
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { static public int i;
                  //@ assignable \\everything;
                  //@ ensures \\result == i;
                  //@ ensures i == \\old(i) + 1;
                  public int m1ok() {
                    return ++i;
                  }
                  //@ assignable \\everything;
                  //@ ensures \\result == i;
                  //@ ensures i == \\old(i) - 1;
                  public int m2ok() {
                    return --i;
                  }
                  //@ assignable \\everything;
                  //@ ensures \\result == \\old(i);
                  //@ ensures i == \\old(i) + 1;
                  public int m3ok() {
                    return i++;
                  }
                  //@ assignable \\everything;
                  //@ ensures \\result == i;
                  //@ ensures i == \\old(i) + 1;
                  public int m3bad() {
                    return i++;
                  }
                  //@ assignable \\everything;
                  //@ ensures \\result == \\old(i);
                  //@ ensures i == \\old(i) - 1;
                  public int m4ok() {
                    return i--;
                  }
                  //@ assignable \\everything;
                  //@ ensures \\result == i;
                  //@ ensures i == \\old(i) - 1;
                  public int m4bad() {
                    return i--;
                  }
                }
                """
                ,"/tt/TestJava.java:25: verify: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                ,"/tt/TestJava.java:22: verify: Associated declaration",7
                ,"/tt/TestJava.java:37: verify: The prover cannot establish an assertion (Postcondition) in method m4bad",5
                ,"/tt/TestJava.java:34: verify: Associated declaration",7
                );
    }

    // Just testing binary and unary
    @Test
    public void testJMLBinaryUnary() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires p ==> q;
                  //@ ensures !p || q;
                  public void m1ok(boolean p, boolean q) {
                  }
                  //@ requires p <==> q;
                  //@ ensures p == q;
                  public void m2ok(boolean p, boolean q) {
                  }
                  //@ requires p <=!=> q;
                  //@ ensures p != q;
                  public void m3ok(boolean p, boolean q) {
                  }
                  //@ requires p <== q;
                  //@ ensures p || !q;
                  public void m4ok(boolean p, boolean q) {
                  }
                  //@ requires !p || q;
                  //@ ensures p ==> q;
                  public void m5ok(boolean p, boolean q) {
                  }
                  //@ requires p == q;
                  //@ ensures p <==> q;
                  public void m6ok(boolean p, boolean q) {
                  }
                  //@ requires p != q;
                  //@ ensures p <=!=> q;
                  public void m7ok(boolean p, boolean q) {
                  }
                  //@ requires p || !q;
                  //@ ensures p <== q;
                  public void m8ok(boolean p, boolean q) {
                  }
                }
                """
                );
    }

    @Test
    public void testConditional2() {
        addOptions("-escMaxWarnings=1");
        addOptions("-code-math=safe");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i < 100000;
                  //@ ensures \\result == i;
                  public int m1bad(boolean b, int i) {
                    return (b && (i == 1)) ? i : i + 1 ;
                  }
                  //@ requires i < 100000;
                  //@ ensures \\result >= i;
                  public int m1ok(boolean b, int i) {
                    return (b && (i == 1)) ? i : i + 1 ;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                );
    }

    @Test
    public void testConditional() {
        addOptions("-escMaxWarnings=1");
        addOptions("-code-math=java");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires true;
                  //@ ensures \\result == i;
                  public int m1bad(boolean b, int i) {
                    return (b && (i == 1)) ? i : i + 1 ;
                  }
                  //@ requires i < 100000;
                  //@ ensures \\result >= i;
                  public int m1ok(boolean b, int i) {
                    return (b && (i == 1)) ? i : i + 1 ;
                  }
                  //@ requires true;
                  //@ ensures \\result >= i;
                  public int m2bad(boolean b, int i) {
                    return (b && (i == 1)) ? i : i + 1 ;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                ,"/tt/TestJava.java:14: verify: Associated declaration",7
                );
    }

    @Test
    public void testConditional3() {
        addOptions("-escMaxWarnings=1");
        addOptions("-code-math=math");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires true;
                  //@ ensures \\result == i;
                  public int m1bad(boolean b, int i) {
                    return (b && (i == 1)) ? i : i + 1 ;
                  }
                  //@ requires true;
                  //@ ensures \\result >= i;
                  public int m1ok(boolean b, int i) {
                    return (b && (i == 1)) ? i : i + 1 ;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                );
    }

    @Test
    public void testShortCircuit() {
        //Assume.assumeTrue(!"cvc4".equals(solver)); // SKIPPING cvc4 does not handle integer division
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava { int f;
                  public boolean m1bad(boolean b, int i) {
                    return i != 0 || (20/i <= 20 ? true : true) ;
                  }
                  //@ ensures \\result;
                  public boolean m1ok(boolean b, int i) {
                    return i == 0 || (i/i > 0 ? true : true) ;
                  }
                  public boolean m2bad(boolean b, int i) {
                    return i == 0 && (20/i <= 20) ;
                  }
                  public boolean m2ok(boolean b, int i) {
                    return i != 0 && (20/i <= 20 ? true : true) ;
                  }
                  public boolean m3bad(@Nullable TestJava t) {
                    return t != null || t.f == 1 ;
                  }
                  public boolean m3ok(@Nullable TestJava t) {
                    return t != null && t.f == 1 ;
                  }
                  //@ requires a;
                  //@ ensures \\result;
                  //@ also
                  //@ requires !a;
                  //@ ensures \\result == b;
                  public boolean m4ok(boolean a, boolean b) {
                    return a || b ;
                  }
                  //@ requires a;
                  //@ ensures b;
                  //@ also
                  //@ requires !a;
                  //@ ensures \\result == b;
                  public boolean m4bad(boolean a, boolean b) {
                    return a || b ;
                  }
                  //@ requires a;
                  //@ ensures \\result == b;
                  //@ also
                  //@ requires !a;
                  //@ ensures \\result == false;
                  public boolean m5ok(boolean a, boolean b) {
                    return a && b ;
                  }
                  //@ requires i < 2 && i > -2;
                  //@ ensures \\result;
                  public boolean m1bugOK(int i) {
                    return i == 0 || (20/i <= 20 ? true : true) ;
                  }
                  //@ ensures \\result;  // FIXME Look at the counterexample on this one (TODO)
                  public boolean m1bug(int i) {
                    return i == 0 || (20/i <= 20 ? true : true) ;
                  }
                  //@ requires i < 30 && i > -30;
                  //@ ensures \\result;
                  public boolean m1bugOK2(int i) {
                    return i == 0 || (20/i <= 20 ? true : true) ;
                  }
                }
                """
                // FIXME - Regarding m1bugOK it should be valid, but returns unknown
                // Keep these - the result is unknown on some solvers and
                // exposed a bug in handling unknown results

                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1bad",25
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2bad",25
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m3bad",26
                ,"/tt/TestJava.java:36: verify: The prover cannot establish an assertion (Postcondition) in method m4bad",5
                ,"/tt/TestJava.java:31: verify: Associated declaration",7
                );
    }

    // FIXME - almost duplicate with escnew // FIXME - duplicate of what?
    @Test public void testShortCircuitDup() {
        addOptions("-escMaxWarnings=1");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava { int f;
                  public boolean m1bad(boolean b, int i) {
                    return i != 0 || (20/i <= 20) ;
                  }
                  //@ ensures \\result;
                  public boolean m1ok(boolean b, int i) {
                    return i == 0 || (i/i > 0) ;
                  }
                  public boolean m2bad(boolean b, int i) {
                    return i == 0 && (20/i <= 20) ;
                  }
                  public boolean m2ok(boolean b, int i) {
                    return i != 0 && (20/i <= 20) ;
                  }
                  public boolean m3bad(@Nullable TestJava t) {
                    return t != null || t.f == 1 ;
                  }
                  public boolean m3ok(@Nullable TestJava t) {
                    return t != null && t.f == 1 ;
                  }
                  //@ requires a;
                  //@ ensures \\result;
                  //@ also
                  //@ requires !a;
                  //@ ensures \\result == b;
                  public boolean m4ok(boolean a, boolean b) {
                    return a || b ;
                  }
                  //@ requires a;
                  //@ ensures b;
                  //@ also
                  //@ requires !a;
                  //@ ensures \\result == b;
                  public boolean m4bad(boolean a, boolean b) {
                    return a || b ;
                  }
                  //@ requires a;
                  //@ ensures \\result == b;
                  //@ also
                  //@ requires !a;
                  //@ ensures \\result == false;
                  public boolean m5ok(boolean a, boolean b) {
                    return a && b ;
                  }
                  //@ requires i < 2 && i > -2;
                  //@ ensures \\result;
                  public boolean m1bugOK(int i) {
                    return i == 0 || (20/i <= 20) ;
                  }
                  //@ ensures \\result;
                  public boolean m1bug(int i) {
                    return i == 0 || (20/i <= 20) ;
                  }
                  //@ requires i < 30 && i > -30;
                  //@ ensures \\result;
                  public boolean m1bugOK2(int i) {
                    return i == 0 || (20/i <= 20) ;
                  }
                }
                """
                // FIXME - Regarding m1bugOK: it should be valid, but returns unknown
                // Keep these - the result is unknown on some solvers and
                // exposed a bug in handling unknown results

                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1bad",25
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2bad",25
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m3bad",26
                ,"/tt/TestJava.java:36: verify: The prover cannot establish an assertion (Postcondition) in method m4bad",5
                ,"/tt/TestJava.java:31: verify: Associated declaration",7
//                ,"/tt/TestJava.java:52: verify: The prover cannot establish an assertion (Postcondition) in method m1bug",5
//                ,"/tt/TestJava.java:50: verify: Associated declaration",7  // FIXME - review?
                );
    }

    @Test public void testJmlLabelExpression() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires true;
                  //@ ensures b ==> (i!=5) ;
                  public int m1ok(boolean b, int i) {
                    //@ ghost boolean bb = (\\lbl LBL_BB b);
                    //@ ghost boolean bbp = (\\lblpos LBL_BB2 (i!=5));
                    //@ ghost boolean bbn = (\\lblneg LBL_BB3 (i!=5));
                    //@ ghost int ii = (\\lbl LBL_BBI i);
                    return 1;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: Label LBL_BB has value true",34
                ,"/tt/TestJava.java:8: verify: Label LBL_BB3 has value false",38
                ,"/tt/TestJava.java:9: verify: Label LBL_BBI has value 5",30
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Postcondition) in method m1ok",5
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                );
    }

    @Test
    public void testBoolOpsParens() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires true;
                  //@ ensures \\result;
                  public boolean m1bad(boolean p, boolean q) {
                    return p == q;
                  }
                  //@ requires p && q;
                  //@ ensures \\result;
                  public boolean m1ok(boolean p, boolean q) {
                    return ((p == q)) ;
                  }
                  //@ requires true;
                  //@ ensures \\result;
                  public boolean m2bad(boolean p, boolean q) {
                    return p != q;
                  }
                  //@ requires p && !q;
                  //@ ensures \\result;
                  public boolean m2ok(boolean p, boolean q) {
                    return p != q ;
                  }
                  //@ requires true;
                  //@ ensures \\result;
                  public boolean m3bad(boolean p, boolean q) {
                    return p == !q;
                  }
                  //@ requires p && !q;
                  //@ ensures \\result;
                  public boolean m3ok(boolean p, boolean q) {
                    return p == !q ;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                ,"/tt/TestJava.java:14: verify: Associated declaration",7
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                ,"/tt/TestJava.java:24: verify: Associated declaration",7
                );
    }

    @Test
    public void testBoxing() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int m1bad(/*@ nullable */ Integer i) {
                    return i;
                  }
                  public int m1ok(/*@ non_null */ Integer i) {
                    return i;
                  }
                  public void m2ok() {
                    int i = 3;
                    Integer ii = i;
                    int j = ii;
                    //@ assert i == j;
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method m1bad",12
                );
    }

    @Test  // FIXME - problem is an infinite loop with use of consistentWithEquals - invariants use it, but the invariants are part of the specs for the (model pure) consistentWithEquals method
    public void testSelect() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int f;
                  //@ requires true;
                  //@ ensures \\result == 1;
                  public int m1bad() {
                    return this.f ;
                  }
                  //@ requires this.f == 1;
                  //@ ensures \\result == 1;
                  public int m1ok() {
                    return this.f ;
                  }
                  //@ requires true;
                  //@ ensures \\result == 1;
                  public int m2bad() {
                    return f ;
                  }
                  //@ requires f == 1;
                  //@ ensures \\result == 1;
                  public int m2ok() {
                    return f ;
                  }
                  //@ requires f == 1;
                  //@ ensures \\result == 1;
                  public int m3bad(TestJava p) {
                    return p.f ;
                  }
                  //@ requires true;
                  //@ ensures true;
                  public int m3bad2(/*@ nullable*/ TestJava p) {
                    return p.f ;
                  }
                  //@ requires p.f == 1;
                  //@ ensures \\result == 1;
                  public int m3ok(TestJava p) {
                    return p.f ;
                  }
                  public void m4ok(TestJava p) {
                    System.out.println("A");
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:5: verify: Associated declaration",7
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                ,"/tt/TestJava.java:15: verify: Associated declaration",7
                ,"/tt/TestJava.java:27: verify: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                ,"/tt/TestJava.java:25: verify: Associated declaration",7
                ,"/tt/TestJava.java:32: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m3bad2",13
                );
    }

    @Test
    public void testChangedParam() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int f;
                  //@ requires i < 100;
                  //@ ensures \\result == i;
                  public int m1bad(int i) {
                    return (i+=1) ;
                  }
                  //@ requires i < 100;
                  //@ ensures \\result == i+1;
                  public int m1good(int i) {
                    return (i+=1) ;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:5: verify: Associated declaration",7
                );
    }

    @Test
    public void testNameReused() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1good() {
                    { int s = 0; /*@ assert s == 0; */ }
                    { int s = 1; /*@ assert s == 1; */ }
                  }
                  public void m1bad() {
                    { int s = 0; /*@ assert s == 1; */ }
                    { int s = 1; /*@ assert s == 0; */ }
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method m1bad",22
                );
    }

    @Test
    public void testNonNullField() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public Object nnf;
                  public /*@ nullable*/ Object f;
                  public Object m1bad() {
                    return this.f ;
                  }
                  public Object m1ok() {
                    return this.nnf ;
                  }
                  public void m2bad() {
                    nnf = null ;
                  }
                  public void m2ok() {
                    f = null ;
                  }
                  public TestJava() { nnf = new Object(); }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method m1bad", 10
                ,"/tt/TestJava.java:5: verify: Associated declaration", 17
                ,"/tt/TestJava.java:6: verify: Associated method exit", 5
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2bad",9
                );
    }

    // This tests a bug in which static invariants were not part of the VC.
    // The problem is that helper methods do not inherit invariants, even ones that are fixed, such as those that define the values of fields
    @Test
    public void testInvariantInheritance2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public static int CHILD = 3;
                  //@ static public invariant CHILD == 3;
                  //@ helper pure
                  public static void m1() {
                    //@ assert CHILD == 3 ;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m1",9
                );
    }

    @Test
    public void testAsList() {
        helpEsc("tt.TestJava",
                """
                package tt;
                import java.util.List; public class TestJava  {
                  public enum E { A};
                  public static void m1() {
                    List<E> m = java.util.Arrays.asList(new E[]{E.A});
                  }
                }
                """
                );
        }

    @Test
    public void testAsList1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public enum E { A};
                  public static void m1() {
                    java.util.List<E> m = java.util.Arrays.asList(new E[]{E.A});
                  }
                }
                """
                );
        }

    @Test // Allow final on invariant to mean assume regardless of helper status
    public void testInvariantInheritance() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public final static int CHILD; static { CHILD = 3; }
                  //@ static final public invariant CHILD == 3;
                  //@ public normal_behavior
                  //@   ensures true;
                  //@   static_initializer
                  //@ helper pure
                  public static void m1() {
                    //@ assert CHILD == 3 ;
                  }
                }
                """
                );
        }
    @Test
    public void testInvariantInheritance3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public /*@ final */ static int CHILD = 3;
                  //@ helper pure
                  public static void m1() {
                    //@ assert CHILD == 3 ;
                  }
                }
                """
                );
        }

    @Test
    public void testInvariantInheritanceArray() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public /*@ final */ static int[] FIELD = new int[]{1,2,3,4,5};
                  public /*@ final */ static int[] FIELD2 = {1,2,3,4,5,6};
                  //@ public normal_behavior
                  //@   ensures true;
                  //@   static_initializer
                  //@  pure
                  public static void m1() {
                    //@ assert H.ZZZZ == 79 ;
                    //@ assert FIELD.length == 5 ;
                    //@ assert FIELD2.length == 6 ;
                    //@ assert H.CHILD.length == 5 ;
                    //@ assert H.CHILD2.length == 6 ;
                  }
                }
                 class H  {
                  public /*@ final */ static int ZZZZ = 79;
                  public /*@ final */ static int[] CHILD = new int[]{1,2,3,4,5};
                  public /*@ final */ static int[] CHILD2 = {1,2,3,4,5,6};
                  //@ public normal_behavior
                  //@   ensures true;
                  //@   static_initializer
                }
                """
                );

        }

    @Test
    public void testDeterminism() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava<T> {
                  //@ ensures true;
                  //@ model pure public int mm(int i);
                  //@ ensures true;
                  //@ pure
                  public int mmr(int i) { return 0; };
                  //@ ensures !\\fresh(\\result);
                  //@ spec_pure
                  //@ model public <TT> TT mt(int i);
                  //@ ensures !\\fresh(\\result);
                  //@ spec_pure
                  public /*@ nullable */ <TT> TT mtr(int i) { return null; };
                  //@ ensures true;
                  //@ model no_state public static int mf(int i);
                  //@ ensures true;
                  //@ no_state
                  public static int mfr(int i) { return 0; }
                  //@ ensures mm(i) == mm(i);
                  public void m1(int i) {
                  }
                  //@ ensures mmr(i) == \\result;
                  public int m1x(int i) { // Line 20
                      return mmr(i);
                  }
                  //@ ensures mt(i) == mt(i);
                  public void m3(int i) { // Line 24
                  }
                  //@ ensures mtr(i) == \\result;
                  public /*@ nullable */ <T> T m3x(int i) {
                    return mtr(i); } // Line 28
                  //@ ensures mf(i) == mf(i);
                  public void m2(int i) {
                  }
                  //@ ensures mfr(i) == \\result;
                  public int m2x(int i) {
                      return mfr(i);
                  }
                }
                """
                );
    }

    @Test
    public void testDeterminismFresh() {
        addOptions("--no-allow-pure-in-specs");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava<T> {
                  public /*@ nullable */ Object o;
                  //@ ensures \\fresh(\\result);
                  //@ pure
                  public Object mm(int i) { return new Object(); }
                  //@ ensures \\result == o;
                  //@ pure
                  public /*@ nullable */ Object mm2(int i) { return o; } // Line 7
                  //@ ensures true;
                  //@ pure
                  public Object mm3(int i) { return new Object(); }
                  //@ ensures \\fresh(\\result); // Line 10
                  //@ ensures mm(i) == \\result; // ERROR - not necessarily the case
                  public Object m1(int i) {
                      return mm(i); // Line 13
                  }
                  //@ ensures \\result == null || !\\fresh(\\result);
                  //@ ensures mm2(i) == \\result;
                  public /*@ nullable */ Object m2(int i) {
                      return mm2(i);
                  }
                  //@ ensures mm3(i) == \\result; // Line 20 // ERROR - not necessarily the case
                  public Object m3(int i) {
                      return mm3(i);
                  }
                }
                """
                ,"/tt/TestJava.java:14: warning: A non-pure method is being called where it is not permitted: tt.TestJava.mm(int)", 17
                ,"/tt/TestJava.java:19: warning: A non-pure method is being called where it is not permitted: tt.TestJava.mm2(int)", 18
                ,"/tt/TestJava.java:23: warning: A non-pure method is being called where it is not permitted: tt.TestJava.mm3(int)", 18
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Postcondition) in method m1",7
                ,"/tt/TestJava.java:14: verify: Associated declaration",7
                ,"/tt/TestJava.java:25: verify: The prover cannot establish an assertion (Postcondition) in method m3",7
                ,"/tt/TestJava.java:23: verify: Associated declaration",7
                );
    }

    @Test
    public void testMethodMatching() {
        addOptions("-method=mm"); // Part of test
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava<T> {
                   int k;
                  //@ ensures true;
                  //@ pure
                  public int mpure(int i) { return i+17; }
                  public void mm(int i) {
                     int j = 0;
                     if (i == 1) j = mpure(i);
                     else if (i == 2) { j = mpure(i);  }
                     else  j = 29;
                     //@ assert i==1 ==> j == mpure(1);
                     //@ assert i==2 ==> j == mpure(2);
                     //@ assert i==3 ==> j == mpure(1); // CAN'T PROVE
                     //@ assert i==3 ==> j != mpure(1); // CAN'T PROVE
                  }
                }
                """
                ,anyorder(
                 seq("/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Assert) in method mm",10)
                ,seq("/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Assert) in method mm",10)
                )
                );
    }

    @Test
    public void testMethodMatching1() {
        addOptions("--method=mm"); // Part of test
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava<T> {
                   int k;
                  //@ ensures true;
                  //@ pure
                  public int mpure(int i) { return i+17; }
                  public void mm(int i) {
                     int j = 0;
                     if (i == 1) j = mpure(i);
                     else if (i == 2) { j = mpure(i); k = 0; }
                     else  j = 29;
                     //@ check i==1 ==> j == mpure(1);
                     //@ check i==2 ==> j == mpure(2); // CAN'T PROVE
                     //@ check i==3 ==> j == mpure(1); // CAN'T PROVE
                     //@ check i==3 ==> j != mpure(1); // CAN'T PROVE
                  }
                }
                """
                ,anyorder(
              //   seq("/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method mm",10)  // FIXME - review
                 seq("/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assert) in method mm",10) // FIXME - review -- why not prove this like the i == 1 case
                ,seq("/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Assert) in method mm",10)
                ,seq("/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Assert) in method mm",10)
                )
                );
    }

    @Test
    public void testExplicitAssert() {
        addOptions("-escMaxWarnings=1");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires true;
                  public void m1bad(int i) {
                    //@ assert i == 0 ;
                  }
                  //@ requires i == 0;
                  public void m1ok(int i) {
                    //@ assert i == 0 ;
                  }
                  public void m1okb(int i) {
                    //@ assume i == 0 ;
                    //@ assert i == 0 ;
                  }
                  //@ requires true;
                  public void m2bad(int i) {
                    assert i == 0 ;
                  }
                  //@ requires true;
                  public void m2badb(int i) { // Line 20
                    assert i == 0 : "m2badb fails" ;
                  }
                  //@ requires i == 0;
                  public void m2ok(int i) {
                    assert i == 0 : "ASD" ;
                  }
                  public void m2okb(int i) {
                    //@ assume i == 0 ;
                    assert i == 0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assert) in method m2bad",5
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Assert) in method m2badb: m2badb fails",5
                );
    }

    @Test
    public void testUndefined() {
        Assume.assumeTrue(runLongTests);
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires 10/i < 0;
                  public void m1bad(int i) {
                  }
                  //@ requires i != 0 && 10/i < 0;
                  public void m1good(int i) {
                  }
                  //@ ensures 10/i < 0 || true;
                  public void m2bad(int i) {
                  }
                  //@ ensures i == 0 || 10/i < 0 || true;
                  public void m2good(int i) {
                  }
                  public void m3bad(int i) {
                  //@ assume 10/i < 0 || true;
                  }
                  public void m3good(int i) {
                  //@ assume i == 0 || 10/i < 0 || true;
                  }
                  public void m4bad(int i) {
                  //@ assert 10/i < 0 ||true;
                  }
                  public void m4good(int i) {
                  //@ assert i == 0 || 10/i < 0 || true;
                  }
                  public void m5bad(int i) {
                  //@ assert 10%i < 0 ||true;
                  }
                  public void m5good(int i) {
                  //@ assert i == 0 || 10%i < 0 || true;
                  }
                }
                """   // FIXME - not sure why just one postcondition problem has exit information
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (UndefinedDivideByZero) in method m1bad",18
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (UndefinedDivideByZero) in method m2bad",17
                ,"/tt/TestJava.java:11: verify: Associated method exit",4
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (UndefinedDivideByZero) in method m3bad",16
                ,"/tt/TestJava.java:22: verify: The prover cannot establish an assertion (UndefinedDivideByZero) in method m4bad",16
                ,"/tt/TestJava.java:28: verify: The prover cannot establish an assertion (UndefinedDivideByZero) in method m5bad",16
                );    }


    @Test
    public void testControl() {
        addOptions("--code-math=java");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  int x,xx; static int y,yy;
                  public void m1good() {
                    for (int i=0; i<10; i=i+1) {
                       //@ assert i<10;
                    }
                  }
                  public void m2good() {
                    int i=0;
                    while (i<10) {
                       //@ assert i<10;
                       i = i + 1;
                    }
                    //@ assert i>=10;
                  }
                  public void m2bad() {
                    int i=0;
                    while (i<10) {
                       //@ assert i<10;
                       i = i + 1;
                    }
                    //@ assert i>10;
                  }
                  //@ requires arg != null;
                  public void m4good(int[] arg) {
                    int i=0;
                    for (int k: arg) {
                       i = i + 1;
                    }
                    // FIXME //@ assert i == arg.length;
                  }
                  //@ requires arg != null;
                  public void m4bad(int[] arg) {
                    int i=0;
                    for (int k: arg) {
                       i = i + 1;
                    }
                    //@ unreachable;
                  }
                }
                """
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Assert) in method m2bad",9
                ,"/tt/TestJava.java:39: verify: The prover cannot establish an assertion (Unreachable) in method m4bad",9
                );
        // FIXME - fix the assumptions here - first time through loop
//      +"  public void m3good() {\n"
//      +"    int i=0; \n"
//      +"    do {\n"
//      +"       //@ assert i<10;\n"
//      +"       i = i + 1;\n"
//      +"       //@ assert i<=10;\n"
//      +"    } while (i<10); \n"
//      +"    //@ assert i>=10;\n"
//      +"  }\n"
//                      
//      +"  public void m3bad() {\n"
//      +"    int i=0; \n"
//      +"    do {\n"
//      +"       //@ assert i<10;\n"
//      +"       i = i + 1;\n"
//      +"       //@ assert i<=10;\n"
//      +"    } while (i<10); \n"
//      +"    //@ assert i>10;\n"
//      +"  }\n"
        }

    @Test
    public void testConstantFolding() {
        helpEsc("tt.TestJava",// FIXME - lots more tests needed
                """
                package tt;
                public class TestJava<T> {
                  public void mm(int i) {
                      boolean b = true && false;
                      //@ assert !b;
                      b = true || false;
                      //@ assert b;
                      b = true == false;
                      //@ assert !b;
                      b = true != false;
                      //@ assert b;
                      b = 3L != 2;
                      //@ assert b;
                      b = (short)3 == (short)3;
                      //@ assert b;
                      b = "" == "";
                      //@ assert b;
                      b = ' ' == ' ';
                      //@ assert b;
                      int a = 2 + 3;
                      //@ assert a == 5;
                      a = (short)2 + (short)3;
                      //@ assert a == 5;
                      long g = 2L + 3;
                      //@ assert g == 5;
                      g = (short)2 + (short)3;
                      //@ assert g == 5;
                      a = (short)3 / (short)2;
                      //@ assert a == 1;
                      g = 3L / 2;
                      //@ assert g == 1;
                      g = (short)3 / (short)2;
                      //@ assert g == 1;
                  }
                }
                """
//                +"      String s = \"x\" + \"y\";\n" 
//              +"      //@ assert s = \"xy\";\n" 
//              +"      s = \"x\" + 1;\n" 
//              +"      //@ assert s = \"x1\";\n" 
//              +"      s = \"x\" + true;\n" 
//              +"      //@ assert s = \"xtrue\";\n" 
//              +"      s = false + \"x\";\n" 
//              +"      //@ assert s = \"falsex\";\n" 
//              +"      s = \"x\" + null;\n" 
//              +"      //@ assert s = \"xnull\";\n" 
                );
    }

    @Test
    public void testConstantFolding4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a.length > 10;
                  public void mm(int[] a) {
                      int x = a[2];
                      int[] z = new int[3];
                      //@ ghost boolean b = Integer.class <:= Number.class;
                      //@ ghost boolean bb = Number.class <:= Boolean.class;
                      //@ assert b && !bb;
                  }
                }
                """
                );
    }

    @Test
    public void testConstantFolding3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1() {
                      m(Integer.class);
                  }
                  public void m2() {
                      m(Boolean.class);
                  }
                  public void m3() {
                      m(Short.class);
                  }
                  public static int j;
                  //@   requires clazz <:= Number.class;
                  //@   assignable j;
                  //@   ensures j >= 200;// Line 15
                  //@ also
                  //@   requires clazz <:= Boolean.class;
                  //@   assignable j;
                  //@   ensures j  == 100;
                  //@ also
                  //@   requires clazz <:= String.class;
                  //@   assignable j;
                  //@   ensures j == 0;
                  public static  void m( Class<?> clazz) {// Line 24
                    //@ show clazz, Integer.class, Short.class, Boolean.class, String.class, clazz <:= Number.class, clazz <:= Boolean.class, clazz, Number.class.isAssignableFrom(clazz) == (clazz <:= Number.class);
                    //@ assert clazz <:= Number.class <==> Number.class.isAssignableFrom(clazz);
                    if (clazz == Integer.class) j = 200;
                    else if (clazz == Short.class) j = 201;
                    else if (clazz == Boolean.class) j = 100;
                    else if (Number.class.isAssignableFrom(clazz)) j = 202;
                    else j = 0;
                  }
                }
                """
                );
    }

    @Test
    public void testConstantFolding5() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void mm() {
                      m(1);
                      m(2);
                  }
                  public int j;
                  //@ requires i > 0;
                  //@ assignable j;
                  //@ ensures j > 100;
                  //@ also
                  //@ requires i >= 2;
                  //@ assignable j;
                  //@ ensures j > 200;
                  public void m(int i) {
                    j = 1000;
                  }
                }
                """
                );
    }

    @Test
    public void testConstantFolding2() { // FIXME - lots more tests needed
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava<T> {
                  public void mm(int i) {
                      int a = 2 / 1;
                      a = 2 / (1-1);
                      long g = 3L / 0;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method mm",13
                );
    }

    @Test
    public void testRefactoring() {
        expectedExit = 0;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void mok(int i) {
                      int a = 2;
                      {
                      //@#-
                      a++;
                      //@#
                      a+=3;
                      //@# a += 2;
                      }
                      //@ assert a == 7;
                  }
                  public void mmbad(int i) {
                      int a = 2;
                      {
                      //@#-
                      a++;
                      //@#-
                      a+=3;
                      //@# a += 2;
                      }
                      //@ assert a == 4; // OK
                      //@ assert a == 7; // SHOULD FAIL
                  }
                  public void mok2(int i) {
                      int a = 2;
                      {
                      //@#-
                      a++;
                      //@# a += 2;
                      }
                      //@ assert a == 4;
                  }
                }
                """
                ,"/tt/TestJava.java:19: warning: Already skipping tokens",10
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Assert) in method mmbad",11
                );
    }

    @Test
    public void testRefactoring2() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void mbad2(int i) {
                      int a = 2;
                      {
                      //@#-
                      a++;
                      }
                      //@ assert a == 4;
                  }
                }
                """
                ,"/tt/TestJava.java:6: warning: //#- block is not closed at the end of file",10
                ,"/tt/TestJava.java:5: error: reached end of file while parsing",8
                );
    }

    @Test
    public void testRefactoringNotAComment() {
        expectedExit = 0;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void mbad2(int i) {
                      int a = 2;
                      {
                      //@#Q
                      a++;
                      //@#Q
                      }
                      //@ assert a == 3;
                  }
                }
                """
                );
    }

    @Test
    public void testPreconditionInfo() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava<T> {
                  //@ requires i == 4;
                  //@ ensures \\result == 5;
                  //@ also
                  //@ requires i == 5;
                  //@ ensures \\result == 6;
                  /*@ pure */ public int m(int i) {
                     return i + 1;
                  }
                  public void mm(int i) {
                  //@ assert 0<m(3);
                  }
                }
                """
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method mm",17
                ,"/tt/TestJava.java:8: verify: Associated declaration",26
                ,optional(
                "/tt/TestJava.java:3: verify: Precondition conjunct is false: i == 4",18
                ,"/tt/TestJava.java:6: verify: Precondition conjunct is false: i == 5",18
                )


                );
    }

    @Test
    public void testOldInAssign() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                 public int f;
                 public int[] a = new int[10];
                  //@ old int j = i+2;
                  //@ requires 0 <= j && j < 10;
                  //@ requires a != null && a.length == 10;
                  //@ assignable a[j];
                  //@ ensures a[j] == 42;
                  public void m(int i) {
                     a[i+2] = 42;
                  }
                  //@ requires 0 <= i && i < 8;
                  //@ requires a != null && a.length == 10;
                  //@ assignable a[i];
                  public void m1bad(int i) {
                     i += 2; a[i] = 42;
                  }
                  //@ requires 0 <= i && i < 8;
                  //@ requires a != null && a.length == 10;
                  //@ assignable a[i+2];
                  public void m2(int i) {
                     i += 2; a[i] = 42;
                  }
                  //@ old int j = i+1;
                  //@ requires 0 <= j && j < 9;
                  //@ requires a != null && a.length == 10;
                  //@ assignable a[j];
                  public void mbad(int i) {
                     a[i+2] = 42;
                  }
                }
                """
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assignable) in method m1bad: a[i]",19
                ,"/tt/TestJava.java:15: verify: Associated declaration",7
                ,"/tt/TestJava.java:30: verify: The prover cannot establish an assertion (Assignable) in method mbad: a[i + 2]",13
                ,"/tt/TestJava.java:28: verify: Associated declaration",7


                );
    }

    @Test
    public void testOldInCall() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                 public int f;
                 public int[] a = new int[100];
                  //@ old int j = i+off;
                  //@ requires a != null && a.length == 100;
                  //@ requires 0 <= i && i < 50 && 0 <= off && off < 30;
                  //@ assignable a[j];
                  public void mmm(int i, int off) {
                     a[i+off] = 42;
                  }
                  //@ requires 0 <= i && i < 50;
                  //@ requires a != null && a.length == 100;
                  //@ assignable a[i],a[i+10],a[i+25];
                  public void m(int i) {
                     mmm(i,0);
                     mmm(i,10);
                     mmm(i,25);
                  }
                }
                """
                );
    }

    @Test
    public void testConcat() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires s1.length() + s2.length() <= Integer.MAX_VALUE;
                  public void m1(String s1, String s2) {
                     String s = s1 + s2;
                     //@ assert s.length() == s1.length() + s2.length();
                  }
                  //@ requires s1.length() < Integer.MAX_VALUE;
                  public void m2(String s1, String s2) {
                     String s = s1 + String.valueOf('c'); String sc = String.valueOf('c'); //@ check sc.length() == 1;
                     //@ assert s.length() == s1.length() + 1;
                  }
                  //@ requires s1.length() < Integer.MAX_VALUE;
                  public void m2a(String s1, String s2) {
                     String s = s1 + Character.toString('c'); //@ check s.chars.length == s1.chars.length + 1;
                     //@ assert s.length() == s1.length() + 1;
                  }
                  //@ requires s1.length() < Integer.MAX_VALUE;
                  public void m3(String s1, String s2) {
                     String s = s1 + 'c';
                     //@ assert s.length() == s1.length() + 1;
                  }
                }
                """
                );
    }

    @Test
    public void testLongShift() {
        addOptions("--code-math=java");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1(long x) {
                     int y = (int)x;
                     long yy = y < 0 ? ((long)y-Integer.MIN_VALUE-Integer.MIN_VALUE) : y;
                     int z = (int)(x>>32);
                     long w = (((long)z)<<32) + yy;
                     long zzz = (x>>>32);
                     int zz = (int)(x>>>32);
                     long ww = (((long)zz)<<32) + yy;
                     //@ show x, y, z, zzz, zz, yy, w, ww;
                     //@ assert w == x;
                     //@ assert ww == x;
                  }
                }
                """
                );
    }

    @Test
    public void testPureConstructor() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {

                  public int i;

                  //@ pure
                  public TestJava(int i) { this.i = i; }

                  public void m() {
                    var c = new TestJava(42);
                  }
                }
                """
                );
    }

    @Test
    public void testSpecPureConstructor() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {

                  public int i;

                  //@ spec_pure
                  public TestJava(int i) { this.i = i; }

                  public void m() {
                    var c = new TestJava(42);
                  }
                }
                """
                ,"/tt/TestJava.java:6: error: This JML modifier is not allowed for a constructor declaration", 7
                );
    }
}
