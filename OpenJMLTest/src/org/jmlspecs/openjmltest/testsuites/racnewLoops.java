package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Test;

/** These tests exercise the RAC checking.  They compile a test class
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racnewLoops extends RacBase {

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true; print = true;
        super.setUp();
        addOptions("--rac-show-source=line");
        addOptions("-code-math=java","-spec-math=java");  // FIXME - errors if we use bigint semantics
    }

    // FIXME - needs more tests with break and continue, including nested loops
    // Also tests with \count and \values

    @Test public void testForLoop2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m();
                    System.out.println("END");
                  }
                  static void m() {
                    //@ loop_invariant i <9 ;
                    //@ decreases 10-i;
                    for (int i=0; i<10; i++) ;
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: JML loop invariant is false at end of loop body"
                ,"/tt/TestJava.java:8: verify: JML assumed loop invariant is false at beginning of loop body"
                ,"/tt/TestJava.java:8: verify: JML loop invariant is false at end of loop body"
                ,"/tt/TestJava.java:8: verify: JML assumed loop invariant is false at beginning of loop body"
                ,"/tt/TestJava.java:8: verify: JML loop invariant is false after exiting loop"
                ,"END"
                );
    }

    @Test public void testForLoop() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m();
                    System.out.println("END");
                  }
                  static void m() {
                    //@ loop_invariant i <= 10 ;
                    //@ decreases 7-i;
                    for (int i=0; i<10; i++) ;
                  }
                }
                """
                ,"/tt/TestJava.java:9: JML loop variant is negative"
                ,"/tt/TestJava.java:9: JML loop variant is negative"
                ,"END"
                );
    }

    @Test public void testForLoopIndex() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m();
                    System.out.println("END");
                  }
                  static void m() {
                    //@ loop_invariant i == \\count ;
                    //@ decreases 10-\\count;
                    for (int i=0; i<10; i++) ;
                  }
                }
                """
                ,"END"
                );
    }

    @Test public void testForNested() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m();
                    System.out.println("END");
                  }
                  static void m() {
                    //@ loop_invariant i <= 10 ;
                    for (int i=0; i<10; i++) {
                      //@ ghost int save = \\count;
                      //@ loop_invariant \\count <= save;
                      for (int j=0; j<i; j++) {
                        ;
                      }
                    }
                  }
                }
                """
                ,"END"
                );
    }


    @Test public void testForEachLoop() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m();
                    System.out.println("END");
                  }
                  static void m() {
                    int[] a = new int[10];
                    //@ ghost int i = 0;
                    //@ loop_invariant i <= a.length ;
                    //@ decreases a.length-i;
                    for (int j: a) {
                       //@ set i = i + 1;
                    }
                  }
                }
                """
                ,"END"
                );
    }

    @Test public void testForEachLoop2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m();
                    System.out.println("END");
                  }
                  static void m() {
                    int[] a = new int[10];
                    //@ ghost int i = 0;
                    //@ loop_invariant i < a.length ;
                    //@ decreases a.length-i-2;
                    for (int j: a) {
                       //@ set i = i + 1;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:11: JML loop variant is negative"
                ,"/tt/TestJava.java:10: JML loop invariant is false at end of loop body"
                ,"/tt/TestJava.java:10: JML assumed loop invariant is false at beginning of loop body"
                ,"/tt/TestJava.java:10: verify: JML loop invariant is false after exiting loop"
                ,"END"
                );
    }


    @Test public void testLoop() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(5);
                    m(0);
                    System.out.println("END");
                  }
                  static void m(int i) {
                    //@ loop_invariant i>= 0;
                    //@ decreases i;
                    while (i>0) --i;
                  }
                }
                """
                ,"END"
                );
    }

    @Test public void testLoopIndex() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(5);
                    m(0);
                    System.out.println("END");
                  }
                  static void m(int i) {
                    //@ loop_invariant i + \\count == \\old(i);
                    //@ decreases i;
                    while (i>0) --i;
                  }
                }
                """
                ,"END"
                );
    }


    @Test public void testLoop2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(5);
                    m(0);
                    m(-1);
                    System.out.println("END");
                  }
                  static void m(int i) {
                    System.out.println("VALUE " + i);
                    //@ loop_invariant i>= 0;
                    //@ decreases i;
                    while (i>=0) --i;
                  }
                }
                """
                ,"VALUE 5"
                ,"/tt/TestJava.java:11: verify: JML loop invariant is false at end of loop body"
                ,"/tt/TestJava.java:11: verify: JML assumed loop invariant is false at beginning of loop body"
                ,"/tt/TestJava.java:11: verify: JML loop invariant is false after exiting loop"
                ,"VALUE 0"
                ,"/tt/TestJava.java:11: verify: JML loop invariant is false at end of loop body"
                ,"/tt/TestJava.java:11: verify: JML assumed loop invariant is false at beginning of loop body"
                ,"/tt/TestJava.java:11: verify: JML loop invariant is false after exiting loop"
                ,"VALUE -1"
                ,"/tt/TestJava.java:11: verify: JML loop invariant is false before entering loop"
                ,"/tt/TestJava.java:11: verify: JML assumed loop invariant is false at beginning of loop body"
                ,"/tt/TestJava.java:11: verify: JML loop invariant is false after exiting loop"
               ,"END"
                );
    }

    @Test public void testLoop3() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(5);
                    System.out.println("END");
                  }
                  static void m(int i) {
                    //@ loop_invariant i>= 0;
                    //@ decreases i-2;
                    while (i>0) --i;
                  }
                }
                """
                ,"/tt/TestJava.java:9: JML loop variant is negative"
                ,"END"
                );
    }

    @Test public void testLoop4() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(1);
                    System.out.println("END");
                  }
                  static void m(int i) {
                    //@ loop_invariant i>= 0;
                    //@ decreases 10-i;
                    while (i>0) --i;
                  }
                }
                """
                ,"/tt/TestJava.java:9: JML loop variant does not decrease"
                ,"END"
                );
    }

    @Test public void testLoop5() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(7);
                    System.out.println("END");
                  }
                  static void m(int i) {
                    //@ loop_invariant i>= 0;
                    //@ decreases i;
                    while (i>0) {
                        System.out.println("VALUE " + i);
                        --i;
                        if (i == 4) continue;
                        --i;
                    }
                  }
                }
                """
                ,"VALUE 7"
                ,"VALUE 5"
                ,"VALUE 4"
                ,"VALUE 2"
                ,"END"
                );
    }


    @Test public void testDoLoop() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(5);
                    m(1);
                    System.out.println("END");
                  }
                  static void m(int i) {
                    //@ loop_invariant i>= 0;
                    //@ decreases i;
                    do { --i; } while (i>0);
                  }
                }
                """
                ,"END"
                );
    }

    @Test public void testDoLoopIndex() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(5);
                    m(1);
                    System.out.println("END");
                  }
                  static void m(int i) {
                    //@ loop_invariant i>= 0;
                    //@ decreases i;
                    /*@ loop_invariant i + \\count == \\old(i); */
                    do { --i; } while (i>0);
                  }
                }
                """
                ,"END"
                );
    }

    @Test public void testDoLoopIndexBad() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(1);
                    System.out.println("END");
                  }
                  static void m(int i) {
                    //@ decreases i;
                    /*@ loop_invariant i + \\count == \\old(i); */
                    do {
                      --i;
                      --i;
                    } while (i>0);
                    //@ assert i == -1;
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: JML loop invariant is false after exiting loop"
                ,"END"
                );
    }


    @Test public void testDoLoop2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(5);
                    m(0);
                    m(-2);
                    System.out.println("END");
                  }
                  static void m(int i) {
                    System.out.println("VALUE " + i);
                    //@ loop_invariant i >= -1;
                    //@ decreases i;
                    do { --i; } while (i>=0);
                  }
                }
                """
                ,"VALUE 5"
                ,"VALUE 0"
                ,"VALUE -2"
                ,"/tt/TestJava.java:11: verify: JML loop invariant is false before entering loop"
                ,"/tt/TestJava.java:11: verify: JML assumed loop invariant is false at beginning of loop body"
                ,"/tt/TestJava.java:12: verify: JML loop variant is negative"
                ,"/tt/TestJava.java:11: verify: JML loop invariant is false after exiting loop"
                ,"END"
                );
    }



    @Test public void testForIter1() {
        helpRacText("tt.A",
                """
                package tt;
                class A {
                  public static void main(String[] args) {
                    java.util.List<Integer> list = new java.util.LinkedList<Integer>();
                    list.add(0);
                    m(list);
                  }
                  static void m(java.util.List<Integer> list) {
                    int sum = 0;
                    //@ loop_invariant sum >= 0;
                    for (int o: list) {  sum += o; }
                    //@ assert sum >= 0;
                  }
                }
                """
                );
    }

    @Test public void testForIter1bad() {
        helpRacText("tt.A",
                """
                package tt;
                class A {
                  public static void main(String[] args) {
                    java.util.List<Integer> list = new java.util.LinkedList<Integer>();
                    list.add(0);
                    m(list);
                  }
                  static void m(java.util.List<Integer> list) {
                    int sum = 0;
                    //@ loop_invariant sum >= 0;
                    for (int o: list) {  sum += o; }
                    //@ assert sum > 0;
                  }
                }
                """
                ,"/tt/A.java:12: JML assertion is false"
                );
    }

    @Test public void testForEach4() {
        helpRacText("tt.A",
                """
                package tt;
                class A {
                  public static void main(String[] args) {
                    Integer[] aa = new Integer[]{1,2,3};
                    m(aa);
                  }
                  static void m(Integer[] list) {
                    int sum = 0;
                    //@ loop_invariant sum >= 0;
                    for (int o: list) { /*@ assume o >= 0; */ sum += o; }
                    //@ assert sum >= 0;
                  }
                }
                """
                );
    }

    @Test public void testForEach4bad() {
        helpRacText("tt.A",
                """
                package tt;
                class A {
                  public static void main(String[] args) {
                    Integer[] aa = new Integer[]{0,0,0};
                    m(aa);
                  }
                  static void m(Integer[] list) {
                    int sum = 0;
                    //@ loop_invariant sum >= 0;
                    for (int o: list) { /*@ assume o >= 0; */ sum += o; }
                    //@ assert sum > 0;
                  }
                }
                """
                ,"/tt/A.java:11: JML assertion is false"
                );
    }




}
