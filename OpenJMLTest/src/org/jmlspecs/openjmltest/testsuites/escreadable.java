package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escreadable extends EscBase {


    // FIXME - needs writable checks for assignables in method calls?
    // FIXME - what about assignments to arrays elements
    // FIXME - what about references in type decl initializations
    // FIXME - what about reads/writes in constructors
    // FIXME - same checks in rac

    @Test
    public void testReadable() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_java_math*/ public class TestJava {
                  public static boolean b; public boolean bb; int z; //@ readable z if bb;
                  int x; //@ readable x if b;
                  static int y; //@ readable y if b;
                  //@ requires b;
                  public int m1(int i) { int j = 0;
                    return x + this.x + i + j;
                  }
                  //@ requires !b;
                  public int m1b() {
                    return x;
                  }
                  //@ requires !b;
                  public int m1c() {
                    return this.x ;
                  }
                  //@ requires b;
                  public int m2() {
                    return y + TestJava.y ;
                  }
                  //@ requires !b;
                  public int m2b() {
                    return y;
                  }
                  //@ requires !b;
                  public int m2c() {
                    return TestJava.y ;
                  }
                  //@ requires !bb && a.bb;
                  public int m3(TestJava a) {
                    return a.z ;
                  }
                  //@ requires bb && !a.bb;
                  public int m3b(TestJava a) {
                    return a.z ;
                  }
                  //@ requires !bb && a.bb;
                  public int m3c(TestJava a) {
                    return this.z ;
                  }
                  //@ requires bb && !a.bb;
                  public int m3d(TestJava a) {
                    return this.z ;
                  }
                  //@ requires !bb && a.bb;
                  public int m3e(TestJava a) {
                    return z ;
                  }
                  //@ requires bb && !a.bb;
                  public int m3f(TestJava a) {
                    return z ;
                  }
                }
                """
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Readable-if) in method m1b: tt.TestJava.x",12
                ,"/tt/TestJava.java:4: verify: Associated declaration",14
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Readable-if) in method m1c: tt.TestJava.x",16
                ,"/tt/TestJava.java:4: verify: Associated declaration",14
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Readable-if) in method m2b: tt.TestJava.y",12
                ,"/tt/TestJava.java:5: verify: Associated declaration",21
                ,"/tt/TestJava.java:28: verify: The prover cannot establish an assertion (Readable-if) in method m2c: tt.TestJava.y",20
                ,"/tt/TestJava.java:5: verify: Associated declaration",21
                ,"/tt/TestJava.java:36: verify: The prover cannot establish an assertion (Readable-if) in method m3b: tt.TestJava.z",13
                ,"/tt/TestJava.java:3: verify: Associated declaration",58
                ,"/tt/TestJava.java:40: verify: The prover cannot establish an assertion (Readable-if) in method m3c: tt.TestJava.z",16
                ,"/tt/TestJava.java:3: verify: Associated declaration",58
                ,"/tt/TestJava.java:48: verify: The prover cannot establish an assertion (Readable-if) in method m3e: tt.TestJava.z",12
                ,"/tt/TestJava.java:3: verify: Associated declaration",58
                );
    }


    @Test
    public void testWritable() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_java_math*/ public class TestJava {
                  public static boolean b; public boolean bb; int z; //@ writable z if bb;
                  int x; //@ writable x if b;
                  static int y; //@ writable y if b;
                  //@ requires b;
                  public void m1(int i) {
                    x = 0 ; i = 0; int j; j = 0;
                    this.x = 0 ;
                  }
                  //@ requires !b;
                  public void m1b() {
                    x = 0 ;
                  }
                  //@ requires !b;
                  public void m1c() {
                    this.x = 0 ;
                  }
                  //@ requires b;
                  public void m2() {
                    y = 0;
                    TestJava.y = 0 ;
                  }
                  //@ requires !b;
                  public void m2b() {
                    y = 0;
                  }
                  //@ requires !b;
                  public void m2c() {
                    TestJava.y = 0 ;
                  }
                  //@ requires !bb && a.bb;
                  public void m3(TestJava a) {
                    a.z = 0 ;
                  }
                  //@ requires bb && !a.bb;
                  public void m3b(TestJava a) {
                    a.z = 0 ;
                  }
                  //@ requires !bb && a.bb;
                  public void m3c(TestJava a) {
                    z = 0 ;
                  }
                  //@ requires bb && !a.bb;
                  public void m3d(TestJava a) {
                    z = 0 ;
                  }
                  //@ requires !bb && a.bb;
                  public void m3e(TestJava a) {
                    this.z = 0 ;
                  }
                  //@ requires bb && !a.bb;
                  public void m3f(TestJava a) {
                    this.z = 0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Writable-if) in method m1b: tt.TestJava.x",5
                ,"/tt/TestJava.java:4: verify: Associated declaration",14
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Writable-if) in method m1c: tt.TestJava.x",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",14
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (Writable-if) in method m2b: tt.TestJava.y",5
                ,"/tt/TestJava.java:5: verify: Associated declaration",21
                ,"/tt/TestJava.java:30: verify: The prover cannot establish an assertion (Writable-if) in method m2c: tt.TestJava.y",13
                ,"/tt/TestJava.java:5: verify: Associated declaration",21
                ,"/tt/TestJava.java:38: verify: The prover cannot establish an assertion (Writable-if) in method m3b: tt.TestJava.z",6
                ,"/tt/TestJava.java:3: verify: Associated declaration",58
                ,"/tt/TestJava.java:42: verify: The prover cannot establish an assertion (Writable-if) in method m3c: tt.TestJava.z",5
                ,"/tt/TestJava.java:3: verify: Associated declaration",58
                ,"/tt/TestJava.java:50: verify: The prover cannot establish an assertion (Writable-if) in method m3e: tt.TestJava.z",9
                ,"/tt/TestJava.java:3: verify: Associated declaration",58
                );
    }

    @Test
    public void testWritable2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_java_math*/ public class TestJava {
                  public static boolean b; public boolean bb; int z; //@ writable z if bb;
                  int x; //@ writable x if b;
                  static int y; //@ writable y if b;
                  //@ requires b;
                  public void m1(int i) {
                    x += 0 ; i += 0; int j = 0; j += 0;
                    this.x += 0 ;
                  }
                  //@ requires !b;
                  public void m1b() {
                    x += 0 ;
                  }
                  //@ requires !b;
                  public void m1c() {
                    this.x += 0 ;
                  }
                  //@ requires b;
                  public void m2() {
                    y += 0;
                    TestJava.y += 0 ;
                  }
                  //@ requires !b;
                  public void m2b() {
                    y += 0;
                  }
                  //@ requires !b;
                  public void m2c() {
                    TestJava.y += 0 ;
                  }
                  //@ requires !bb && a.bb;
                  public void m3(TestJava a) {
                    a.z += 0 ;
                  }
                  //@ requires bb && !a.bb;
                  public void m3b(TestJava a) {
                    a.z += 0 ;
                  }
                  //@ requires !bb && a.bb;
                  public void m3c(TestJava a) {
                    z += 0 ;
                  }
                  //@ requires bb && !a.bb;
                  public void m3d(TestJava a) {
                    z += 0 ;
                  }
                  //@ requires !bb && a.bb;
                  public void m3e(TestJava a) {
                    this.z += 0 ;
                  }
                  //@ requires bb && !a.bb;
                  public void m3f(TestJava a) {
                    this.z += 0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Writable-if) in method m1b: tt.TestJava.x",5
                ,"/tt/TestJava.java:4: verify: Associated declaration",14
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Writable-if) in method m1c: tt.TestJava.x",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",14
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (Writable-if) in method m2b: tt.TestJava.y",5
                ,"/tt/TestJava.java:5: verify: Associated declaration",21
                ,"/tt/TestJava.java:30: verify: The prover cannot establish an assertion (Writable-if) in method m2c: tt.TestJava.y",13
                ,"/tt/TestJava.java:5: verify: Associated declaration",21
                ,"/tt/TestJava.java:38: verify: The prover cannot establish an assertion (Writable-if) in method m3b: tt.TestJava.z",6
                ,"/tt/TestJava.java:3: verify: Associated declaration",58
                ,"/tt/TestJava.java:42: verify: The prover cannot establish an assertion (Writable-if) in method m3c: tt.TestJava.z",5
                ,"/tt/TestJava.java:3: verify: Associated declaration",58
                ,"/tt/TestJava.java:50: verify: The prover cannot establish an assertion (Writable-if) in method m3e: tt.TestJava.z",9
                ,"/tt/TestJava.java:3: verify: Associated declaration",58
                );
    }

    @Test
    public void testReadableA() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_java_math*/ public class TestJava {
                  public static boolean b; public boolean bb; int z; //@ readable z if bb;
                  int x; //@ readable x if b;
                  static int y; //@ readable y if b;
                  //@ requires b;
                  public void m1(int i) {
                    x = 0 ; i = 0; int j; j = 0;
                    this.x = 0 ;
                  }
                  //@ requires !b;
                  public void m1b() {
                    x = 0 ;
                  }
                  //@ requires !b;
                  public void m1c() {
                    this.x = 0 ;
                  }
                  //@ requires b;
                  public void m2() {
                    y = 0;
                    TestJava.y = 0 ;
                  }
                  //@ requires !b;
                  public void m2b() {
                    y = 0;
                  }
                  //@ requires !b;
                  public void m2c() {
                    TestJava.y = 0 ;
                  }
                  //@ requires !bb && a.bb;
                  public void m3(TestJava a) {
                    a.z = 0 ;
                  }
                  //@ requires bb && !a.bb;
                  public void m3b(TestJava a) {
                    a.z = 0 ;
                  }
                  //@ requires !bb && a.bb;
                  public void m3c(TestJava a) {
                    z = 0 ;
                  }
                  //@ requires bb && !a.bb;
                  public void m3d(TestJava a) {
                    z = 0 ;
                  }
                  //@ requires !bb && a.bb;
                  public void m3e(TestJava a) {
                    this.z = 0 ;
                  }
                  //@ requires bb && !a.bb;
                  public void m3f(TestJava a) {
                    this.z = 0 ;
                  }
                }
                """
                );
    }

    @Test
    public void testReadableB() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_java_math*/ public class TestJava {
                  public static boolean b; public boolean bb; int z; //@ readable z if bb;
                  int x; //@ readable x if b;
                  static int y; //@ readable y if b;
                  //@ requires b;
                  public void m1(int i) {
                    x += 0 ; i += 0; int j = 0; j += 0;
                    this.x += 0 ;
                  }
                  //@ requires !b;
                  public void m1b() {
                    x += 0 ;
                  }
                  //@ requires !b;
                  public void m1c() {
                    this.x += 0 ;
                  }
                  //@ requires b;
                  public void m2() {
                    y += 0;
                    TestJava.y += 0 ;
                  }
                  //@ requires !b;
                  public void m2b() {
                    y += 0;
                  }
                  //@ requires !b;
                  public void m2c() {
                    TestJava.y += 0 ;
                  }
                  //@ requires !bb && a.bb;
                  public void m3(TestJava a) {
                    a.z += 0 ;
                  }
                  //@ requires bb && !a.bb;
                  public void m3b(TestJava a) {
                    a.z += 0 ;
                  }
                  //@ requires !bb && a.bb;
                  public void m3c(TestJava a) {
                    z += 0 ;
                  }
                  //@ requires bb && !a.bb;
                  public void m3d(TestJava a) {
                    z += 0 ;
                  }
                  //@ requires !bb && a.bb;
                  public void m3e(TestJava a) {
                    this.z += 0 ;
                  }
                  //@ requires bb && !a.bb;
                  public void m3f(TestJava a) {
                    this.z += 0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Readable-if) in method m1b: tt.TestJava.x",5
                ,"/tt/TestJava.java:4: verify: Associated declaration",14
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Readable-if) in method m1c: tt.TestJava.x",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",14
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (Readable-if) in method m2b: tt.TestJava.y",5
                ,"/tt/TestJava.java:5: verify: Associated declaration",21
                ,"/tt/TestJava.java:30: verify: The prover cannot establish an assertion (Readable-if) in method m2c: tt.TestJava.y",13
                ,"/tt/TestJava.java:5: verify: Associated declaration",21
                ,"/tt/TestJava.java:38: verify: The prover cannot establish an assertion (Readable-if) in method m3b: tt.TestJava.z",6
                ,"/tt/TestJava.java:3: verify: Associated declaration",58
                ,"/tt/TestJava.java:42: verify: The prover cannot establish an assertion (Readable-if) in method m3c: tt.TestJava.z",5
                ,"/tt/TestJava.java:3: verify: Associated declaration",58
                ,"/tt/TestJava.java:50: verify: The prover cannot establish an assertion (Readable-if) in method m3e: tt.TestJava.z",9
                ,"/tt/TestJava.java:3: verify: Associated declaration",58
                );
    }

    @Test
    public void testVisibility() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_java_math*/ public class TestJava {
                  public static boolean bs1;
                  protected static boolean bs2;
                   static boolean bs3;
                  private static boolean bs4;
                  public boolean b1;
                  protected boolean b2;
                   boolean b3;
                  private boolean b4;
                  static public int z1; //@ readable z1 if b1;
                  public int x1; //@ readable x1 if b1 || b2 || b3 || b4;
                  static public int y1; //@ readable y1 if bs1 || bs2 || bs3 || bs4;
                  protected int x2; //@ readable x2 if b1 || b2 || b3 || b4;
                  static protected int y2; //@ readable y2 if bs1 || bs2 || bs3 || bs4;
                   int x3; //@ readable x3 if b1 || b2 || b3 || b4;
                  static  int y3; //@ readable y3 if bs1 || bs2 || bs3 || bs4;
                  private int x4; //@ readable x4 if b1 || b2 || b3 || b4;
                  static private int y4; //@ readable y4 if bs1 || bs2 || bs3 || bs4;
                }
                """
                ,"/tt/TestJava.java:11: error: non-static variable b1 cannot be referenced from a static context",44
                ,"/tt/TestJava.java:12: error: An identifier with protected visibility may not be used in a readable clause with public visibility",43
                ,"/tt/TestJava.java:12: error: An identifier with package visibility may not be used in a readable clause with public visibility",49
                ,"/tt/TestJava.java:12: error: An identifier with private visibility may not be used in a readable clause with public visibility",55
                ,"/tt/TestJava.java:13: error: An identifier with protected visibility may not be used in a readable clause with public visibility",51
                ,"/tt/TestJava.java:13: error: An identifier with package visibility may not be used in a readable clause with public visibility",58
                ,"/tt/TestJava.java:13: error: An identifier with private visibility may not be used in a readable clause with public visibility",65
                ,"/tt/TestJava.java:14: error: An identifier with package visibility may not be used in a readable clause with protected visibility",52
                ,"/tt/TestJava.java:14: error: An identifier with private visibility may not be used in a readable clause with protected visibility",58
                ,"/tt/TestJava.java:15: error: An identifier with package visibility may not be used in a readable clause with protected visibility",61
                ,"/tt/TestJava.java:15: error: An identifier with private visibility may not be used in a readable clause with protected visibility",68
                ,"/tt/TestJava.java:16: error: An identifier with private visibility may not be used in a readable clause with package visibility",49
                ,"/tt/TestJava.java:17: error: An identifier with private visibility may not be used in a readable clause with package visibility",59
                );
    }
}
