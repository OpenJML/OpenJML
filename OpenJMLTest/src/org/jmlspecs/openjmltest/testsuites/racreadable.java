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
public class racreadable extends RacBase {

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true; print = true;
        super.setUp();
        addOptions("-jmltesting");
    }

    @Test
    public void testReadable() {
    	addOptions("--rac-show-source=line");
        helpRacText("tt.TestJava",
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
                  public static void main(String... args) {
                     TestJava a = new TestJava(); TestJava t = new TestJava();
                     t.b = true; t.m1(0); t.b = false; t.m1b(); t.m1c();
                     t.b = true; t.m2(); t.b = false; t.m2b(); t.m2c();
                     t.bb = false; a.bb = true; t.m3(a);
                     t.bb = true; a.bb = false; t.m3b(a);
                     t.bb = false; a.bb = true; t.m3c(a);
                     t.bb = true; a.bb = false; t.m3d(a);
                     t.bb = false; a.bb = true; t.m3e(a);
                     t.bb = true; a.bb = false; t.m3f(a);
                  }
                }
                """
                ,"/tt/TestJava.java:12: JML readable clause is false for variable tt.TestJava.x"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:16: JML readable clause is false for variable tt.TestJava.x"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:24: JML readable clause is false for variable tt.TestJava.y"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:28: JML readable clause is false for variable tt.TestJava.y"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:36: JML readable clause is false for variable tt.TestJava.z"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"/tt/TestJava.java:40: JML readable clause is false for variable tt.TestJava.z"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"/tt/TestJava.java:48: JML readable clause is false for variable tt.TestJava.z"
                ,"/tt/TestJava.java:3: Associated declaration"
                );
    }

    @Test
    public void testWritable() {
    	addOptions("--rac-show-source=line");
    	helpRacText("tt.TestJava",
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
                  public static void main(String... args) {
                     TestJava a = new TestJava(); TestJava t = new TestJava();
                     t.b = true; t.m1(0); t.b = false; t.m1b(); t.m1c();
                     t.b = true; t.m2(); t.b = false; t.m2b(); t.m2c();
                     t.bb = false; a.bb = true; t.m3(a);
                     t.bb = true; a.bb = false; t.m3b(a);
                     t.bb = false; a.bb = true; t.m3c(a);
                     t.bb = true; a.bb = false; t.m3d(a);
                     t.bb = false; a.bb = true; t.m3e(a);
                     t.bb = true; a.bb = false; t.m3f(a);
                  }
                }
                """
                ,"/tt/TestJava.java:13: JML writable clause is false for variable tt.TestJava.x"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:17: JML writable clause is false for variable tt.TestJava.x"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:26: JML writable clause is false for variable tt.TestJava.y"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:30: JML writable clause is false for variable tt.TestJava.y"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:38: JML writable clause is false for variable tt.TestJava.z"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"/tt/TestJava.java:42: JML writable clause is false for variable tt.TestJava.z"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"/tt/TestJava.java:50: JML writable clause is false for variable tt.TestJava.z"
                ,"/tt/TestJava.java:3: Associated declaration"
                );
    }
}
