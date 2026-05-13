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
public class racnew3 extends RacBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--rac-show-source=line");
    }

    /** Tests not_modified */
    @Test public void testNotModified1() {
        helpRacText("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                    public static void main(String... args) {
                       m(3);
                    }
                    public static void m(int i) {
                       i = 3;
                       //@ assert \\not_modified(i);
                       i = 4;
                       //@ assert \\not_modified(i); // FAILS
                    }
                }
                """
                ,"/tt/TestJava.java:10: JML assertion is false"
        );
    }

    /** Tests not_modified */
    @Test public void testNotModified2() {
        helpRacText("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                    int f = 5;
                    public static void main(String... args) {
                       (new TestJava()).m(3,2);
                    }
                    public void m(int i, int j) {
                       i = 4;
                       //@ assert \\not_modified(j,this.f,f);
                       f=6;
                       //@ assert \\not_modified(this.f); // FAILS
                    }
                }
                """
                ,"/tt/TestJava.java:11: JML assertion is false"

        );
    }

    /** Tests not_modified */
    @Test public void testNotModified3() {
        helpRacText("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                    int f = 5;
                    public static void main(String... args) {
                       (new TestJava()).m(3,2);
                    }
                    public void m(int i, int j) {
                       i = 4;
                       //@ assert \\not_modified(j,this.f,f);
                       f=6;
                       //@ assert \\not_modified(f); // FAILS
                    }
                }
                """
                ,"/tt/TestJava.java:11: JML assertion is false"

        );
    }

    /** Tests not_modified */
    @Test public void testNotModified4() {
        helpRacText("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                    int f = 5;
                    public static void main(String... args) {
                       (new TestJava()).m(new int[]{1,2},7);
                    }
                    public void m(int[] a, int j) {
                       j = 4;
                       //@ assert \\not_modified(a[0]);
                       a[0]=10;
                       //@ assert \\not_modified(a[0]); // FAILS
                    }
                }
                """
                ,"/tt/TestJava.java:11: JML assertion is false"
        );
    }


    // FIXME - need tests for X.f X.* o.* a[*] a[1..3] a[1..]

    @Test
    public void testCast() {
        addOptions("--code-math=safe","--spec-math=safe");
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static double d;
                  public static float f;
                  public static long l;
                  public static int i;
                  public static short s;
                  public static char c;
                  public static byte b;
                    public static void main(String... args) {
                       i = 6; m0();
                       i = 100000; m0bad();
                    }
                  //@ requires i == 6;
                  //@ modifies \\everything;
                  public static void m0() {
                    s = (short)i;
                    //@ assert s == i; // OK
                    b = (byte)i;
                    //@ assert b == i; // OK // Line 20
                    c = (char)i;
                    //@ assert c == i; // OK
                    l = (long)i;
                    //@ assert l == i; // OK
                    int ii = (int)i;
                    //@ assert ii == i; // OK
                    //@ assert i == (short)i;
                    //@ assert i == (long)i;
                    //@ assert i == (char)i;
                    //@ assert i == (byte)i;
                    //@ assert i == (int)i;
                  }
                  //@ requires i == 100000;
                  //@ modifies \\everything;
                  public static void m0bad() {
                    s = (short)i;
                    //@ assert s == i; // BAD // Line 37
                    b = (byte)i;
                    //@ assert b == i; // BAD
                    c = (char)i;
                    //@ assert c == i; // BAD
                    l = (long)i;
                    //@ assert l == i; // OK
                    int ii = (int)i;
                    //@ assert ii == i; // OK
                    //@ assert i == (short)i; // BAD // Line
                    //@ assert i == (long)i;
                    //@ assert i == (char)i;
                    //@ assert i == (byte)i;
                    //@ assert i == (int)i;
                  }
                }
                """
                ,"/tt/TestJava.java:36: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:37: JML assertion is false"
                ,"/tt/TestJava.java:38: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:39: JML assertion is false"
                ,"/tt/TestJava.java:40: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:41: JML assertion is false"
                ,"/tt/TestJava.java:46: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:46: JML assertion is false"
                ,"/tt/TestJava.java:48: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:48: JML assertion is false"
                ,"/tt/TestJava.java:49: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:49: JML assertion is false"
                );
    }


    @Test
    public void testCast1() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static void main(String... args) {
                       m0();
                    }
                  public static void m0() {
                    {/*@ nullable */ Short s = null;
                    try { //@ assert 0 == (short)s;
                } catch (NullPointerException e) {}
                    try { short d = (Short)null; //@ forbid // Lines 10-11
                } catch (NullPointerException e) {}
                    }
                    {/*@ nullable */ Long s = null;
                    try { //@ assert 0 == (long)s;
                } catch (NullPointerException e) {}
                    try { long d = (Long)null; //@ forbid
                } catch (NullPointerException e) {}
                    }
                    {/*@ nullable */ Byte s = null;
                    try { //@ assert 0 == (byte)s;
                } catch (NullPointerException e) {}
                    try { byte d = (Byte)null; //@ forbid
                } catch (NullPointerException e) {}
                    }
                    {/*@ nullable */ Integer s = null;
                    try { //@ assert 0 == (int)s;
                } catch (NullPointerException e) {}
                    try { int d = (Integer)null; //@ forbid
                } catch (NullPointerException e) {}
                    }
                    {/*@ nullable */ Character s = null;
                    try { //@ assert 0 == (char)s;
                } catch (NullPointerException e) {}
                    try { char d = (Character)null; //@ forbid
                } catch (NullPointerException e) {}
                    }
                    {/*@ nullable */ Float s = null;
                    try { //@ assert 0 == (float)s;
                } catch (NullPointerException e) {}
                    try { float d = (Float)null; //@ forbid
                } catch (NullPointerException e) {}
                    }
                    {/*@ nullable */ Double s = null;
                    try { //@ assert 0 == (double)s;
                } catch (NullPointerException e) {}
                    try { double d = (Double)null;//@ forbid
                } catch (NullPointerException e) {}
                    }
                    {/*@ nullable */ Boolean s = null;
                    try { //@ assert (boolean)s;
                } catch (NullPointerException e) {}
                    try { boolean d = (Boolean)null;//@ forbid
                } catch (NullPointerException e) {}
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:8: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:10: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:14: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:16: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:20: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:22: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:26: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:28: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:32: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:34: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:38: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:40: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:44: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:46: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:50: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:52: JML Attempt to unbox a null object"
                );
    }


    @Test
    public void testCast2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static void main(String... args) {
                       m1();
                    }
                  public static void m1() {
                    short s = (short)9;
                    //@ assert 9 == (Short)s;
                  }
                }
                """
                );
    }

    @Test
    public void testVarargs() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static void main(String... args) {
                       m1(args);
                       m1();
                       m1("a");
                       m1("a","b");
                    }
                  //@ requires args.length >= 0;
                  //@ ensures args.length == \\result;
                  public static int m1(String ... args) {
                    return args.length;
                  }
                }
                """
                );
    }

    @Test
    public void testTryResources1() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also assignable TestJava.flag;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR r = new RR()){
                       flag = 2;
                       //@ assert TestJava.flag == 2;
                    }
                    //@ assert TestJava.flag == 1;
                  }
                  public static void main(String ... args) {
                    mmm();
                  }
                }
                """
                );

    }

    // If RR() throws an exception, flag == 0
    // If close exits normally, flag == 1
    // If close throws an exception, flag == 10
    @Test public void testTryResources1x() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       /*@ pure */ public RR(){}
                       //@ also assignable TestJava.flag;
                       //@ ensures TestJava.flag == 1;
                       //@ signals (Exception e) TestJava.flag == 10;
                       public void close() { TestJava.flag = 1; }
                    }

                   //@ requires flag == 0;
                   //@ assignable flag;
                   public static void mmm() {
                       //@ assert TestJava.flag == 0;
                       try {
                           try (RR r = new RR()){
                               flag = 2;
                              //@ assert TestJava.flag == 2;
                           }
                       } catch (Exception eee) {
                          //@ assert (\\lbl FLAG TestJava.flag) == 0 || TestJava.flag == 1|| TestJava.flag == 10;
                       }
                   }

                   public static void main(String ... args) {
                       mmm();
                   }
                }
                """
                );
    }

    // If RR() throws an exception, mmm exits exceptionally
    @Test public void testTryResources1a() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also assignable TestJava.flag;
                       //@ ensures TestJava.flag == 1;
                       //@ signals (Exception e) TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR r = new RR()){
                       flag = 2;
                       //@ assert TestJava.flag == 2;
                    }
                    //@ assert TestJava.flag == 1;
                    //@ assert TestJava.flag == 100; // ERROR - line 19
                  }
                  public static void main(String ... args) {
                    mmm();
                  }
                }
                """
                ,"/tt/TestJava.java:19: JML assertion is false"
                );
    }

    // Checks that close calls execute in reverse order
    @Test public void testTryResources2() {
        addOptions("--rac-check-assumptions");
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                    public static class RR2 implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag;
                       //@ ensures TestJava.flag == 2;
                       public void close() { TestJava.flag = 2; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR2 r = new RR2(); RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                    }
                    //@ assert TestJava.flag == 2;
                    //@ assert TestJava.flag == 200; // ERROR - line 25
                  }
                  public static void main(String ... args) {
                    mmm();
                  }
                }
                """
                ,"/tt/TestJava.java:25: JML assertion is false"
                );
    }

    // Checks the class of the resulting exception when try body and close calls throw exceptions
    @Test public void testTryResources2b() {
        addOptions("--rac-check-assumptions");
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static class EE extends Exception {  /*@ public normal_behavior ensures true; */public EE() {}}
                    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}
                    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}
                    public static class EE3 extends EE {/*@ public normal_behavior ensures true; */public EE3() {}}
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       /*@ public normal_behavior ensures true; */ public RR() {}
                       //@ also public exceptional_behavior
                       //@ assignable TestJava.flag;
                       //@ signals_only EE1;
                       //@ signals (Exception e) TestJava.flag == 1;
                       public void close() throws EE { TestJava.flag = 1; throw new EE1(); }
                    }
                    public static class RR2 implements AutoCloseable {
                       /*@ public normal_behavior ensures true; */ public RR2() {}
                       //@ also public exceptional_behavior
                       //@ assignable TestJava.flag;
                       //@ signals_only EE2;
                       //@ signals (Exception e) TestJava.flag == 2;
                       public void close() throws EE { TestJava.flag = 2; throw new EE2(); }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm(boolean b) { // Line 26
                    //@ assert TestJava.flag == 0;
                    try {
                      if (b) try (RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                       throw new EE3();
                      }
                      //@ assert TestJava.flag == 111; // not feasible - so not checked in RAC
                    } catch (EE e) {
                      //@ assert TestJava.flag == 1;
                       //@ assert e instanceof EE3 ; // Line 37
                      //@ assert TestJava.flag == 100;
                    }
                  }
                  public static void main(String ... args) {
                    mmm(true);
                  }
                }
                """
                ,"/tt/TestJava.java:38: JML assertion is false"
                );
    }

    // Checks the class of the resulting exception when try body and close calls throw exceptions
    @Test public void testTryResources2c() {
        addOptions("--rac-check-assumptions");
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static class EE extends RuntimeException {  /*@ public normal_behavior ensures true; */public EE() {}}
                    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}
                    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}
                    public static class EE3 extends EE {/*@ public normal_behavior ensures true; */public EE3() {}}
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       /*@ public normal_behavior ensures true; */ public RR() {}
                       //@ also public exceptional_behavior
                       //@ assignable TestJava.flag;
                       //@ signals_only EE1;
                       //@ signals (Exception e) TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; throw new EE1(); }
                    }
                    public static class RR2 implements AutoCloseable {
                       /*@ public normal_behavior ensures true; */ public RR2() {}
                       //@ also public exceptional_behavior
                       //@ assignable TestJava.flag;
                       //@ signals_only EE2;
                       //@ signals (Exception e) TestJava.flag == 2;
                       public void close() { TestJava.flag = 2; throw new EE2(); }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm(boolean b) { // Line 26
                    //@ assert TestJava.flag == 0;
                    try {
                      if (b) try (RR2 r = new RR2(); RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                       throw new EE3();
                      }
                      //@ assert TestJava.flag == 222; // not feasible - so not checked in RAC
                    } catch (EE1 | EE2 | EE3 e) {
                       //@ assert e instanceof EE3 ; // Line 36
                       //@ assert flag == 2;
                       //@ assert flag == 100; // Error
                    }
                  }
                  public static void main(String ... args) {
                    mmm(true);
                  }
                }
                """
                ,"/tt/TestJava.java:38: JML assertion is false"
                );
    }

    // Checks the class of the resulting exception when close calls throw exceptions, but not the try body
    @Test public void testTryResources2a() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static class EE extends Exception {  /*@ public normal_behavior ensures true; */public EE() {}}
                    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}
                    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       /*@ public normal_behavior ensures true; */ public RR() {}
                       //@ also public exceptional_behavior
                       //@ assignable TestJava.flag;
                       //@ signals_only EE1;
                       //@ signals (Exception e) TestJava.flag == 1;
                       public void close() throws EE1 { TestJava.flag = 1; throw new EE1(); }
                    }
                    public static class RR2 implements AutoCloseable {
                       /*@ public normal_behavior ensures true; */ public RR2() {}
                       //@ also public exceptional_behavior
                       //@ assignable TestJava.flag;
                       //@ signals_only EE2;
                       //@ signals (Exception e) TestJava.flag == 2;
                       public void close() throws EE2 { TestJava.flag = 2; throw new EE2(); }
                    }
                  //@ requires flag == 0; // Line 23
                  //@ assignable flag;
                  public static void mmm() { // Line 25
                    //@ assert TestJava.flag == 0;
                    try {
                      try (RR2 r = new RR2(); RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                      }
                      //@ assert TestJava.flag == 222; // Not feasible - so not checked in RAC
                    } catch (EE e) {
                       //@ assert TestJava.flag == 2; // Line 34 // Should be OK
                       //@ assert e instanceof EE1; // Line 35 // Should be OK
                    }
                  }
                  public static void main(String ... args) {
                    mmm();
                  }
                }
                """
                );
    }

    // Check that finally block of try encloses declarations and calls to close
    @Test public void testTryResources3() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                    } finally {
                      flag = 2;
                    }
                    //@ assert TestJava.flag == 2;
                  }
                  public static void main(String ... args) {
                    mmm();
                  }
                }
                """
                );
    }

    // If RR() throws an exception, then catch block will execute
    @Test public void testTryResources4() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm() {
                    boolean normal = true;
                    //@ assert TestJava.flag == 0;
                    try (RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                    } catch (Exception e) {
                      flag = 2;
                      normal = false;
                    }
                    //@ assert normal ==> flag == 1;
                    //@ assert !normal ==> flag == 2;
                  }
                  public static void main(String ... args) {
                    mmm();
                  }
                }
                """
                );
    }

    @Test public void testTryResources4a() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                       throw new Exception();
                    } catch (Exception e) {
                      flag = 2;
                    }
                    //@ assert TestJava.flag == 2; // FIXME - should not be able to skip the catch block
                  }
                  public static void main(String ... args) {
                    mmm();
                  }
                }
                """
                );
    }

    @Test public void testTryResources4b() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also assignable TestJava.flag;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                       throw new Exception();
                    } catch (Exception e) {
                      flag = 2;
                    }
                    //@ assert TestJava.flag == 2; // FIXME - should not be able to skip the catch block
                  }
                  public static void main(String ... args) {
                    mmm();
                  }
                }
                """
                );
    }

    // No resource - executes the catch block
    @Test public void testTryResources4c() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm() {
                    //@ assert TestJava.flag == 0;
                    try {
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                       throw new Exception();
                    } catch (Exception e) {
                      flag = 2;
                    }
                    //@ assert TestJava.flag == 2;
                  }
                  public static void main(String ... args) {
                    mmm();
                  }
                }
                """
                );
    }

    // Checks that the outer finally block is last to execute
    @Test public void testTryResources5() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also assignable TestJava.flag;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                    } catch (Exception e) {
                      flag = 2;
                    } finally {
                      flag = 5;
                    }
                    //@ assert TestJava.flag == 5;
                  }
                  public static void main(String ... args) {
                    mmm();
                  }
                }
                """
                );
    }

    // Java 9+ expression resource: single variable passed as resource.
    // Verifies that close() is called after normal exit from the try body.
    @Test public void testTryResourcesIdentifier1() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also assignable TestJava.flag;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm() {
                    RR r = new RR();
                    //@ assert TestJava.flag == 0;
                    try (r) {
                       flag = 2;
                       //@ assert TestJava.flag == 2;
                    }
                    //@ assert TestJava.flag == 1;
                    //@ assert TestJava.flag == 100; // ERROR
                  }
                  public static void main(String ... args) {
                    mmm();
                  }
                }
                """
                ,"/tt/TestJava.java:19: JML assertion is false"
                );
    }

    // Java 9+ expression resource: two variables listed in one try statement.
    // Verifies that both close() calls execute in reverse declaration order.
    @Test public void testTryResourcesIdentifierMultiple() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                    public static class RR2 implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag;
                       //@ ensures TestJava.flag == 2;
                       public void close() { TestJava.flag = 2; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm() {
                    RR2 r2 = new RR2();
                    RR r = new RR();
                    //@ assert TestJava.flag == 0;
                    try (r2; r) {
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                    }
                    //@ assert TestJava.flag == 2;
                    //@ assert TestJava.flag == 200; // ERROR
                  }
                  public static void main(String ... args) {
                    mmm();
                  }
                }
                """
                ,"/tt/TestJava.java:27: JML assertion is false"
                );
    }

    // Two identifier resources; the second (first to close) throws.
    // In try(r2; r): r closes first (throws), r2 closes second (sets flag=2).
    // Confirms the first resource (r2) is still closed despite r throwing.
    @Test public void testTryResourcesIdentifierSecondCloseThrows() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       public void close() { throw new RuntimeException(); }
                    }
                    public static class RR2 implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag;
                       //@ ensures TestJava.flag == 2;
                       public void close() { TestJava.flag = 2; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm() {
                    RR r = new RR();
                    RR2 r2 = new RR2();
                    try {
                      try (r2; r) {
                         flag = 3;
                         //@ assert TestJava.flag == 3;
                      }
                    } catch (Exception e) {
                      //@ assert TestJava.flag == 2;
                      //@ assert TestJava.flag == 100; // ERROR - confirms we reached catch with flag==2
                    }
                  }
                  public static void main(String ... args) {
                    mmm();
                  }
                }
                """
                ,"/tt/TestJava.java:25: JML assertion is false"
                );
    }

    // Java 9+ expression resource: close() is still called when the body throws.
    @Test public void testTryResourcesIdentifierException() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public static void mmm() {
                    RR r = new RR();
                    //@ assert TestJava.flag == 0;
                    try (r) {
                       flag = 3;
                       throw new Exception();
                    } catch (Exception e) {
                       flag = 2;
                    }
                    //@ assert TestJava.flag == 2;
                  }
                  public static void main(String ... args) {
                    mmm();
                  }
                }
                """
                );
    }

    @Test
    public void testInstanceOfA() {
        helpRacText("tt.TestJava",
                """
                package tt;
                class A {}
                public class TestJava extends A {
                  public int k;
                  //@ requires a instanceof TestJava && ((TestJava)a).k == 42;
                  public void m(A a) {
                    if (a instanceof TestJava t) {
                       //@ check t.k == 42;
                       //@ check t.k == 43; // ERROR
                    }
                  }
                  public static void main(String... args) { var t = new TestJava(); t.k = 42; t.m(t); }
                }
                """
                ,"/tt/TestJava.java:9: verify: JML assertion is false"
                );
    }

    @Test
    public void testInstanceOfB() {
        helpRacText("tt.TestJava",
                """
                package tt;
                class A {}
                public class TestJava extends A {
                  public int k;
                  //@ requires a instanceof TestJava tt && tt.k == 42;
                  public void m(A a) {
                    if (a instanceof TestJava t) {
                       //@ check t.k == 42;
                       //@ check t.k == 43; // ERROR
                    }
                  }
                  public static void main(String... args) { var t = new TestJava(); t.k = 42; t.m(t); }
                }
                """
                ,"/tt/TestJava.java:9: verify: JML assertion is false"
                );
    }

    @Test
    public void testInstanceOfC() {
        helpRacText("tt.TestJava",
                """
                package tt;
                class A {}
                public class TestJava extends A {
                  public int k;
                  //@ requires a instanceof TestJava tt && tt.k == 42;
                  public void m(A a) {
                    if (a instanceof TestJava t && t.k == 42) {
                        //@ unreachable; // ERROR is reachable
                    } else {
                        //@ unreachable; // OK
                    }
                  }
                  public static void main(String... args) { var t = new TestJava(); t.k = 42; t.m(t); }
                }
                """
                ,"/tt/TestJava.java:8: verify: JML unreachable statement reached"
                );
    }

    @Test
    public void testInstanceOfD() {
        helpRacText("tt.TestJava",
                """
                package tt;
                class A {}
                public class TestJava extends A {
                  public int k;
                  public void m(A a) {
                    //@ check \\forall int i; i == 0; (a instanceof TestJava t && t.k == 42);
                  }
                  public static void main(String... args) { var t = new TestJava(); t.m(t); }
                }
                """
                ,"/tt/TestJava.java:6: verify: JML assertion is false"
                );
    }

    // -----------------------------------------------------------------------
    // Record constructor tests
    // -----------------------------------------------------------------------

    // Default (generated) canonical constructor: confirms fields equal the
    // constructor arguments at runtime.
    @Test
    public void testRecordDefaultConstructor() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    record Point(int x, int y) {}
                    public static void main(String... args) {
                        Point p = new Point(3, 4);
                        //@ assert p.x() == 3;
                        //@ assert p.y() == 4;
                        //@ assert p.x() == 100;  // ERROR - line 8
                    }
                }
                """
                ,"/tt/TestJava.java:8: JML assertion is false"
                );
    }

    // Compact constructor that reassigns x = 10 in the body.
    // Confirms that Lower.java assigns this.x = x (the new value 10)
    // and this.y = y (unchanged as 4) after the body runs.
    @Test
    public void testRecordCompactConstructorWithReassignment() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    record Point(int x, int y) {
                        Point {
                            x = 10;  // reassign x in compact body
                        }
                    }
                    public static void main(String... args) {
                        Point p = new Point(3, 4);
                        //@ assert p.x() == 10;  // body set x=10, so field is 10
                        //@ assert p.y() == 4;   // y unchanged
                        //@ assert p.x() == 100;  // ERROR - line 12
                    }
                }
                """
                ,"/tt/TestJava.java:12: JML assertion is false"
                );
    }

    // -----------------------------------------------------------------------
    // Pattern-matching switch tests
    // -----------------------------------------------------------------------

    /** Binding pattern: case String s matches a String and binds it. */
    @Test
    public void testPatternSwitchBindingPattern() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ spec_pure
                    public static int classify(Object o) {
                        return switch (o) {
                            case String s -> s.length();
                            case Integer i -> i;
                            default -> -1;
                        };
                    }
                    public static void main(String... args) {
                        //@ assert classify("hello") == 5;
                        //@ assert classify(42) == 42;
                        //@ assert classify(3.14) == -1;
                        //@ assert classify("hello") == 99;  // ERROR - line 15
                    }
                }
                """
                ,"/tt/TestJava.java:15: JML assertion is false"
                );
    }

    /** Guarded pattern: when clause further constrains the match. */
    @Test
    public void testPatternSwitchGuardedPattern() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ spec_pure
                    public static String size(Object o) {
                        return switch (o) {
                            case Integer i when i > 100 -> "large";
                            case Integer i when i > 10  -> "medium";
                            case Integer i              -> "small";
                            default                     -> "other";
                        };
                    }
                    public static void main(String... args) {
                        //@ assert size(200).equals("large");
                        //@ assert size(50).equals("medium");
                        //@ assert size(5).equals("small");
                        //@ assert size("x").equals("other");
                        //@ assert size(50).equals("large");  // ERROR - line 17
                    }
                }
                """
                ,"/tt/TestJava.java:17: JML assertion is false"
                );
    }

    /** Null case label: explicit null matching in switch. */
    @Test
    public void testPatternSwitchNullCase() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ spec_pure
                    public static String describe(/*@ nullable */Object o) {
                        return switch (o) {
                            case null    -> "nothing";
                            case String s -> s;
                            default      -> "other";
                        };
                    }
                    public static void main(String... args) {
                        //@ assert describe(null).equals("nothing");
                        //@ assert describe("hi").equals("hi");
                        //@ assert describe(42).equals("other");
                        //@ assert describe(null).equals("something");  // ERROR - line 15
                    }
                }
                """
                ,"/tt/TestJava.java:15: JML assertion is false"
                );
    }

    /** Sealed interface with binding patterns — exhaustive switch. */
    @Test
    public void testPatternSwitchSealedInterface() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    sealed interface Shape permits Circle, Rect {}
                    record Circle(double r) implements Shape {}
                    record Rect(double w, double h) implements Shape {}
                    //@ spec_pure
                    public static String name(Shape s) {
                        return switch (s) {
                            case Circle c -> "circle";
                            case Rect r   -> "rect";
                        };
                    }
                    public static void main(String... args) {
                        var s = new Circle(1.0);
                        //@ assert name(s).equals("circle");
                        var r = new Rect(2.0, 3.0);
                        //@ assert name(r).equals("rect");
                        var c = new Circle(1.0);
                        //@ assert name(c).equals("rect");  // ERROR - line 19
                    }
                }
                """
                ,"/tt/TestJava.java:19: JML assertion is false"
                );
    }

    /** Nested record patterns: matching Add(Lit(a), Lit(b)) requires two levels
     *  of destructuring — the outer Add and the inner Lit components. */
    @Test
    public void testPatternSwitchNestedRecordPattern() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    sealed interface Expr permits Lit, Add {}
                    record Lit(int v) implements Expr {}
                    record Add(Expr left, Expr right) implements Expr {}
                    //@ spec_pure
                    public static int eval(Expr e) {
                        return switch (e) {
                            case Add(Lit(int a), Lit(int b)) -> a + b;
                            case Add(Lit(int a), Add(Lit(int b), Lit(int c))) -> a + b + c;
                            case Lit(int v) -> v;
                            default -> -1;
                        };
                    }
                    public static void main(String... args) {
                        var v = eval(new Lit(7));
                        //@ assert v == 7;
                        var a = eval(new Add(new Lit(3), new Lit(4)));
                        //@ assert a == 7;
                        var b = eval(new Add(new Lit(1), new Add(new Lit(2), new Lit(3))));
                        //@ assert b == 6;
                        var c = eval(new Add(new Lit(3), new Lit(4)));
                        //@ assert c == 10;  // ERROR - line 23
                    }
                }
                """
                ,"/tt/TestJava.java:23: JML assertion is false"
                );
    }

    /** Record pattern destructuring in switch expression. */
    @Test
    public void testPatternSwitchRecordPattern() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    record Point(int x, int y) {}
                    //@ pure
                    public static int sum(Object o) {
                        return switch (o) {
                            case Point(int x, int y) -> x + y;
                            default -> -1;
                        };
                    }
                    public static void main(String... args) {
                        int k = sum(new Point(3, 4));
                        //@ assert k == 7;
                        k = sum(new Point(0, 0));
                        //@ assert k == 0;
                        k = sum("not a point");
                        //@ assert k == -1;
                        k = sum(new Point(3, 4));
                        //@ assert k == 10;  // ERROR - line 19
                    }
                }
                """
                ,"/tt/TestJava.java:19: JML assertion is false"
                );
    }
}
