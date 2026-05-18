package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.*;

/** These tests exercise the RAC checking.  They compile a test class
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racnew2 extends RacBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--code-math=java","--spec-math=java");;
        addOptions("--rac-show-source=line");
        // Tests presume --nonnull-by-default
    }

    /** Tests a copying modifiers and annotations */
    // We really need to inspect the output to see that the result is OK. But at least this tests that it does not crash
    @Test public void testMods() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                import java.lang.annotation.*;
                @Retention(RetentionPolicy.RUNTIME)
                @interface A { }
                public class TestJava {
                  public static void main(String... args) {}
                }
                """
        );
    }

    @Test public void testMods2() {
        expectedExit = 1;
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                import java.lang.annotation.*;
                public class TestJava {
                    @NonNull  protected void m() {}
                    public static void main(String... args) {}
                }
                """
                //,"/tt/TestJava.java:5: error: annotation interface not applicable to this kind of declaration",5
                ,"/tt/TestJava.java:5: error: the type modifier/annotation is not permitted on a primitive type: void",5
        );
    }

    @Test public void testMethodCall() {
        helpRacText("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                import java.lang.annotation.*;
                public class TestJava {
                  //@ ensures \\result > 0;
                  public static int m(int i) { return i; }
                  public static void main(String... args) {
                    System.out.println("START");
                    int k = m(1);
                    System.out.println("MID");
                    k += 5 + m(-1);
                    System.out.println("END");
                  }
                }
                """
                ,"START"
                ,"MID"
                ,"/tt/TestJava.java:6: verify: JML postcondition is false"
                ,"/tt/TestJava.java:5: verify: Associated declaration: /tt/TestJava.java:6:"
                ,"/tt/TestJava.java:11: verify: JML postcondition is false"
                ,"/tt/TestJava.java:5: verify: Associated declaration: /tt/TestJava.java:11:"
                ,"END"
        );
    }

    /** Tests new array */
    @Test public void testNewArray() {  // FIXME - improve error message when String.equals includes its model methods for RAC
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    String[] a = new String[]{"abc","def"};
                    int i = a.length;
                    //@ assert i == 2;
                    String[][] aa = new String[][]{{"abc","defz"},{"g","h","i"}};
                    i = aa.length;
                    boolean b = aa[1][0].equals("g");
                    //@ assert i == 2;
                    //@ assert aa[1].length == 3;
                    //@ assert (new int[]{1,2,3}).length == 3;
                    //@ assert (new int[]{1,2,3})[1] == 2;
                    String[][] aaa = new String[1][2];
                    //@ assert aaa.length == 1;
                    //@ assert aaa[0].length == 2;
                    //@ assert aaa[0][0] == null;
                    System.out.println("END");
                  }
                }
                """
                ,"END"
        );
    }

    /** Tests new array */
    @Test public void testNewArray2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    int[] x = new int[3];
                    //@ assert x.length == 3;
                    //@ assert x[0] == 0;
                    String[] a = {"abc","def"};
                    int i = a.length;
                    //@ assert i == 2;
                    String[][] aa = {{"abc","defz"},{"g","h","i"}};
                    i = aa.length;
                    boolean b = aa[1][0].equals("g");
                    //@ assert i == 2;
                    //@ assert aa[1].length == 3;
                    String[][] aaa = new String[1][2];
                    //@ assert aaa.length == 1;
                    //@ assert aaa[0].length == 2;
                    //@ assert aaa[0][0] == null;
                    System.out.println("END");
                  }
                }
                """
                ,"END"
        );
    }

    /** Tests new object */
    @Test public void testNewObject() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    TestJava a = new TestJava();
                    int i = a.m(10);
                    //@ assert i == 11;
                    TestJava aa = new TestJava() { public int m(int i) { return i + 2; } } ;
                    i = aa.m(10);
                    //@ assert i == 12;
                    System.out.println("END");
                  }
                  public int m(int i) { return i + 1; }
                }
                """
                ,"END"
        );
    }

    /** Tests new object in JML */
    @Test public void testNewObject2() {
        expectedExit = 1;
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    // @ assert (new TestJava()).m(15) == 16;
                    //@ assert (new TestJava() { public pure int m(int i) { return i + 2; } }).m(15) == 17;
                    System.out.println("END");
                  }
                  /*@ pure */ public int m(int i) { return i + 1; }
                }
                """
                ,"/tt/TestJava.java:5: error: Object allocation is not permitted in specification expressions",17
                ,"END"
        );
    }

    /** Tests a simple try-finally block */
    @Test public void testTry() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    int i;
                    try { i = 0; } finally { i = 1; }
                    //@ assert i == 1;
                    System.out.println("END");
                  }
                }
                """
                ,"END"
        );
    }

    /** Test skip statement */
    @Test public void testSkip() {
        helpRacText("tt.A",
                """
                package tt;
                class A {
                  public static void main(String[] args) {
                    int i ;;; i = 9;;;; //@ assert i == 9;
                  }
                }
                """
                );
    }

    /** Test synchronized statement with this */
    @Test public void testSynchronized() {
        helpRacText("tt.A",
                """
                package tt;
                class A {
                  public static void main(String[] args) { new A().m(); }
                  public void m() {
                    int i;
                    synchronized (this) { i = 0; }
                  }
                }
                """
                );
    }

    /** Test synchronized statement with null lock */
    @Test public void testSynchronized2() {
        expectedRACExit = 1;
        helpRacText("tt.A",
                """
                package tt;
                class A {
                    public static void main(String[] args) throws Exception {
                        new A().m();
                    }
                    public void m() throws RuntimeException {
                        /*@ nullable*/ Object o = null;
                        int i;
                        synchronized (o) { i = 0; }
                    }
                }
                """
                ,"/tt/A.java:9: verify: JML An object is unexpectedly null"
                ,"Exception in thread \"main\" java.lang.NullPointerException: Cannot enter synchronized block because \"<local4>\" is null"
                ,"\tat tt.A.m(A.java:9)"
                ,"\tat tt.A.main(A.java:4)"
                );
    }


    /** Tests a simple try-throw-catch block */
    @Test public void testThrow() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    int i;
                    try { i = 0; throw new RuntimeException(); } catch (RuntimeException e) { i = 1; }
                    //@ assert i == 1;
                    System.out.println("END");
                  }
                }
                """
                ,"END"
        );
    }


    /** Tests binary operators */
    // FIXME - add equalities among various types, && || & ^ | logical and bit
    // FIXME - test JML binary
    @Test public void testBinary() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    int a=5,b=6,c;
                    boolean f, e= true,d=false;
                    c = a + b;
                    //@ assert c == a + 6;
                    c = a - b;
                    //@ assert a - c == 6;
                    c = a * b;
                    //@ assert b == c / 5;
                    c = b / (a - 3);
                    //@ assert b == c * 2;
                    c = b % a;
                    //@ assert a % b == a && c == 1;
                    f = a < b ; // FIXME - this line causes a problem
                    //@ assert  f && a <= b;
                    f = a <= b ;
                    //@ assert  f && a < b;
                    f = a > b ;
                    //@ assert  !f && a >= b;
                    f = a >= b ;
                    //@ assert  !f && a > b;
                    System.out.println("END");
                  }
                }
                """
                ,"/tt/TestJava.java:21: JML assertion is false"
                ,"/tt/TestJava.java:23: JML assertion is false"
                ,"END"
        );
    }

    /** Tests binary operators */
    @Test public void testShift() {
        addOptions("--code-math=safe");
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    int a=5,b=6,c=100;
                    int d = a << b;
                    d = a << c; // ERROR
                    d = a >> b;
                    d = a >> c; // ERROR
                    d = a >>> b;
                    d = a >>> c; // ERROR
                    long e = 20L << b;
                    e = 20L << (b+40); // OK
                    e = 20L << c; // ERROR
                    System.out.println("END");
                  }
                }
                """
                ,"/tt/TestJava.java:6: JML shift amount is out of expected range"
                ,"/tt/TestJava.java:8: JML shift amount is out of expected range"
                ,"/tt/TestJava.java:10: JML shift amount is out of expected range"
                ,"/tt/TestJava.java:13: JML shift amount is out of expected range"
                ,"END"
        );
    }

    /** Tests binary operators */
    @Test public void testConditional() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    int a=5,b=6,c=100;
                    int d = a < 10 ? b + 3 : c-40;
                    System.out.println(d);
                    //@ assert (c > 4? a + 3 : b + 3) == 9; // ERROR
                    System.out.println("END");
                  }
                }
                """
                ,"9"
                ,"/tt/TestJava.java:7: JML assertion is false"
                ,"END"
        );
    }

    /** Tests unary operators */ // FIXME - test unary with expressions in ++ --
    @Test public void testUnary() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    int a=5,b=0,c=0;
                    boolean e=true,d=false;
                    b = a++;
                    //@ assert b+1 == a;
                    b = a--;
                    //@ assert b-1 == a;
                    c = a; b = ++a;
                    //@ assert b == a && c+1 == b;
                    b = --a;
                    //@ assert b == a && c == b;
                    b = -a;
                    //@ assert b == -5;
                    e = d ;
                    //@ assert  !d;
                    System.out.println("END");
                  }
                }
                """
                ,"END"
        );
    }

    /** Tests parens operators */
    @Test public void testParens() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    int a=5,b=6,c=0;
                    boolean e=true,d=false;
                    c = (a*b)+3*b-2*(a-(((b))));
                    //@ assert ((((c) == 50)));
                    c = b / (((a)));
                    System.out.println("END");
                  }
                }
                """
                ,"END"
        );
    }



    /** Tests switch statement */
    // Unlabelled breaks are not allowed for blocks
    @Test public void testBreak() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(0);
                    m(2);
                    m(3);
                    m(5);
                    System.out.println("END");
                  }
                  static void m(int i) {
                    out: {
                       in: {
                            System.out.print(i + "A");
                            if (i == 2) break in;
                            if (i == 3) break out;
                            System.out.print("B");
                           }
                            System.out.print("C");
                            if (i == 5) break out;
                            System.out.print("D");
                        }
                            System.out.println("Z");
                  }
                }
                """
                ,"0ABCDZ"
                ,"2ACDZ"
                ,"3AZ"
                ,"5ABCZ"
                ,"END"
        );
    }

    // Unlabelled breaks are not allowed for blocks
    @Test public void testSimpleBreak() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(0);
                    m(2);
                    System.out.println("END");
                  }
                  static void m(int i) {
                       in: {
                            System.out.print(i + "A");
                            if (i == 2) break in;
                            System.out.print("B");
                           }
                            System.out.println("C");
                        }
                }
                """
                ,"0ABC"
                ,"2AC"
                ,"END"
        );
    }


    /** Tests type test and type cast expressions */
    @Test public void testTypeCast() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    Integer i = Integer.valueOf(10);
                    Object o = i;
                    Integer ii = (Integer)o;
                    System.out.println(ii);
                    System.out.println("END");
                  }
                }
                """
                ,"10"
                ,"END"
        );
    }

    /** Tests a bad cast */
    @Test public void testTypeCast2() {
        expectedRACExit = 1;
        addOptions("--rac-show-source=source");
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    Boolean i = Boolean.TRUE;
                    Object o = i;
                    Integer ii = (Integer)o;
                    System.out.println(ii);
                    System.out.println("END");
                  }
                }
                """
                ,"/tt/TestJava.java:6: JML A cast is invalid - from java.lang.Object to java.lang.Integer"
                ,"    Integer ii = (Integer)o;"
                ,"                 ^"
                ,"Exception in thread \"main\" java.lang.ClassCastException: class java.lang.Boolean cannot be cast to class java.lang.Integer (java.lang.Boolean and java.lang.Integer are in module java.base of loader 'bootstrap')"
                ,"\tat tt.TestJava.main(TestJava.java:6)"
        );
    }

    /** Tests a type test with a cast */
    @Test public void testTypeCast3() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    Boolean b = Boolean.TRUE;
                    Integer i = Integer.valueOf(10);
                    /*@ nullable */ Integer ii = null;
                    Object o = i;
                    if (o instanceof Integer) { ii = (Integer)o; }
                    o = b;
                    if (o instanceof Integer) { ii = (Integer)o; }
                    System.out.println(ii);
                    System.out.println("END");
                  }
                }
                """
                ,"10"
                ,"END"
        );
    }

    /** Test a type tests and casts in JML */
    @Test public void testTypeTest4() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    Boolean b = Boolean.TRUE;
                    Integer i = Integer.valueOf(10);
                    /*@ nullable */ Integer ii = null;
                    Object o = i;
                    //@ assert o instanceof Integer;
                    o = b;
                    //@ assert o instanceof Integer;
                    System.out.println("END");
                  }
                }
                """
                ,"/tt/TestJava.java:10: JML assertion is false"
                ,"END"
        );
    }

    /** Test a type tests and casts in JML */
    @Test public void testTypeCast5() {
        expectedRACExit = 1;
        addOptions("--rac-show-source=line");
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    Boolean b = Boolean.TRUE;
                    Integer i = Integer.valueOf(10);
                    /*@ nullable */ Integer ii = null;
                    Object o = i;
                    //@ assert (Integer)o != null;
                    o = b;
                    //@ assert (Integer)o != null;
                    System.out.println("END");
                  }
                }
                """
                ,"/tt/TestJava.java:10: JML A cast is invalid - from java.lang.Object to java.lang.Integer"
                ,"Exception in thread \"main\" java.lang.ClassCastException: class java.lang.Boolean cannot be cast to class java.lang.Integer (java.lang.Boolean and java.lang.Integer are in module java.base of loader 'bootstrap')"
                ,"\tat tt.TestJava.main(TestJava.java:10)"
        );
    }

    /** Test a type tests and casts in JML */
    @Test public void testTypeCast6() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    Boolean b = Boolean.TRUE;
                    Integer i = Integer.valueOf(10);
                    /*@ nullable */ Integer ii = null;
                    Object o = i;
                    //@ assert o instanceof Integer && (Integer)o != null;
                    o = b;
                    //@ assert o instanceof Integer && (Integer)o != null;
                    System.out.println("END");
                  }
                }
                """
                ,"/tt/TestJava.java:10: JML assertion is false"
                ,"END"
        );
    }


    /** Tests the JML lbl lblpos and lblneg expressions */
    @Test public void testLbl() {
        addOptions("--spec-math=math");
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(null);
                    System.out.println("END");
                  }
                  static int i = 0;
                  static String n = "asd";
                  static void m(/*@nullable*/ Object o) {
                //@ assert (\\lbl STRING "def") != null;
                ++i; //@ assert (\\lbl SHORT (short)(i)) != 0;
                ++i; //@ assert (\\lbl LONG (long)(i)) != 0;
                ++i; //@ assert (\\lbl BYTE (byte)(i)) != 0;
                ++i; //@ assert (\\lbl INT (int)(i)) != 0;
                ++i; //@ assert (\\lbl FLOAT (float)(i)) != 0;
                ++i; //@ assert (\\lbl DOUBLE (double)(i)) != 0;
                //@ assert (\\lbl CHAR (char)(i+60) ) != 0;
                //@ assert (\\lbl BOOLEAN (i == 0)) ;
                //@ assert (\\lbl OBJECT o) == null;
                //@ assert (\\lbl NULL null) == null;
                //@ assert (\\lbl STRING "abc") != null;
                //@ assert (\\lblpos POST (i!=0));
                //@ assert !(\\lblpos POSF (i==0));
                //@ assert (\\lblneg NEGT (i!=0));
                //@ assert !(\\lblneg NEGF (i==0));
                //@ assert !(\\lblpos POST (i!=0));
                //@ assert (\\lblneg NEGF (i==0));
                  }
                }
                """
                ,"LABEL STRING = def"
                ,"LABEL SHORT = 1"
                ,"LABEL LONG = 2"
                ,"LABEL BYTE = 3"
                ,"LABEL INT = 4"
                ,"LABEL FLOAT = 5.0"
                ,"LABEL DOUBLE = 6.0"
                ,"LABEL CHAR = B"
                ,"LABEL BOOLEAN = false"
                ,"/tt/TestJava.java:18: JML assertion is false"
                ,"LABEL OBJECT = null"
                ,"LABEL NULL = null"
                ,"LABEL STRING = abc"
                ,"LABEL POST = true"
                ,"LABEL NEGF = false"
                ,"LABEL POST = true"
                ,"/tt/TestJava.java:26: JML assertion is false"
                ,"LABEL NEGF = false"
                ,"/tt/TestJava.java:27: JML assertion is false"
                ,"END"
                );

    }

    /** Tests the JML lbl expression when the argument is a literal */
    @Test public void testLblConst() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(null);
                    System.out.println("END");
                  }
                  static int i = 0;
                  static void m(/*@nullable*/ Object o) {
                //@ check (\\lbl OBJECT null) == null;
                //@ check (\\lbl INT 4) != 0;
                //@ check (\\lbl SHORT (short)(1)) != 0;
                //@ check (\\lbl LONG 2L) != 0;
                //@ check (\\lbl BYTE (byte)(3)) != 0;
                //@ check (\\lbl FLOAT 5.0f) != 0; // Line 10
                //@ check (\\lbl DOUBLE 6.0) != 0;
                //@ check (\\lbl CHAR 'a') != 0;
                //@ check (\\lbl BOOLEAN true) ;
                //@ check (\\lbl STRING "abc") != null;
                  }
                }
                """
                ,"LABEL OBJECT = null"
                ,"LABEL INT = 4"
                ,"LABEL SHORT = 1"
                ,"LABEL LONG = 2"
                ,"LABEL BYTE = 3"
                ,"LABEL FLOAT = 5.0"
                ,"LABEL DOUBLE = 6.0"
                ,"LABEL CHAR = a"
                ,"LABEL BOOLEAN = true"
                ,"LABEL STRING = abc"
                ,"END"
                );

    }

    /** A misc early test case for lbl expressions */
    @Test public void testLabel() {
        addOptions("--rac-show-source=source");
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  /*@ assignable \\everything; */
                  public static void main(String[] args) {
                    m(1);
                    m(0);
                    System.out.println("END");
                  }
                  static public int k = 0;
                  /*@ assignable \\everything; ensures (\\lbl ENS k == 1); */
                  static public void m(int i) {
                    System.out.println("i = " + i);
                    k = i;
                  }
                }
                """
                ,"i = 1"
                ,"LABEL ENS = true"
                ,"LABEL ENS = true"
                ,"i = 0"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:11: JML postcondition is false"
                ,"  static public void m(int i) {"
                ,"                     ^"
                ,"/tt/TestJava.java:10: Associated declaration: /tt/TestJava.java:11:"
                ,"  /*@ assignable \\everything; ensures (\\lbl ENS k == 1); */"
                ,"                              ^"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:6: JML postcondition is false"
                ,"    m(0);"
                ,"     ^"
                ,"/tt/TestJava.java:10: Associated declaration: /tt/TestJava.java:6:"
                ,"  /*@ assignable \\everything; ensures (\\lbl ENS k == 1); */"
                ,"                              ^"
                ,"END"
        );
    }

    /** A misc early test case for lbl expressions */
    @Test public void testLabel2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  /*@ assignable \\everything; */
                  public static void main(String[] args) {
                    m(1);
                    m(0);
                    System.out.println("END");
                  }
                  static public int k = 0;
                  /*@ assignable \\everything; ensures (\\lblneg ENS (\\lbl RES k) == 1); */
                  static public void m(int i) {
                    k = i;
                    return;
                  }
                }
                """
                ,"LABEL RES = 1"
                ,"LABEL RES = 1"
                ,"LABEL RES = 0"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:11: verify: JML postcondition is false"
                ,"/tt/TestJava.java:10: verify: Associated declaration: /tt/TestJava.java:11:"
                ,"LABEL RES = 0"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:6: verify: JML postcondition is false"
                ,"/tt/TestJava.java:10: verify: Associated declaration: /tt/TestJava.java:6:"
                ,"END"
        );
    }

    /** Checks one can do assignments in a model method. */
    @Test public void testModelMethod() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                   //@ ghost boolean k; set k = m(); assert k;
                   //@                  set k = m(); assert k;
                   System.out.println("END");
                  }
                  //@ ghost static int i = 0;
                  //@ ghost static int j = 0;
                  //@ model static boolean m() { j = 1; i+= 1; int k = 2; return i == 1; }
                }
                """
                ,"/tt/TestJava.java:5: JML assertion is false"
                ,"END"
        );
    }

    /** Checks select expressions. */
    @Test public void testSelect() {
        expectedRACExit = 1;
        helpRacText("tt.TestJava",
            """
            package tt;
                public class TestJava {
                    public static void main(String[] args) {
                        //@ assert a[0] == 0;
                        //@ assert b != null && b[0] == 0;
                        //@ assert b[0] == 0;
                        System.out.println(\"END\");
                    }
                static int[] a = { 0,1,2};
                static int /*@nullable*/[] b = null;
            }
            """
            ,"/tt/TestJava.java:5: JML assertion is false"
            ,"/tt/TestJava.java:6: JML A null object is dereferenced within a JML expression"
            ,"Exception in thread \"main\" java.lang.NullPointerException: Cannot read the array length because \"tt.TestJava.b\" is null"
            ,"\tat tt.TestJava.main(TestJava.java:6)"
        );
    }

    /** Checks select expressions. */
    @Test public void testSelect2() {
        expectedRACExit = 1;
        helpRacText("tt.TestJava",
            """
            package tt;
            public class TestJava {
                 public static void main(String[] args) {
                     System.out.println(a[1]);
                     System.out.println(b[1]);
                     System.out.println(\"END\");
                }
                static int[] a = { 0,1,2};
                static int /*@nullable*/[] b = null;
            }
            """
            ,"1"
            ,"/tt/TestJava.java:5: verify: JML A null object is dereferenced"
            ,"Exception in thread \"main\" java.lang.NullPointerException: Cannot read the array length because \"tt.TestJava.b\" is null"
            ,"\tat tt.TestJava.main(TestJava.java:5)"
        );
    }

    /** Checks a model class. */
    @Test public void testModelClass() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                   System.out.println(m(1));
                   //@ set System.out.println(p(new G()));
                   System.out.println("END");
                  }
                  static <T> T m(T i) { return i; }
                  //@ model static public class G {}
                  //@ model static int p(G i) { return 5; }
                }
                """
                ,"1"
                ,"5"
                ,"END"
        );
    }

    /** Checks generic method. */
    @Test public void testGenMethod() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                   System.out.println(m(1));
                   System.out.println("END");
                  }
                  static <T> T m(T i) { return i; }
                }
                """
                ,"1"
                ,"END"
        );
    }

    /** Checks generic method. */
    @Test public void testGenMethod2() {  // FIXME - this needs more investigation -- the type int seems to be used (e.g. in addImplicitCOnversion) in an expression i != null where I would expect it to have been converted to T
        helpRacText("tt.TestJava",
                """
                package tt;
                import java.util.*;
                public class TestJava {
                  public static void main(String[] args) {
                   System.out.println(m(1));
                   System.out.println("END");
                  }
                  static /*@nullable*/ <T> List<?> m(T i) { return null; }
                }
                """
                ,"null"
                ,"END"
        );
    }

    /** Checks generic classes. */
    @Test public void testGenClass() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                   System.out.println(m(1));
                   System.out.println(p(new G<Integer>()));
                   System.out.println("END");
                  }
                  static <T> T m(T i) { return i; }
                  static public class G<T> {}
                  static <T> int p(G<?> i) { return 5; }
                }
                """
                ,"1"
                ,"5"
                ,"END"
        );
    }

    // FIXME - uncomment or delete the following material
//    @Test public void testNoWarn() {
//        helpRacText("tt.A","package tt; public class A { \n"
//                +"static public int i = 0;  \n "
//                +"//@ ensures i == 0; \n "
//                +"static public void m(int j) { i = j; }  \n "
//                +"public static void main(String[] args) { \n"
//                +"m(1); \n"
//                +"System.out.println(\"MID\"); \n"
//                +"m(2); //@ nowarn Postcondition; \n"
//                +"System.out.println(\"MID\"); \n"
//                +"m(3); //@ nowarn; \n"
//                +"System.out.println(\"MID\"); \n"
//                +"m(4); //@ nowarn InvariantExit; \n"
//                +"System.out.println(\"MID\"); \n"
//                +"m(5); //@ nowarn InvariantExit,Postcondition; \n"
//                +"System.out.println(\"END\"); \n"
//                +"}}"
//                ,"/tt/A.java:4: JML postcondition is false"
//                ,"/tt/A.java:3: Associated declaration: /tt/A.java:4:"
//                ,"/tt/A.java:6: JML postcondition is false"
//                ,"/tt/A.java:3: Associated declaration: /tt/A.java:6:"
//                ,"MID"
//                ,"/tt/A.java:4: JML postcondition is false"
//                ,"/tt/A.java:3: Associated declaration: /tt/A.java:4:"
//                ,"MID"
//                ,"/tt/A.java:4: JML postcondition is false"
//                ,"/tt/A.java:3: Associated declaration: /tt/A.java:4:"
//                ,"MID"
//                ,"/tt/A.java:4: JML postcondition is false"
//                ,"/tt/A.java:3: Associated declaration: /tt/A.java:4:"
//                ,"/tt/A.java:12: JML postcondition is false"
//                ,"/tt/A.java:3: Associated declaration: /tt/A.java:12:"
//                ,"MID"
//                ,"/tt/A.java:4: JML postcondition is false"
//                ,"/tt/A.java:3: Associated declaration: /tt/A.java:4:"
//                ,"END"
//                );
//    }
//
//
//    @Test public void testNoWarn1() {
//        helpRacText("tt.A","package tt; public class A { \n"
//                +"//@ public invariant i == 0; \n "
//                +"public int i = 0;  \n "
//                +"void m(int j) { i = j; }  //@ nowarn InvariantExit; \n "
//                +"public static void main(String[] args) { \n"
//                +"new A().m(1); //@ nowarn InvariantExit, InvariantReenterCaller \n"
//                +"System.out.println(\"END\"); \n"
//                +"}}"
//                ,"END"
//                );
//    }
//
//    @Test public void testNoWarn2() {
//        helpRacText("tt.A","package tt; public class A { \n"
//                +"//@ public invariant i == 0; \n"
//                +"public int i = 0;  \n"
//                +"void m(int j) { i = j; }  //@ nowarn ; \n"
//                +"public static void main(String[] args) { \n"
//                +"new A().m(1); //@ nowarn \n"
//                +"System.out.println(\"END\"); \n"
//                +"}}"
//                ,"END"
//                );
//    }
//
//    @Test public void testNoWarn3() {
//        helpRacText("tt.A","package tt; public class A { \n"
//                +"//@ public invariant i == 0; \n "
//                +"public int i = 0;  \n "
//                +"void m(int j) { i = j; }  //@ nowarn Precondition ; \n "
//                +"public static void main(String[] args) { \n"
//                +"new A().m(1); \n"
//                +"System.out.println(\"END\"); \n"
//                +"}}"
//                ,"/tt/A.java:4: verify: JML invariant is false on leaving method tt.A.m(int)"
//                ,"/tt/A.java:2: verify: Associated declaration: /tt/A.java:4:"
//                ,"/tt/A.java:6: verify: JML invariant is false on leaving method tt.A.m(int), returning to tt.A.main(java.lang.String[])"
//                ,"/tt/A.java:2: verify: Associated declaration: /tt/A.java:6:"
//                ,"/tt/A.java:6: verify: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m(int))"
//                ,"/tt/A.java:2: verify: Associated declaration: /tt/A.java:6:"
//                ,"END"
//                );
//    }
//
//    @Test public void testNoWarn4() {
//        helpRacText("tt.A","package tt; public class A { \n"
//                +"//@ invariant i == 0; \n "
//                +"int i = 0;  \n "
//                +"void m(int j) { i = j; }  //@ nowarn Precondition, InvariantExit; \n "
//                +"public static void main(String[] args) { \n"
//                +"new A().m(1); //@ nowarn InvariantExit, InvariantReenterCaller ; \n"
//                +"System.out.println(\"END\"); \n"
//                +"}}"
//                ,"END"
//                );
//    }

    @Test public void testReceiver1() {
        helpRacText("tt.A",
                """
                package tt;
                public class A {
                public A(int k) { i = k; }
                 public int i;
                 /*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }
                 public static void main(String[] args) {
                   boolean z;
                A a = new A(1);
                A b = new A(2);
                z = a.m(1);
                z = b.m(2) && z;
                z = a.m(2) && z;
                System.out.println("END");
                }
                }
                """
                ,"/tt/A.java:12: JML precondition is false"
                ,"/tt/A.java:5: Associated declaration: /tt/A.java:12:"
                ,"/tt/A.java:5: JML precondition is false"
                ,"END"
                );
    }

    @Test public void testReceiver2() {
        helpRacText("tt.A",
                """
                package tt;
                public class A {
                /*@ assignable i; */ public A(int k) { i = k; }
                 static public int i;
                 /*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }
                 public static void main(String[] args) {
                   boolean z;
                A a = new A(1);
                A b = new A(2);
                a.m(1);
                b.m(2);
                a.m(2);
                System.out.println("END");
                }
                }
                """
                ,"/tt/A.java:10: JML precondition is false"
                ,"/tt/A.java:5: Associated declaration: /tt/A.java:10:"
                ,"/tt/A.java:5: JML precondition is false"
                ,"END"
                );
    }

    @Test public void testReceiver3() {
        helpRacText("tt.A",
                """
                package tt;
                public class A {
                /*@ assignable i; */ public A(int k) { i = k; }
                 static public int i;
                 /*@ requires i == j; ensures \\result; */ static public boolean m(int j) { return true; }
                 public static void main(String[] args) {
                   boolean z;
                A a = new A(1);
                A b = new A(2);
                z = A.m(1);
                z = A.m(2);
                z = A.m(2);
                System.out.println("END");
                }
                }
                """
                ,"/tt/A.java:10: JML precondition is false"
                ,"/tt/A.java:5: Associated declaration: /tt/A.java:10:"
                ,"/tt/A.java:5: JML precondition is false"
                ,"END"
                );
    }


    @Test public void testReceiver4() {
        helpRacText("tt.A",
                """
                package tt;
                public class A {
                //@ ensures i == k;
                 public A(int k) { i = k; }
                 public int i;
                public static void main(String[] args) {
                  boolean z;
                A a = new A(1);
                System.out.println("END");
                }
                }
                """
                ,"END"
                );
    }

    @Test public void testReceiver4bad() {
        helpRacText("tt.A",
                """
                package tt;
                public class A {
                //@ ensures i == 1;
                 public A(int k) { i = k; }
                 public int i;
                public static void main(String[] args) {
                  boolean z;
                A a = new A(1);
                A b = new A(2);
                System.out.println("END");
                }
                }
                """
                ,"/tt/A.java:4: JML postcondition is false"
                ,"/tt/A.java:3: Associated declaration: /tt/A.java:4:"
                ,"/tt/A.java:9: JML postcondition is false"
                ,"/tt/A.java:3: Associated declaration: /tt/A.java:9:"
                ,"END"
                );
    }

    @Test public void testLet() {
        helpRacText("tt.A",
                """
                package tt;
                public class A {
                //@ ensures (\\let int k = 1; \\result == k + i) ;
                 public static int m(int i) { return i + 1; }
                //@ ensures (\\let int k = 1; \\result == k - i) ;
                 public static int mm(int i) { return i + 1; }
                public static void main(String[] args) {
                m(1);
                mm(1);
                System.out.println("END");
                }
                }
                """
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/tt/A.java:5: Associated declaration: /tt/A.java:6:"
                ,"/tt/A.java:9: JML postcondition is false"
                ,"/tt/A.java:5: Associated declaration: /tt/A.java:9:"
                ,"END"
                );
    }

    @Test public void testLet2() {
        helpRacText("tt.A",
                """
                package tt;
                public class A {
                //@ ensures (\\let int k = 1, int j = k; \\result == j + i) ;
                 public static int m(int i) { return i + 1; }
                //@ ensures (\\let int k = 1, int j = k; \\result == j - i) ;
                 public static int mm(int i) { return i + 1; }
                public static void main(String[] args) {
                m(1);
                mm(1);
                System.out.println("END");
                }
                }
                """
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/tt/A.java:5: Associated declaration: /tt/A.java:6:"
                ,"/tt/A.java:9: JML postcondition is false"
                ,"/tt/A.java:5: Associated declaration: /tt/A.java:9:"
                ,"END"
                );
    }

    @Test public void testBoxingOnDeclaration() {
        helpRacText("tt.A",
                """
                package tt;
                public class A {
                public static void main(String[] args) {
                { Integer i = 6;
                int k = i;
                //@ assert k == i;
                }
                { Boolean i = true;
                boolean k = i;
                //@ assert k == i;
                }
                { Short i = 6;
                short k = i;
                //@ assert k == i;
                }
                { Long i = 6L;
                long k = i;
                //@ assert k == i;
                }
                { Byte i = 6;
                byte k = i;
                //@ assert k == i;
                }
                { Double i = 6.0;
                double k = i;
                //@ assert k == i;
                }
                { Float i = 6.0f;
                float k = i;
                //@ assert k == i;
                }
                { Character i = 6;
                char k = i;
                //@ assert k == i;
                }
                { Integer i = 6;
                int k = i;
                //@ assert k == i+1;
                }
                System.out.println("END");
                }
                }
                """
                ,"/tt/A.java:38: JML assertion is false"
                ,"END"
                );
    }

    @Test public void testBoxingOnNullDeclaration() {
        helpRacText("tt.A",
                """
                package tt;
                /*@ nullable_by_default*/
                public class A {
                public static void main(String[] args) {
                try { Integer i = null;
                int k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                try { Boolean i = null;
                boolean k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                try { Short i = null;
                short k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                try { Long i = null;
                long k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                try { Byte i = null;
                byte k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                try { Double i = null;
                double k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                try { Float i = null;
                float k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                try { Character i = null;
                char k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                System.out.println("END");
                }
                }
                """
                ,"/tt/A.java:6: JML Attempt to unbox a null object"
                ,"/tt/A.java:10: JML Attempt to unbox a null object"
                ,"/tt/A.java:14: JML Attempt to unbox a null object"
                ,"/tt/A.java:18: JML Attempt to unbox a null object"
                ,"/tt/A.java:22: JML Attempt to unbox a null object"
                ,"/tt/A.java:26: JML Attempt to unbox a null object"
                ,"/tt/A.java:30: JML Attempt to unbox a null object"
                ,"/tt/A.java:34: JML Attempt to unbox a null object"
                ,"END"
                );
    }

    @Test public void testBoxingOnAssignment() {  // In Java mode
        addOptions("--code-math=java");
        helpRacText("tt.A",
                """
                package tt;
                public class A {
                public static void main(String[] args) {
                { Integer i; int k; i = 6;
                 k = i;
                //@ assert k == i;
                }
                { Boolean i; boolean k; i = true;
                 k = i;
                //@ assert k == i;
                }
                { Short i; short k; i = 6;
                 k = i;
                //@ assert k == i;
                }
                { Long i; long k; i = 6L;
                 k = i;
                //@ assert k == i;
                }
                { Byte i; byte k; i = 6;
                 k = i;
                //@ assert k == i;
                }
                { Double i; double k; i = 6.0;
                 k = i;
                //@ assert k == i;
                }
                { Float i; float k; i = 6.0f;
                 k = i;
                //@ assert k == i;
                }
                { Character i; char k; i = 6;
                 k = i;
                //@ assert k == i;
                }
                { Integer i = 6;
                int k = i;
                //@ assert k == i+1;
                }
                System.out.println("END");
                }
                }
                """
                ,"/tt/A.java:38: JML assertion is false"
                ,"END"
                );
    }

    @Test public void testBoxingOnAssignmentMathMode() {
        addOptions("--code-math=math");
        helpRacText("tt.A",
                """
                package tt;
                public class A {
                public static void main(String[] args) {
                { Integer i; int k; i = 6;
                 k = i;
                //@ assert k == i;
                }
                { Boolean i; boolean k; i = true;
                 k = i;
                //@ assert k == i;
                }
                { Short i; short k; i = 6;
                 k = i;
                //@ assert k == i;
                }
                { Long i; long k; i = 6L;
                 k = i;
                //@ assert k == i;
                }
                { Byte i; byte k; i = 6;
                 k = i;
                //@ assert k == i;
                }
                { Double i; double k; i = 6.0;
                 k = i;
                //@ assert k == i;
                }
                { Float i; float k; i = 6.0f;
                 k = i;
                //@ assert k == i;
                }
                { Character i; char k; i = 6;
                 k = i;
                //@ assert k == i;
                }
                { Integer i = 6;
                int k = i;
                //@ assert k == i+1;
                }
                System.out.println("END");
                }
                }
                """
                ,"/tt/A.java:38: JML assertion is false"
                ,"END"
                );
    }

    @Test public void testBoxingOnAssignmentOp() {
        helpRacText("tt.A",
                """
                package tt;
                /*@ nullable_by_default*/
                public class A {
                  public static void main(String[] args) {
                    try { Integer i = null; int k = 6;
                      k += i; //@ forbid // FIXME - why duplicate messages
                    } catch (Exception e) {}

                    try { Integer i = null; int k = 6;
                      i += k;  //@ forbid // FIXME - why duplicate messages
                    } catch (Exception e) {}

                    { Integer i = 5; int k = 6;
                      k += i; i += k;
                      //@ assert k == 11;
                    }

                    try { Boolean i = null; boolean k = true;
                          k &= i; //@ forbid // FIXME - and no duplicate here, or below
                    } catch (Exception e) {}

                    try { Boolean i = null; boolean k = true;
                         i &= k; //@ forbid
                    } catch (Exception e) {}

                    { Boolean i = false; boolean k = true;
                      k &= i;
                      i &= k;
                      //@ assert  !k;
                    }

                    System.out.println(\"END\");
                  }
                }
                """
                ,"/tt/A.java:6: verify: JML Attempt to unbox a null object"
                ,"/tt/A.java:6: verify: JML Attempt to unbox a null object"
                ,"/tt/A.java:10: verify: JML Attempt to unbox a null object"
                ,"/tt/A.java:10: verify: JML Attempt to unbox a null object"
                ,"/tt/A.java:19: verify: JML Attempt to unbox a null object"
                ,"/tt/A.java:23: verify: JML Attempt to unbox a null object"
                ,"END"
                );
    }

    @Test public void testBoxingOnNullAsssignment() {
        helpRacText("tt.A",
                """
                package tt;
                /*@ nullable_by_default*/
                public class A {
                public static void main(String[] args) {
                try { Integer i = null;
                int k; k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                try { Boolean i = null;
                boolean k; k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                try { Short i = null;
                short k; k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                try { Long i = null;
                long k; k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                try { Byte i = null;
                byte k; k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                try { Double i = null;
                double k; k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                try { Float i = null;
                float k; k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                try { Character i = null;
                char k; k = i; //@ forbid
                //@ assert k == i;
                } catch (Exception e) {}
                System.out.println("END");
                }
                }
                """
                ,"/tt/A.java:6: JML Attempt to unbox a null object"
                ,"/tt/A.java:10: JML Attempt to unbox a null object"
                ,"/tt/A.java:14: JML Attempt to unbox a null object"
                ,"/tt/A.java:18: JML Attempt to unbox a null object"
                ,"/tt/A.java:22: JML Attempt to unbox a null object"
                ,"/tt/A.java:26: JML Attempt to unbox a null object"
                ,"/tt/A.java:30: JML Attempt to unbox a null object"
                ,"/tt/A.java:34: JML Attempt to unbox a null object"
                ,"END"
                );

    }

    @Test public void testBoxing() {
        helpRacText("tt.A",
                """
                package tt;
                /*@ nullable_by_default*/
                public class A {
                public static int unbox(int i) { return i;}
                public static Integer box(Integer i) { return i;}
                public static void main(String[] args) {
                try { Boolean i = null;
                boolean k = true && i; //@ forbid // Null problem
                //@ assert k == i;
                } catch (Exception e) {}
                try { Boolean i = false;
                boolean k = true && i;
                //@ assert k == false;
                } catch (Exception e) {}
                try { Boolean i = null;
                boolean k = i && true; //@ forbid // Null problem
                //@ assert k == i;
                } catch (Exception e) {}
                try { Boolean i = false;
                boolean k = i && true;
                //@ assert k == false;
                } catch (Exception e) {}
                try { Integer i = null;
                int k = 0 + i; //@ forbid // Null problem - 22
                //@ assert k == i;
                } catch (Exception e) {}
                try { Integer i = 6;
                int k = 0 + i;
                //@ assert k == 6;
                } catch (Exception e) {}
                try { Integer i = null;
                int k = i + 0; //@ forbid // Null problem - 30
                //@ assert k == i;
                } catch (Exception e) {}
                try { Integer i = 6;
                int k = i + 0;
                //@ assert k == 6;
                } catch (Exception e) {}
                try { Integer i = null;
                int k = - i; //@ forbid // Null problem -- 38
                //@ assert k == -i;
                } catch (Exception e) {}
                try { Integer i = 6;
                int k = - i;
                //@ assert k == -6;
                } catch (Exception e) {}
                try { Integer i = null;
                unbox(i); // Null problem -- 46
                } catch (Exception e) { System.out.println("CAUGHT 46"); }
                try { Integer i = 6;
                int k = unbox(i);
                //@ assert k == 6;
                } catch (Exception e) {}
                try { int i = 6;
                Integer k = box(i); int ii = k;
                //@ assert ii == 6;
                } catch (Exception e) {}
                try { Boolean b = null;
                int i = b ? 4 : 5; //@ forbid // Null problem - 57
                //@ assert i == 6;
                } catch (Exception e) {}
                try { Boolean b = false;
                int i = b ? 4 : 5;
                //@ assert i == 5;
                } catch (Exception e) {}
                try { Boolean b = null;
                int i; if (b) i = 4; else i = 5; //@ forbid // Null problem 65
                //@ assert i == 6;
                } catch (Exception e) {}
                try { Boolean b = false;
                int i; if (b) i = 4; else i = 5;
                //@ assert i == 5;
                } catch (Exception e) {}
                System.out.println("END");
                }
                }
                """
                ,"/tt/A.java:8: JML Attempt to unbox a null object"
                ,"/tt/A.java:16: JML Attempt to unbox a null object"
                ,"/tt/A.java:24: JML Attempt to unbox a null object"
                ,"/tt/A.java:32: JML Attempt to unbox a null object"
                ,"/tt/A.java:40: JML Attempt to unbox a null object"
                ,"CAUGHT 46"
                ,"/tt/A.java:59: JML Attempt to unbox a null object"
                ,"/tt/A.java:67: JML Attempt to unbox a null object"
                ,"END"
                );

        // FIXME: Also synchronized expression, switch expression, not on String, conditional, assignop, array index
        // type test, type case, return, loop initializers, array initializers, if condition
    }

    @Test public void testBoxingClass() {
        expectedRACExit = 1;
        helpRacText("tt.A",
                """
                package tt;
                /*@ nullable_by_default*/
                public class A {
                  public static int unbox(int i) { return i;}
                  public static Integer box(Integer i) { return i;}
                  public static Integer i = 6;
                  public static int j = i;
                  static { //@ assert j == 6;
                  }
                  static { Integer k = 6; int m = k; //@ assert m == 6;
                  }
                  static { try { Integer k = null; int m = k; } catch (Exception e) {} //@ forbid
                  }
                  public static Integer ii = null;
                  public static int jj = ii; //@ forbid

                  public static void main(String[] args) {
                      System.out.println(\"END\");
                  }
                }
                """
                    ,"/tt/A.java:12: verify: JML Attempt to unbox a null object"
                    ,"/tt/A.java:15: verify: JML Attempt to unbox a null object"
                    ,"java.lang.ExceptionInInitializerError"
                    ,"Caused by: java.lang.NullPointerException: Cannot invoke \"java.lang.Integer.intValue()\" because \"tt.A.ii\" is null"
                    ,"\tat tt.A.<clinit>(A.java:15)"
                );
    }

    @Test public void testBoxingString() {
        helpRacText("tt.A",
                """
                package tt;
                /*@ nullable_by_default*/
                public class A {
                public static int unbox(int i) { return i;}
                public static Integer box(Integer i) { return i;}
                public static void main(String[] args) {
                try { String s = null;
                String ss = "a" + s; ss += s; // No null problem // FIXME - crashes on the +=

                } catch (Exception e) {}
                System.out.println("END");
                }
                }
                """
                ,"END"
                );
    }
}
