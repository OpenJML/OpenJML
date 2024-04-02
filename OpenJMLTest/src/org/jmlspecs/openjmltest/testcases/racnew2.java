package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Assert;
import org.junit.Test;

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
        addOptions("-code-math=java","-spec-math=java");;
        addOptions("--rac-show-source=line");
        expectedNotes = 0;
        // Tests presume --nonnull-by-default
    }
    
    /** Tests a copying modifiers and annotations */
    // We really need to inspect the output to see that the result is OK. But at least this tests that it does not crash
    @Test public void testMods() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; import java.lang.annotation.*; \n" +
                " @Retention(RetentionPolicy.RUNTIME)  \n" +
                "  @interface A { }\n" +
                " public class TestJava { public static void main(String... args) {}" +
                "}"
        );        
    }

    @Test public void testMods2() {
        expectedExit = 1;
        helpTCX("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*; import java.lang.annotation.*;
                public class TestJava {
                    @NonNull  protected void m() {}
                    public static void main(String... args) {}
                }
                """
                ,"/tt/TestJava.java:3: error: annotation interface not applicable to this kind of declaration",5
        );        
    }
    
    @Test public void testMethodCall() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; import java.lang.annotation.*; \n" +
                " public class TestJava { \n" +
                "   //@ ensures \\result > 0; \n" +
                "   public static int m(int i) {return i;} \n" +
                "   public static void main(String... args) {\n" +
                "     System.out.println(\"START\"); \n" +
                "     int k = m(1);\n" +
                "     System.out.println(\"MID\"); \n" +
                "     k += 5 + m(-1);\n" +
                "     System.out.println(\"END\"); \n" +
                "   }" +
                "}"
                ,"START"
                ,"MID"
                ,"/tt/TestJava.java:4: verify: JML postcondition is false"
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:4:"
                ,"/tt/TestJava.java:9: verify: JML postcondition is false"
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:9:"
                ,"END"
        );        
    }
    
    /** Tests new array */
    @Test public void testNewArray() {  // FIXME - improve error message when String.equals includes its model methods for RAC
        addOptions("--show");
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
//                "  String[] a = new String[]{\"abc\",\"def\"};\n" +
//                "  int i = a.length; \n" +
//                "  //@ assert i == 2; \n" +
                "  String[][] aa = new String[][]{{\"abc\",\"defz\"},{\"g\",\"h\",\"i\"}};\n" +
//                "  i = aa.length; \n" +
                "  boolean b = aa[1][0].equals(\"g\"); \n" +
//                "  //@ assert i == 2; \n" +
//                "  //@ assert aa[1].length == 3; \n" +
//                "  //@ assert (new int[]{1,2,3}).length == 3; \n" +
//                "  //@ assert (new int[]{1,2,3})[1] == 2; \n" +
//                "  String[][] aaa = new String[1][2]; \n" +
//                "  //@ assert aaa.length == 1; \n" +
//                "  //@ assert aaa[0].length == 2; \n" +
//                "  //@ assert aaa[0][0] == null; \n" +
//                
//                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"END"
        );        
    }

    /** Tests new array */
    @Test public void testNewArray2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  int[] x = new int[3]; \n" +
                "  //@ assert x.length == 3; \n" +
                "  //@ assert x[0] == 0; \n" +
                "  String[] a = {\"abc\",\"def\"};\n" +
                "  int i = a.length; \n" +
                "  //@ assert i == 2; \n" +
                "  String[][] aa = {{\"abc\",\"defz\"},{\"g\",\"h\",\"i\"}};\n" +
                "  i = aa.length; \n" +
                "  boolean b = aa[1][0].equals(\"g\"); \n" +
                "  //@ assert i == 2; \n" +
                "  //@ assert aa[1].length == 3; \n" +
                "  String[][] aaa = new String[1][2]; \n" +
                "  //@ assert aaa.length == 1; \n" +
                "  //@ assert aaa[0].length == 2; \n" +
                "  //@ assert aaa[0][0] == null; \n" +
                
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"END"
        );        
    }

    /** Tests new object */
    @Test public void testNewObject() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  TestJava a = new TestJava();\n" +
                "  int i = a.m(10); \n" +
                "  //@ assert i == 11; \n" +
                "  TestJava aa = new TestJava() { public int m(int i) { return i + 2; } } ;\n" +
                "  i = aa.m(10); \n" +
                "  //@ assert i == 12; \n" +
                
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "  public int m(int i) { return i + 1; } \n" +
                "}"
                ,"END"
        );        
    }

    /** Tests new object in JML */
    @Test public void testNewObject2() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  // @ assert (new TestJava()).m(15) == 16;\n" +
                "  //@ assert (new TestJava() { public pure int m(int i) { return i + 2; } }).m(15) == 17;\n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "  /*@ pure */ public int m(int i) { return i + 1; } \n" +
                "}"
                ,"/tt/TestJava.java:3: error: Object allocation is not permitted in specification expressions",15
                ,"END"
        );        
    }

//    /** Tests new object in JML */
//    @Test public void testNewObject3() {
//        helpTCX("tt.TestJava",
//                """
//                package tt; public class TestJava {
//                  public int k;
//                  //@requires i > 0; ensures k == i;
//                  public /*@ pure */ TestJava(int i) { k = i < 2 ? i : 5; }
//                  public static void main(String[] args) {
//                    System.out.println(\"TestJava - 1\");
//                    TestJava t = new TestJava(1);
//                    System.out.println(\"TestJava - 0\");
//                    t = new TestJava(0);
//                    System.out.println(\"TestJava - 2\");
//                    //@ assert (new TestJava(2)).k == 2;
//                    System.out.println(\"TestJava - 0\");
//                    //@ assert (new TestJava(0)).k == 0;
//                    System.out.println(\"END\");
//                  }
//                }
//                """
//                ,"TestJava - 1"
//                ,"TestJava - 0"
//                ,"/tt/TestJava.java:9: JML precondition is false" // caller check -- TestJava(0)
//                ,"/tt/TestJava.java:4: Associated declaration: /tt/TestJava.java:9:"
//                ,"/tt/TestJava.java:3: JML precondition is false" // callee check
//                ,"TestJava - 2"
//                ,"/tt/TestJava.java:4: JML postcondition is false" // callee check
//                ,"/tt/TestJava.java:3: Associated declaration: /tt/TestJava.java:4:"
//                ,"/tt/TestJava.java:11: JML postcondition is false" // caller check
//                ,"/tt/TestJava.java:3: Associated declaration: /tt/TestJava.java:11:"
//                ,"/tt/TestJava.java:11: JML assertion is false"
//                ,"TestJava - 0"
//                ,"/tt/TestJava.java:13: JML a method called in a JML expression is undefined because its precondition is false"
//                ,"/tt/TestJava.java:4: Associated declaration: /tt/TestJava.java:13:"
//                ,"/tt/TestJava.java:3: JML precondition is false"
//                ,"END"
//        );        
//    }


    /** Tests a simple try-finally block */
    @Test public void testTry() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  int i; try { i = 0; } finally { i = 1; } //@ assert i == 1; \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"END"
        );        
    }


    /** Test skip statement */
    @Test public void testSkip() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { int i ;;; i = 9;;;; //@ assert i == 9; \n }\n  \n}"
                );
    }

    /** Test synchronized statement with this */
    @Test public void testSynchronized() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { new A().m(); }\n public void m() { int i; \n synchronized (this) { i = 0; } \n}}"
                );
    }

    /** Test synchronized statement with null lock */
    @Test public void testSynchronized2() {
        expectedRACExit = 1;
        helpTCX("tt.A",
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
                ,"/tt/A.java:9: verify: JML An object may be illegally null"
                ,"Exception in thread \"main\" java.lang.NullPointerException: Cannot enter synchronized block because \"<local5>\" is null"
                ,"\tat tt.A.m(A.java:9)"
                ,"\tat tt.A.main(A.java:4)"
                );
    }


    /** Tests a simple try-throw-catch block */
    @Test public void testThrow() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  int i; try { i = 0; throw new RuntimeException(); } catch (RuntimeException e) { i = 1; } //@ assert i == 1; \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"END"
        );        
    }


    /** Tests binary operators */
    @Test public void testBinary() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  int a=5,b=6,c; boolean f, e= true,d=false; \n" +
                "  c = a + b; \n" +
                "  //@ assert c == a + 6; \n" +
                "  c = a - b; \n" +
                "  //@ assert a - c == 6; \n" +
                "  c = a * b; \n" +
                "  //@ assert b == c / 5; \n" +
                "  c = b / (a - 3); \n" +
                "  //@ assert b == c * 2; \n" +
                "  c = b % a; \n" +
                "  //@ assert a % b == a && c == 1; \n" +
                "  f = a < b ; \n" +                    // FIXME - this line causes a problem
                "  //@ assert  f && a <= b; \n" +
                "  f = a <= b ; \n" +  
                "  //@ assert  f && a < b; \n" +
                "  f = a > b ; \n" +  
                "  //@ assert  !f && a >= b; \n" +
                "  f = a >= b ; \n" +  
                "  //@ assert  !f && a > b; \n" +
                // FIXME - add equalities among various types, && || & ^ | logical and bit
                // FIXME - test JML binary
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"/tt/TestJava.java:18: JML assertion is false"
                ,"/tt/TestJava.java:20: JML assertion is false"
                ,"END"
        );        
    }

    /** Tests binary operators */
    @Test public void testShift() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  int a=5,b=6,c=100;  \n" +
                "  int d = a << b; \n" +
                "  d = a << c; \n" +  // ERROR
                "  d = a >> b; \n" +
                "  d = a >> c; \n" + // ERROR
                "  d = a >>> b; \n" +
                "  d = a >>> c; \n" + // ERROR
                "  long e = 20L << b; \n" +
                "  e = 20L << (b+40); \n" + // OK
                "  e = 20L << c; \n" + // ERROR
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"/tt/TestJava.java:4: JML shift amount is out of expected range"
                ,"/tt/TestJava.java:6: JML shift amount is out of expected range"
                ,"/tt/TestJava.java:8: JML shift amount is out of expected range"
                ,"/tt/TestJava.java:11: JML shift amount is out of expected range"
                ,"END"
        );        
    }

    /** Tests binary operators */
    @Test public void testConditional() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  int a=5,b=6,c=100;  \n" +
                "  int d = a < 10 ? b + 3 : c-40; \n" +
                "  System.out.println(d); \n" +
                "  //@ assert (c > 4? a + 3 : b + 3) == 9; \n" +   // ERROR
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"9"
                ,"/tt/TestJava.java:5: JML assertion is false"
                ,"END"
        );        
    }

    /** Tests unary operators */ // FIXME - test unary with expressions in ++ -- 
    @Test public void testUnary() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  int a=5,b=0,c=0; boolean e=true,d=false; \n" +
                "  b = a++; \n" +
                "  //@ assert b+1 == a; \n" +
                "  b = a--; \n" +
                "  //@ assert b-1 == a; \n" +
                "  c = a; b = ++a; \n" +
                "  //@ assert b == a && c+1 == b; \n" +
                "  b = --a; \n" +
                "  //@ assert b == a && c == b; \n" +
                "  b = -a; \n" +
                "  //@ assert b == -5; \n" +
                "  e = d ; \n" + 
                "  //@ assert  !d; \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"END"
        );        
    }

    /** Tests parens operators */ 
    @Test public void testParens() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  int a=5,b=6,c=0; boolean e=true,d=false; \n" +
                "  c = (a*b)+3*b-2*(a-(((b)))); \n" +
                "  //@ assert ((((c) == 50))); \n" +
                "  c = b / (((a))); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"END"
        );        
    }



    /** Tests switch statement */
    @Test public void testBreak() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  m(0);  m(2); m(3);  m(5); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "  static void m(int i) { \n" +
                "    out: { \n" +
                "       in: { \n" +
                "            System.out.print(i + \"A\");\n" +
                // Unlabelled breaks are not allowed for blocks
                "            if (i == 2) break in;\n" +
                "            if (i == 3) break out;\n" +
                "            System.out.print(\"B\");\n" +
                "           }\n" +
                "            System.out.print(\"C\");\n" +
                "            if (i == 5) break out;\n" +
                "            System.out.print(\"D\");\n" +
                "        }\n" +
                "            System.out.println(\"Z\");\n" +
                "  } \n" +
                "}"
                ,"0ABCDZ"
                ,"2ACDZ"
                ,"3AZ"
                ,"5ABCZ"
                ,"END"
        );        
    }
    
    @Test public void testSimpleBreak() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                                "  m(0);  m(2);  \n" +
                                "  System.out.println(\"END\"); \n" +
                                "  } \n" + 
                                "  static void m(int i) { \n" +
                                "       in: { \n" +
                                "            System.out.print(i + \"A\");\n" +
                                // Unlabelled breaks are not allowed for blocks
                                "            if (i == 2) break in;\n" +
                                "            System.out.print(\"B\");\n" +
                                "           }\n" +
                                "            System.out.println(\"C\");\n" +
                                "        }\n" +
                                "}"
                                ,"0ABC"
                                ,"2AC"
                                ,"END"
                        );        
    }

    /** Tests switch statement */
    @Test public void testSwitch() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  m(0); m(1); m(2); m(3); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "  static void m(int i) { \n" +
                "  switch (i) { \n" +
                "  case 0: //@ assert i == 0; \n break; \n" +
                "  case 1: //@ assert i == 0; \n break; \n" +
                "  case 2: //@ assert i == 2; \n break; \n" +
                "  default: //@ assert i == 0; \n break; \n" +
                "  }}\n" +
                "}"
                ,"/tt/TestJava.java:9: JML assertion is false"
                ,"/tt/TestJava.java:13: JML assertion is false"
                ,"END"
        );        
    }

    /** Tests switch statement with declaration in a case*/
    @Test public void testSwitch2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  m(0); m(1); m(2); m(3); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "  static void m(int i) { \n" +
                "  switch (i) { \n" +
                "  case 0: int k = 0; //@ assert i == k; \n  \n" +
                "  case 1: k=1;       //@ assert i == k; \n break; \n" +
                "  case 2: k=2;       //@ assert i == k; \n break; \n" +
                "  default: //@ assert i == 0; \n break; \n" +
                "  }}\n" +
                "}"
                ,"/tt/TestJava.java:9: JML assertion is false" // case 0 falls through
                ,"/tt/TestJava.java:13: JML assertion is false"
                ,"END"
        );        
    }

    /** Tests switch statement with block breaks */
    @Test public void testSwitch3() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  m(0); m(1); m(2); m(3); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "  static void m(int i) { \n" +
                "  System.out.print(i);  \n" +
                "  out: { switch (i) { \n" +
                "  case 0: break; \n" +
                "  case 1: break out; \n" +
                "  case 2: in: { break in; } System.out.print(\"X\"); break; \n" +
                "  default: in: { if (i == 3)  break; } System.out.print(\"Y\"); break; \n" +
                "  }\n" +
                "  System.out.print(\"Z\"); }\n" +
                "  }\n" +
                "}"
                ,"0Z12XZ3ZEND"
        );        
    }

    /** Tests switch statement */
    @Test public void testSwitchShort() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  m((short)0); m((short)1); m((short)2); m((short)3); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "  static void m(short i) { \n" +
                "  switch (i) { \n" +
                "  case 0: //@ assert i == 0; \n break; \n" +
                "  case 1: //@ assert i == 0; \n break; \n" +
                "  case 2: //@ assert i == 2; \n break; \n" +
                "  default: //@ assert i == 0; \n break; \n" +
                "  }}\n" +
                "}"
                ,"/tt/TestJava.java:9: JML assertion is false"
                ,"/tt/TestJava.java:13: JML assertion is false"
                ,"END"
        );        
    }

    /** Tests switch statement */
    @Test public void testSwitchShort2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  m((short)0); m((short)1); m((short)2); m((short)3); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "  static void m(short s) { Short i = Short.valueOf(s); \n" +
                "  switch (i) { \n" +
                "  case 0: //@ assert i == 0; \n break; \n" +
                "  case 1: //@ assert i == 0; \n break; \n" +
                "  case 2: //@ assert i == 2; \n break; \n" +
                "  default: //@ assert i == 0; \n break; \n" +
                "  }}\n" +
                "}"
                ,"/tt/TestJava.java:9: JML assertion is false"
                ,"/tt/TestJava.java:13: JML assertion is false"
                ,"END"
        );        
    }

    /** Tests switch statement */
    @Test public void testSwitchByte() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  m((byte)0); m((byte)1); m((byte)2); m((byte)3); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "  static void m(byte i) { \n" +
                "  switch (i) { \n" +
                "  case 0: //@ assert i == 0; \n break; \n" +
                "  case 1: //@ assert i == 0; \n break; \n" +
                "  case 2: //@ assert i == 2; \n break; \n" +
                "  default: //@ assert i == 0; \n break; \n" +
                "  }}\n" +
                "}"
                ,"/tt/TestJava.java:9: JML assertion is false"
                ,"/tt/TestJava.java:13: JML assertion is false"
                ,"END"
        );        
    }

    /** Tests switch statement */
    @Test public void testSwitchByte2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  m((byte)0); m((byte)1); m((byte)2); m((byte)3); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "  static void m(byte s) { Byte i = Byte.valueOf(s); \n" +
                "  switch (i) { \n" +
                "  case 0: //@ assert i == 0; \n break; \n" +
                "  case 1: //@ assert i == 0; \n break; \n" +
                "  case 2: //@ assert i == 2; \n break; \n" +
                "  default: //@ assert i == 0; \n break; \n" +
                "  }}\n" +
                "}"
                ,"/tt/TestJava.java:9: JML assertion is false"
                ,"/tt/TestJava.java:13: JML assertion is false"
                ,"END"
        );        
    }

    /** Tests switch statement */
    @Test public void testSwitchInteger2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  m(0); m(1); m(2); m(3); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "  static void m(int s) { Integer i = Integer.valueOf(s); \n" +
                "  switch (i) { \n" +
                "  case 0: //@ assert i == 0; \n break; \n" +
                "  case 1: //@ assert i == 0; \n break; \n" +
                "  case 2: //@ assert i == 2; \n break; \n" +
                "  default: //@ assert i == 0; \n break; \n" +
                "  }}\n" +
                "}"
                ,"/tt/TestJava.java:9: JML assertion is false"
                ,"/tt/TestJava.java:13: JML assertion is false"
                ,"END"
        );        
    }

    /** Tests switch statement */
    @Test public void testSwitchInteger2Null() {
        helpTCX("tt.TestJava","package tt; /*@ nullable_by_default*/public class TestJava { public static void main(String[] args) { \n" +
                "  try { m(0); } catch (Exception e) { System.out.println(\"EXCEPTION THROWN\"); } \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "  static void m(int s) { Integer i = null; \n" +
                "  switch (i) { \n" +
                "  case 0: //@ assert i == 0; \n break; \n" +
                "  case 1: //@ assert i == 0; \n break; \n" +
                "  case 2: //@ assert i == 2; \n break; \n" +
                "  default: //@ assert i == 0; \n break; \n" +
                "  }}\n" +
                "}"
                ,"/tt/TestJava.java:6: JML Attempt to unbox a null object"
                ,"EXCEPTION THROWN"
                ,"END"
        );        
    }

    /** Tests switch statement */
    @Test public void testSwitchChar() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  m('a'); m('b'); m('c'); m('d'); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "  static void m(char i) { \n" +
                "  switch (i) { \n" +
                "  case 'a': //@ assert i == 'a'; \n break; \n" +
                "  case 'b': //@ assert i == 'a'; \n break; \n" +
                "  case 'c': //@ assert i == 'c'; \n break; \n" +
                "  default: //@ assert i == 'a'; \n break; \n" +
                "  }}\n" +
                "}"
                ,"/tt/TestJava.java:9: JML assertion is false"
                ,"/tt/TestJava.java:13: JML assertion is false"
                ,"END"
        );        
    }

    /** Tests switch statement */
    @Test public void testSwitchChar2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  m('a'); m('b'); m('c'); m('d'); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "  static void m(char s) { Character i = Character.valueOf(s);\n" +
                "  switch (i) { \n" +
                "  case 'a': //@ assert i == 'a'; \n break; \n" +
                "  case 'b': //@ assert i == 'a'; \n break; \n" +
                "  case 'c': //@ assert i == 'c'; \n break; \n" +
                "  default: //@ assert i == 'a'; \n break; \n" +
                "  }}\n" +
                "}"
                ,"/tt/TestJava.java:9: JML assertion is false"
                ,"/tt/TestJava.java:13: JML assertion is false"
                ,"END"
        );        
    }


    /** Tests type test and type cast expressions */
    @Test public void testTypeCast() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  Integer i = Integer.valueOf(10); \n" +
                "  Object o = i; \n" +
                "  Integer ii = (Integer)o; \n" +
                "  System.out.println(ii); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"10"
                ,"END"
        );        
    }

    /** Tests a bad cast */
    @Test public void testTypeCast2() {
        expectedRACExit = 1;
        addOptions("--rac-show-source=source");
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  Boolean i = Boolean.TRUE; \n" +
                "  Object o = i; \n" +
                "  Integer ii = (Integer)o;\n" +
                "  System.out.println(ii); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"/tt/TestJava.java:4: JML A cast is invalid - from java.lang.Object to java.lang.Integer"
                ,"  Integer ii = (Integer)o;"
                ,"               ^"
                ,"Exception in thread \"main\" java.lang.ClassCastException: class java.lang.Boolean cannot be cast to class java.lang.Integer (java.lang.Boolean and java.lang.Integer are in module java.base of loader 'bootstrap')"
                ,"\tat tt.TestJava.main(TestJava.java:4)"
        );        
    }

    /** Tests a type test with a cast */
    @Test public void testTypeCast3() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  Boolean b = Boolean.TRUE; \n" +
                "  Integer i = Integer.valueOf(10); /*@ nullable */Integer ii = null; \n" +
                "  Object o = i; \n" +
                "  if (o instanceof Integer) { ii = (Integer)o; }\n" +
                "  o = b; \n" +
                "  if (o instanceof Integer) { ii = (Integer)o; }\n" +
                "  System.out.println(ii); \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"10"
                ,"END"
        );        
    }

    /** Test a type tests and casts in JML */
    @Test public void testTypeTest4() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  Boolean b = Boolean.TRUE; \n" +
                "  Integer i = Integer.valueOf(10); /*@ nullable */Integer ii = null; \n" +
                "  Object o = i; \n" +
                "  //@ assert o instanceof Integer; \n" +
                "  o = b; \n" +
                "  //@ assert o instanceof Integer; \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"/tt/TestJava.java:7: JML assertion is false"
                ,"END"
        );        
    }

    /** Test a type tests and casts in JML */
    @Test public void testTypeCast5() {
        expectedRACExit = 1;
        addOptions("--rac-show-source=line");
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  Boolean b = Boolean.TRUE; \n" +
                "  Integer i = Integer.valueOf(10); /*@ nullable */Integer ii = null; \n" +
                "  Object o = i; \n" +
                "  //@ assert (Integer)o != null; \n" +
                "  o = b; \n" +
                "  //@ assert (Integer)o != null; \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"/tt/TestJava.java:7: JML A cast is invalid - from java.lang.Object to java.lang.Integer"
                ,"Exception in thread \"main\" java.lang.ClassCastException: class java.lang.Boolean cannot be cast to class java.lang.Integer (java.lang.Boolean and java.lang.Integer are in module java.base of loader 'bootstrap')"
                ,"\tat tt.TestJava.main(TestJava.java:7)"
        );        
    }

    /** Test a type tests and casts in JML */
    @Test public void testTypeCast6() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "  Boolean b = Boolean.TRUE; \n" +
                "  Integer i = Integer.valueOf(10); /*@ nullable */Integer ii = null; \n" +
                "  Object o = i; \n" +
                "  //@ assert o instanceof Integer && (Integer)o != null; \n" +
                "  o = b; \n" +
                "  //@ assert o instanceof Integer && (Integer)o != null; \n" +
                "  System.out.println(\"END\"); \n" +
                "  } \n" + 
                "}"
                ,"/tt/TestJava.java:7: JML assertion is false"
                ,"END"
        );        
    }


    /** Tests the JML lbl lblpos and lblneg expressions */
    @Test public void testLbl() {
        addOptions("-spec-math=math");
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null); \n" +
                "System.out.println(\"END\"); } \n" +
                "static int i = 0; static String n = \"asd\";\n" +
                " static void m(/*@nullable*/ Object o) { \n" +
                "//@ assert (\\lbl STRING \"def\") != null; \n" +
                "++i; //@ assert (\\lbl SHORT (short)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl LONG (long)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl BYTE (byte)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl INT (int)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl FLOAT (float)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl DOUBLE (double)(i)) != 0; \n" +
                "//@ assert (\\lbl CHAR (char)(i+60) ) != 0; \n" +
                "//@ assert (\\lbl BOOLEAN (i == 0)) ; \n" +
                "//@ assert (\\lbl OBJECT o) == null; \n" +
                "//@ assert (\\lbl NULL null) == null; \n" +
                "//@ assert (\\lbl STRING \"abc\") != null; \n" +
                "//@ assert (\\lblpos POST (i!=0)); \n" +
                "//@ assert !(\\lblpos POSF (i==0)); \n" +
                "//@ assert (\\lblneg NEGT (i!=0)); \n" +
                "//@ assert !(\\lblneg NEGF (i==0)); \n" +
                "//@ assert !(\\lblpos POST (i!=0)); \n" +
                "//@ assert (\\lblneg NEGF (i==0)); \n" +
                "} " +
                "}"
                ,"LABEL STRING = def"
                ,"LABEL SHORT = 1"
                ,"LABEL LONG = 2"
                ,"LABEL BYTE = 3"
                ,"LABEL INT = 4"
                ,"LABEL FLOAT = 5.0"
                ,"LABEL DOUBLE = 6.0"
                ,"LABEL CHAR = B"
                ,"LABEL BOOLEAN = false"
                ,"/tt/TestJava.java:14: JML assertion is false"
                ,"LABEL OBJECT = null"
                ,"LABEL NULL = null"
                ,"LABEL STRING = abc"
                ,"LABEL POST = true"
                ,"LABEL NEGF = false"
                ,"LABEL POST = true"
                ,"/tt/TestJava.java:22: JML assertion is false"
                ,"LABEL NEGF = false"
                ,"/tt/TestJava.java:23: JML assertion is false"
                ,"END"
                );
        
    }
    
    /** Tests the JML lbl expression when the argument is a literal */
    @Test public void testLblConst() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null); \n" +
                "System.out.println(\"END\"); } static int i = 0; \n" +
                " static void m(/*@nullable*/ Object o) { \n" +
                "//@ assert (\\lbl OBJECT null) == null; \n" +
                "//@ assert (\\lbl INT 4) != 0; \n" +
                "//@ assert (\\lbl SHORT (short)(1)) != 0; \n" +
                "//@ assert (\\lbl LONG 2L) != 0; \n" +
                "//@ assert (\\lbl BYTE (byte)(3)) != 0; \n" +
                "//@ assert (\\lbl FLOAT 5.0f) != 0; \n" +
                "//@ assert (\\lbl DOUBLE 6.0) != 0; \n" +
                "//@ assert (\\lbl CHAR 'a') != 0; \n" +
                "//@ assert (\\lbl BOOLEAN true) ; \n" +
                "//@ assert (\\lbl STRING \"abc\") != null; \n" +
                "} " +
                "}"
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
        helpTCX("tt.TestJava",
                "package tt; public class TestJava { /*@ assignable \\everything; */ public static void main(String[] args) { \n" +
                " m(1); m(0); \n" +
                " System.out.println(\"END\"); } static public int k = 0; \n" +
                " /*@ assignable \\everything; ensures (\\lbl ENS k == 1); */ \n" +
                " static public void m(int i) { System.out.println(\"i = \" + i ); k = i; } " +
                "}"
                ,"i = 1"
                ,"LABEL ENS = true"
                ,"LABEL ENS = true"
                ,"i = 0"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:5: JML postcondition is false"
                ," static public void m(int i) { System.out.println(\"i = \" + i ); k = i; } }"
                ,"                    ^"
                ,"/tt/TestJava.java:4: Associated declaration: /tt/TestJava.java:5:"
                ," /*@ assignable \\everything; ensures (\\lbl ENS k == 1); */ "
                ,"                             ^"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ," m(1); m(0); "
                ,"        ^"
                ,"/tt/TestJava.java:4: Associated declaration: /tt/TestJava.java:2:"
                ," /*@ assignable \\everything; ensures (\\lbl ENS k == 1); */ "
                ,"                             ^"
                ,"END"
        );        
    }
    
    /** A misc early test case for lbl expressions */
    @Test public void testLabel2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { /*@ assignable \\everything; */ public static void main(String[] args) { \n" +
                " m(1); m(0); \n" +
                " System.out.println(\"END\"); } static public int k = 0; \n" +
                " /*@ assignable \\everything; ensures (\\lblneg ENS (\\lbl RES k) == 1); */ \n" +
                " static public void m(int i) { k = i; return; } " +
                "}"
                ,"LABEL RES = 1"
                ,"LABEL RES = 1"
                ,"LABEL RES = 0"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:5: verify: JML postcondition is false"
                ,"/tt/TestJava.java:4: verify: Associated declaration: /tt/TestJava.java:5:"
                ,"LABEL RES = 0"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:2: verify: JML postcondition is false"
                ,"/tt/TestJava.java:4: verify: Associated declaration: /tt/TestJava.java:2:"
                ,"END"
        );        
    }
    
    /** Checks one can do assignments in a model method. */
    @Test public void testModelMethod() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " //@ ghost boolean k; set k = m(); assert k; \n" +
                " //@                  set k = m(); assert k; \n" +
                " System.out.println(\"END\"); } \n" +
                " //@ ghost static int i = 0; \n" +
                " //@ ghost static int j = 0; \n" +
                " //@ model static boolean m() { j = 1; i+= 1; int k = 2; return i == 1; } " +
                "}"
                ,"/tt/TestJava.java:3: JML assertion is false"
                ,"END"
        );        
    }
    
    /** Checks select expressions. */
    @Test public void testSelect() {
        expectedRACExit = 1;
        helpTCX("tt.TestJava",
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
        helpTCX("tt.TestJava",
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
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " System.out.println(m(1)); \n" +
                " //@ set System.out.println(p(new G())); \n" +
                " System.out.println(\"END\"); } \n" +
                " static <T> T m(T i) { return i; } \n" +
                " //@ model static public class G {} \n" +
                " //@ model static int p(G i) { return 5; } \n" +
                "}"
                ,"1"
                ,"5"
                ,"END"
        );        
    }
    
    /** Checks generic method. */
    @Test public void testGenMethod() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " System.out.println(m(1)); \n" +
                " System.out.println(\"END\"); } \n" +
                " static <T> T m(T i) { return i; } \n" +
                "}"
                ,"1"
                ,"END"
        );        
    }
    
    /** Checks generic method. */
    @Test public void testGenMethod2() {  // FIXME - this needs more investigation -- the type int seems to be used (e.g. in addImplicitCOnversion) in an expression i != null where I would expect it to have been converted to T
        helpTCX("tt.TestJava","package tt; import java.util.*; public class TestJava { public static void main(String[] args) { \n" +
                " System.out.println(m(1)); \n" +
                " System.out.println(\"END\"); } \n" +
                " static /*@nullable*/ <T> List<?> m(T i) { return null; } \n" +
                "}"
                ,"null"
                ,"END"
        );        
    }
    
    /** Checks generic classes. */
    @Test public void testGenClass() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " System.out.println(m(1)); \n" +
                " System.out.println(p(new G<Integer>())); \n" +
                " System.out.println(\"END\"); } \n" +
                " static <T> T m(T i) { return i; } \n" +
                " static public class G<T> {} \n" +
                " static <T> int p(G<?> i) { return 5; } \n" +
                "}"
                ,"1"
                ,"5"
                ,"END"
        );        
    }
    
//    @Test public void testNoWarn() { 
//        helpTCX("tt.A","package tt; public class A { \n"
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
//        helpTCX("tt.A","package tt; public class A { \n"
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
//        helpTCX("tt.A","package tt; public class A { \n"
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
//        helpTCX("tt.A","package tt; public class A { \n"
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
//        helpTCX("tt.A","package tt; public class A { \n"
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
        helpTCX("tt.A","package tt; public class A { \n"
                +"public A(int k) { i = k; } \n "
                +"public int i; \n "
                +"/*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }\n "
                +"public static void main(String[] args) { boolean z; \n"
                +"A a = new A(1);\n"
                +"A b = new A(2);\n"
                +"z = a.m(1); \n"
                +"z = b.m(2) && z; \n"
                +"z = a.m(2) && z; \n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:10: JML precondition is false"
                ,"/tt/A.java:4: Associated declaration: /tt/A.java:10:"
                ,"/tt/A.java:4: JML precondition is false"
                ,"END"
                );
    }

    @Test public void testReceiver2() { 
        helpTCX("tt.A","package tt; public class A { \n"
                +"/*@ assignable i; */ public A(int k) { i = k; } \n "
                +"static public int i;  \n "
                +"/*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }\n "
                +"public static void main(String[] args) { boolean z; \n"
                +"A a = new A(1);\n"
                +"A b = new A(2);\n"
                +"a.m(1); \n"
                +"b.m(2); \n"
                +"a.m(2); \n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:8: JML precondition is false"
                ,"/tt/A.java:4: Associated declaration: /tt/A.java:8:"
                ,"/tt/A.java:4: JML precondition is false"
                ,"END"
                );
    }

    @Test public void testReceiver3() { 
        helpTCX("tt.A","package tt; public class A { \n"
                +"/*@ assignable i; */ public A(int k) { i = k; } \n "
                +"static public int i; \n "
                +"/*@ requires i == j; ensures \\result; */ static public boolean m(int j) { return true; }\n "
                +"public static void main(String[] args) { boolean z; \n"
                +"A a = new A(1);\n"
                +"A b = new A(2);\n"
                +"z = A.m(1); \n"
                +"z = A.m(2); \n"
                +"z = A.m(2); \n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:8: JML precondition is false"
                ,"/tt/A.java:4: Associated declaration: /tt/A.java:8:"
                ,"/tt/A.java:4: JML precondition is false"
                ,"END"
                );
    }


    @Test public void testReceiver4() { 
        helpTCX("tt.A","package tt; public class A { \n"
                +"//@ ensures i == k; \n "
                +"public A(int k) { i = k; } \n"
                
                +" public int i; \n"
                
                +"public static void main(String[] args) { boolean z; \n"
                +"A a = new A(1);\n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"END"
                );
    }

    @Test public void testReceiver4bad() { 
        helpTCX("tt.A","package tt; public class A { \n"
                +"//@ ensures i == 1; \n "
                +"public A(int k) { i = k; } \n"
                
                +" public int i; \n"
                
                +"public static void main(String[] args) { boolean z; \n"
                +"A a = new A(1);\n"
                +"A b = new A(2);\n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/tt/A.java:2: Associated declaration: /tt/A.java:3:"
                ,"/tt/A.java:7: JML postcondition is false"
                ,"/tt/A.java:2: Associated declaration: /tt/A.java:7:"
                ,"END"
                );
    }

    @Test public void testLet() {
        helpTCX("tt.A","package tt; public class A { \n"
                +"//@ ensures (\\let int k = 1; \\result == k + i) ; \n "
                +"public static int m(int i) { return i + 1; } \n"
                +"//@ ensures (\\let int k = 1; \\result == k - i) ; \n "
                +"public static int mm(int i) { return i + 1; } \n"
                +"public static void main(String[] args) {  \n"
                +"m(1);\n"
                +"mm(1);\n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:5: JML postcondition is false"
                ,"/tt/A.java:4: Associated declaration: /tt/A.java:5:"
                ,"/tt/A.java:8: JML postcondition is false"
                ,"/tt/A.java:4: Associated declaration: /tt/A.java:8:"
                ,"END"
                );
    }

    @Test public void testLet2() {
        helpTCX("tt.A","package tt; public class A { \n"
                +"//@ ensures (\\let int k = 1, int j = k; \\result == j + i) ; \n "
                +"public static int m(int i) { return i + 1; } \n"
                +"//@ ensures (\\let int k = 1, int j = k; \\result == j - i) ; \n "
                +"public static int mm(int i) { return i + 1; } \n"
                +"public static void main(String[] args) {  \n"
                +"m(1);\n"
                +"mm(1);\n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:5: JML postcondition is false"
                ,"/tt/A.java:4: Associated declaration: /tt/A.java:5:"
                ,"/tt/A.java:8: JML postcondition is false"
                ,"/tt/A.java:4: Associated declaration: /tt/A.java:8:"
                ,"END"
                );
    }
    
    @Test public void testBoxingOnDeclaration() {
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] args) {  \n"
                +"{ Integer i = 6;\n"
                +"int k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Boolean i = true;\n"
                +"boolean k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Short i = 6;\n"
                +"short k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Long i = 6L;\n"
                +"long k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Byte i = 6;\n"
                +"byte k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Double i = 6.0;\n"
                +"double k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Float i = 6.0f;\n"
                +"float k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Character i = 6;\n"
                +"char k = i;\n"
                +"//@ assert k == i;\n}\n"
                
                +"{ Integer i = 6;\n"
                +"int k = i;\n"
                +"//@ assert k == i+1;\n}\n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:37: JML assertion is false"
                ,"END"
                );
    }
        
    @Test public void testBoxingOnNullDeclaration() {
        helpTCX("tt.A","package tt; /*@ nullable_by_default*/ public class A { \n"
                +"public static void main(String[] args) {  \n"
                +"try { Integer i = null;\n"
                +"int k = i; //@ forbid\n"
                +"//@ assert k == i; \n} catch (Exception e) {}\n"
                +"try { Boolean i = null;\n"
                +"boolean k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Short i = null;\n"
                +"short k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Long i = null;\n"
                +"long k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Byte i = null;\n"
                +"byte k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Double i = null;\n"
                +"double k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Float i = null;\n"
                +"float k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Character i = null;\n"
                +"char k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"

                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:4: JML Attempt to unbox a null object"
                ,"/tt/A.java:8: JML Attempt to unbox a null object"
                ,"/tt/A.java:12: JML Attempt to unbox a null object"
                ,"/tt/A.java:16: JML Attempt to unbox a null object"
                ,"/tt/A.java:20: JML Attempt to unbox a null object"
                ,"/tt/A.java:24: JML Attempt to unbox a null object"
                ,"/tt/A.java:28: JML Attempt to unbox a null object"
                ,"/tt/A.java:32: JML Attempt to unbox a null object"
                ,"END"
                );
    }       

    @Test public void testBoxingOnAssignment() {  // In Java mode
        main.addOptions("-code-math=java");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] args) {  \n"
                +"{ Integer i; int k; i = 6;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Boolean i; boolean k; i = true;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Short i; short k; i = 6;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Long i; long k; i = 6L;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Byte i; byte k; i = 6;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Double i; double k; i = 6.0;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Float i; float k; i = 6.0f;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Character i; char k; i = 6;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"

                    +"{ Integer i = 6;\n"
                    +"int k = i;\n"
                    +"//@ assert k == i+1;\n}\n"
                    +"System.out.println(\"END\"); \n"
                    +"}}"
                    ,"/tt/A.java:37: JML assertion is false"
                    ,"END"
                );
    }

    @Test public void testBoxingOnAssignmentMathMode() {
        addOptions("-code-math=math");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] args) {  \n"
                +"{ Integer i; int k; i = 6;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Boolean i; boolean k; i = true;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Short i; short k; i = 6;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Long i; long k; i = 6L;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Byte i; byte k; i = 6;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Double i; double k; i = 6.0;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Float i; float k; i = 6.0f;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"
                +"{ Character i; char k; i = 6;\n"
                +" k = i;\n"
                +"//@ assert k == i;\n}\n"

                    +"{ Integer i = 6;\n"
                    +"int k = i;\n"
                    +"//@ assert k == i+1;\n}\n"
                    +"System.out.println(\"END\"); \n"
                    +"}}"
                    ,"/tt/A.java:37: JML assertion is false"
                    ,"END"
                );
    }

    @Test public void testBoxingOnAssignmentOp() {
        helpTCX("tt.A",
                """
                package tt; /*@ nullable_by_default*/ public class A {
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
                ,"/tt/A.java:4: verify: JML Attempt to unbox a null object"
                ,"/tt/A.java:4: verify: JML Attempt to unbox a null object"
                ,"/tt/A.java:8: verify: JML Attempt to unbox a null object"
                ,"/tt/A.java:8: verify: JML Attempt to unbox a null object"
                ,"/tt/A.java:17: verify: JML Attempt to unbox a null object"
                ,"/tt/A.java:21: verify: JML Attempt to unbox a null object"
                ,"END"
                );
    }

    @Test public void testBoxingOnNullAsssignment() {
        helpTCX("tt.A","package tt; /*@ nullable_by_default*/ public class A { \n"
                +"public static void main(String[] args) {  \n"
                +"try { Integer i = null;\n"
                +"int k; k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Boolean i = null;\n"
                +"boolean k; k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Short i = null;\n"
                +"short k; k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Long i = null;\n"
                +"long k; k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Byte i = null;\n"
                +"byte k; k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Double i = null;\n"
                +"double k; k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Float i = null;\n"
                +"float k; k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Character i = null;\n"
                +"char k; k = i; //@ forbid\n"
                +"//@ assert k == i;\n} catch (Exception e) {}\n"

                    +"System.out.println(\"END\"); \n"
                    +"}}"
                    ,"/tt/A.java:4: JML Attempt to unbox a null object"
                    ,"/tt/A.java:8: JML Attempt to unbox a null object"
                    ,"/tt/A.java:12: JML Attempt to unbox a null object"
                    ,"/tt/A.java:16: JML Attempt to unbox a null object"
                    ,"/tt/A.java:20: JML Attempt to unbox a null object"
                    ,"/tt/A.java:24: JML Attempt to unbox a null object"
                    ,"/tt/A.java:28: JML Attempt to unbox a null object"
                    ,"/tt/A.java:32: JML Attempt to unbox a null object"
                    ,"END"
                );

    }

    @Test public void testBoxing() {
        helpTCX("tt.A","package tt; /*@ nullable_by_default*/ public class A { \n"
                +"public static int unbox(int i) { return i;}  \n"
                +"public static Integer box(Integer i) { return i;}  \n"
                +"public static void main(String[] args) {  \n"
                +"try { Boolean i = null;\n"
                +"boolean k = true && i; //@ forbid \n"   // Null problem
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Boolean i = false;\n"
                +"boolean k = true && i;\n"
                +"//@ assert k == false;\n} catch (Exception e) {}\n"
                +"try { Boolean i = null;\n"
                +"boolean k = i && true; //@ forbid \n" // Null problem
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Boolean i = false;\n"
                +"boolean k = i && true;\n"
                +"//@ assert k == false;\n} catch (Exception e) {}\n"
                
                +"try { Integer i = null;\n"
                +"int k = 0 + i; //@ forbid \n"  // Null problem - 22
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Integer i = 6;\n"
                +"int k = 0 + i;\n"
                +"//@ assert k == 6;\n} catch (Exception e) {}\n"
                +"try { Integer i = null;\n"
                +"int k = i + 0; //@ forbid \n" // Null problem - 30
                +"//@ assert k == i;\n} catch (Exception e) {}\n"
                +"try { Integer i = 6;\n"
                +"int k = i + 0;\n"
                +"//@ assert k == 6;\n} catch (Exception e) {}\n"
                +"try { Integer i = null;\n"
                +"int k = - i; //@ forbid \n" // Null problem -- 38
                +"//@ assert k == -i;\n} catch (Exception e) {}\n"
                +"try { Integer i = 6;\n"
                +"int k = - i;\n"
                +"//@ assert k == -6;\n} catch (Exception e) {}\n"
                +"try { Integer i = null;\n"
                +"unbox(i);  \n"  // Null problem -- 46
                +"} catch (Exception e) { System.out.println(\"CAUGHT 46\"); }\n"
                +"try { Integer i = 6;\n"
                +"int k = unbox(i);\n"
                +"//@ assert k == 6;\n} catch (Exception e) {}\n"
                +"try { int i = 6;\n"
                +"Integer k = box(i); int ii = k;\n"
                +"//@ assert ii == 6;\n} catch (Exception e) {}\n"

                +"try { Boolean b = null;\n"
                +"int i = b ? 4 : 5; //@ forbid \n" // Null problem - 57
                +"//@ assert i == 6;\n} catch (Exception e) {}\n"
                +"try { Boolean b = false;\n"
                +"int i = b ? 4 : 5;\n"
                +"//@ assert i == 5;\n} catch (Exception e) {}\n"

                +"try { Boolean b = null;\n"
                +"int i; if (b) i = 4; else i = 5; //@ forbid \n" // Null problem 65
                +"//@ assert i == 6;\n} catch (Exception e) {}\n"
                +"try { Boolean b = false;\n"
                +"int i; if (b) i = 4; else i = 5;\n"
                +"//@ assert i == 5;\n} catch (Exception e) {}\n"
                
                +"System.out.println(\"END\"); \n"
                    +"}}"
                    ,"/tt/A.java:6: JML Attempt to unbox a null object"
                    ,"/tt/A.java:14: JML Attempt to unbox a null object"
                    ,"/tt/A.java:22: JML Attempt to unbox a null object"
                    ,"/tt/A.java:30: JML Attempt to unbox a null object"
                    ,"/tt/A.java:38: JML Attempt to unbox a null object"
                    ,"CAUGHT 46"
                    ,"/tt/A.java:57: JML Attempt to unbox a null object"
                    ,"/tt/A.java:65: JML Attempt to unbox a null object"
                    ,"END"
                );

        // FIXME: Also synchronized expression, switch expression, not on String, conditional, assignop, array index
        // type test, type case, return, loop initializers, array initializers, if condition
    }

    @Test public void testBoxingClass() {
        expectedRACExit = 1;
        helpTCX("tt.A",
                """
                package tt; /*@ nullable_by_default*/ public class A {
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
                    ,"/tt/A.java:10: verify: JML Attempt to unbox a null object"
                    ,"/tt/A.java:13: verify: JML Attempt to unbox a null object"
                    ,"java.lang.ExceptionInInitializerError"
                    ,"Caused by: java.lang.NullPointerException: Cannot invoke \"java.lang.Integer.intValue()\" because \"tt.A.ii\" is null"
                    ,"\tat tt.A.<clinit>(A.java:13)"
                    ,"Exception in thread \"main\" "
                );
    }

    @Test public void testBoxingString() {
        helpTCX("tt.A","package tt; /*@ nullable_by_default*/ public class A { \n"
                +"public static int unbox(int i) { return i;}  \n"
                +"public static Integer box(Integer i) { return i;}  \n"
                +"public static void main(String[] args) {  \n"
                +"try { String s = null;\n"
                +"String ss = \"a\" + s; ss += s; \n" // No null problem // FIXME - crashes on the +=
                +"\n} catch (Exception e) {}\n"

                +"System.out.println(\"END\"); \n"
                    +"}}"
                    ,"END"
                );
    }

    @Test public void testStringSwitch() {
        helpTCX("tt.A","package tt; /*@ nullable_by_default*/ public class A { \n"
                +"public static void main(String[] args) {  \n"
                +"String s = \"abc\"; int k;\n"
                +"switch (s) {\n"
                +"  case \"asd\": k = 1; break;\n"
                +"  case \"abc\": k = 2; break;\n"
                +"  case \"def\": k = 3; break;\n"
                +"  default: k = 4; break;\n"
                +"}\n"
                +"System.out.println(\"END \" + k); \n"
                    +"}}"
                    ,"END 2"
                );
    }

    @Test public void testStringSwitchNull() {
        expectedRACExit = 1;
        helpTCX("tt.A",
                 "package tt; /*@ nullable_by_default*/ public class A { \n"
                +"public static void main(String[] args) {  \n"
                +"String s = null; int k = 0;\n"
                +"{ switch (s) {\n"
                +"  case \"asd\": k = 1; break;\n"
                +"  case \"abc\": k = 2; break;\n"
                +"  case \"def\": k = 3; break;\n"
                +"  default: k = 4; break;\n"
                +"} }\n"
                +"System.out.println(\"END \" + k); \n"
                    +"}}"
                ,"/tt/A.java:4: verify: JML An object may be illegally null"
                ,"Exception in thread \"main\" java.lang.NullPointerException: Cannot invoke \"String.hashCode()\" because \"<local10>\" is null"
                ,"\tat tt.A.main(A.java:4)"
                );
    }

    @Test public void testStringSwitchNullCatch() {
        helpTCX("tt.A","package tt; /*@ nullable_by_default*/ public class A { \n"
                +"public static void main(String[] args) {  \n"
                +"String s = null; int k = 0;\n"
                +"try { switch (s) {\n"
                +"  case \"asd\": k = 1; break;\n"
                +"  case \"abc\": k = 2; break;\n"
                +"  case \"def\": k = 3; break;\n"
                +"  default: k = 4; break;\n"
                +"} } catch (Exception e) { System.out.println(\"CAUGHT\"); }\n" 
                +"System.out.println(\"END \" + k); \n"
                    +"}}"
                ,"CAUGHT"
                ,"END 0"
                );
    }

    @Test public void testEnumSwitch() {
        helpTCX("tt.A","package tt; /*@ nullable_by_default*/ public class A { \n"
                +"enum E { A,B,C}; public static void main(String[] args) {  \n"
                +"E e = E.B; int k = 0;\n"
                +"switch (e) {\n"
                +"  case A: k = 1; break;\n"
                +"  case B: k = 2; break;\n"
                +"  case C: k = 3; break;\n"
                +"  default: k = 4; break;\n"
                +"}\n"
                +"System.out.println(\"END \" + k); \n"
                    +"}}"
                    ,"END 2"
                );
    }


    @Test public void testEnumSwitchNull() {
        expectedRACExit = 1;
        helpTCX("tt.A",
                """
                package tt; /*@ nullable_by_default*/ public class A {
                    enum E { A,B,C};
                    public static void main(String[] args) {
                      E e = null; int k = 0;
                      { switch (e) {
                        case A: k = 1; break;
                        case B: k = 2; break;
                        case C: k = 3; break;
                        default: k = 4; break;
                        }
                      }
                      System.out.println("END " + k);
                   }
                 }
                """
                ,"/tt/A.java:5: verify: JML An object may be illegally null"
                ,"Exception in thread \"main\" java.lang.NullPointerException: Cannot invoke \"tt.A$E.ordinal()\" because \"<local7>\" is null"
                ,"\tat tt.A.main(A.java:5)"
                );
    }


    @Test public void testEnumSwitchNullCatch() {
        helpTCX("tt.A",
                """
                package tt; /*@ nullable_by_default*/ public class A {
                    enum E { A,B,C};
                    public static void main(String[] args) {
                      E e = null; int k = 0;
                      try { switch (e) {
                        case A: k = 1; break;
                        case B: k = 2; break;
                        case C: k = 3; break;
                        default: k = 4; break;
                        }
                      } catch (Exception ee) { System.out.println("CAUGHT");}
                      System.out.println("END " + k);
                   }
                 }
                """
                ,"CAUGHT"
                ,"END 0"
                );
    }


}
