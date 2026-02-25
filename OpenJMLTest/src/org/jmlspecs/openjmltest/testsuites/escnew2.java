package org.jmlspecs.openjmltest.testsuites;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escnew2 extends EscBase {

    @Test
    public void testMultiple() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m(int i) throws Exception {\n"
                +"      if (i == 1) {\n"
                +"          //@ assert i != 1;\n"
                +"      } else if (i == 2) {\n"
                +"          //@ assert false;\n"
                +"      } else if (i == 3) {\n"
                +"          //@ assert i != 3;\n"
                +"      }\n"
                +"  }\n"
                
                +"}"
                ,anyorder(
                seq("/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m",15)
                ,seq("/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m",15)
                ,seq("/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m",15)
                )
                );
    }
    
    @Test
    public void testNullReceiver() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m() {}; \n"
                
                +"  public static void sm() {}; \n"
                
                +"  public void mm0(/*@ nullable*/TestJava t) throws Exception {\n"
                +"      t.m();\n"
                +"  }\n"
                
                +"  //@ signals_only Exception; \n"
                +"  public void mm1(/*@ nullable*/TestJava t) throws Exception {\n"
                +"      t.m();\n"
                +"  }\n"
                
                +"  //@ signals_only Exception; \n"
                +"  public void mm2(/*@ nullable*/TestJava t) throws Exception {\n"
                +"      t.sm();\n"
                +"  }\n"
                
                +"  //@ signals_only Exception; \n"
                +"  public void mm3(/*@ nullable*/TestJava t) throws Exception {\n"
                +"      TestJava.sm();\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method mm0",8
                );
    }
    
    @Test public void testReceiver1good() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"public A(int k) { i = k; } \n "
                +"public int i; \n "
                +"/*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }\n "
                +"public void mm(A a) { boolean z; \n"
                +"//@ assume i == 1 && a.i == 2;\n"
                +"z = a.m(2); \n"
                +"}}"
                );
    }

    @Test public void testReceiver1bad() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"public A(int k) { i = k; } \n "
                +"public int i; \n"
                +"/*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }\n "
                +"public void mm(A a) { boolean z; \n"
                +"//@ assume i == 1 && a.i == 2;\n"
                +"z = a.m(1); \n"
                +"}}"
                ,"/tt/A.java:7: verify: The prover cannot establish an assertion (Precondition) in method mm",8
                ,"/tt/A.java:4: verify: Associated declaration",57
                ,"/tt/A.java:4: verify: Precondition conjunct is false: i == j",16
                );
    }

    @Test public void testReceiver2good() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"public A(int k) { i = k; } \n "
                +"public int i; \n "
                +"/*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }\n "
                +"public void mm(A a) { boolean z; \n"
                +"//@ assume i == 1 && a.i == 2;\n"
                +"z = m(1); \n"
                +"}}"
                );
    }

    @Test public void testReceiver2bad() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"public A(int k) { i = k; } \n "
                +"public int i; \n"
                +"/*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }\n "
                +"public void mm(A a) { boolean z; \n"
                +"//@ assume i == 1 && a.i == 2;\n"
                +"z = m(2); \n"
                +"}}"
                ,"/tt/A.java:7: verify: The prover cannot establish an assertion (Precondition) in method mm",6
                ,"/tt/A.java:4: verify: Associated declaration",57
                ,"/tt/A.java:4: verify: Precondition conjunct is false: i == j",16
                );
    }

    @Test public void testReceiver3good() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"public A(int k) { i = k; } \n "
                +"public int i; \n "
                +"/*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }\n "
                +"public void mm(A a) { boolean z; \n"
                +"//@ assume i == 1 && a.i == 2;\n"
                +"z = this.m(1); \n"
                +"}}"
                );
    }

    @Test public void testReceiver3bad() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"public A(int k) { i = k; } \n "
                +"public int i;\n"
                +"/*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }\n "
                +"public void mm(A a) { boolean z; \n"
                +"//@ assume i == 1 && a.i == 2;\n"
                +"z = this.m(2); \n"
                +"}}"
                ,"/tt/A.java:7: verify: The prover cannot establish an assertion (Precondition) in method mm",11
                ,"/tt/A.java:4: verify: Associated declaration",57
                ,"/tt/A.java:4: verify: Precondition conjunct is false: i == j",16
                );
    }

    @Test public void testReceiver4() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"//@ ensures i == k; \n "
                +"public A(int k) { i = k; } \n"
                
                +" public int i; \n"
                
                +"public static void main(String[] args) {  \n"
                +"A a = new A(1);\n"
                +"//@ assert a.i == 1;\n"
                
                +"}}"
                );
    }

    @Test public void testReceiver4a() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"//@ ensures i == k; \n "
                +"public A(int k) { i = k; } \n"
                
                +" public int i; \n"
                
                +"public static void main(String[] args) {  \n"
                +"A a = new A(1);\n"
                +"//@ assert a != null;\n"
                
                +"}}"
                );
    }

    @Test public void testReceiver4bad() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"//@ ensures i == k; \n "
                +"public A(int k) { i = k; } \n"
                
                +" public int i; \n"
                
                +"public static void main(String[] args) { \n"
                +"A a = new A(1);\n"
                +"//@ assert a.i == 2;\n"
                +"}}"
                ,"/tt/A.java:7: verify: The prover cannot establish an assertion (Assert) in method main",5
                );
    }

     @Test public void testReceiver5() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"//@ ensures i == k; pure \n "
                +"public A(int k) { i = k; } \n"
                
                +" public int i; \n"
                
                +"public static void main(String[] args) {  \n"
                +"A a = new A(1);\n"
                +"A b = new A(2);\n"
                +"//@ assert a.i == 1;\n"
                +"//@ assert b.i == 2;\n"
                +"}}"
                );
    }

    @Test public void testReceiver6() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"//@ ensures i == k; pure \n "
                +"public A(int k) { i = k; } \n"
                
                +" public int i; \n"
                +" public static A x; \n"
                
                +"public static void main(String[] args) { \n"
                +"  A a = new A(1);\n"
                +"  A b = new A(1);\n"
                +"  //@ assert a != b; \n"
                +"}\n"
                
                +"public void m() { \n"
                +"  A a = new A(1);\n"
                +"  //@ assert a != this; \n"
                +"}\n"
                
                +"public void m1(A z) { \n"
                +"  A a = new A(1);\n"
                +"  //@ assert a != z; \n"
                +"}\n"
                
                +"public void m2(A z) { \n"
                +"  A a = new A(1);\n"
                +"  //@ assert a != x; \n"
                +"}\n"
                
                +"public void m2bad(A z) { \n"
                +"  //@ assert this != z; \n" // Not necessarily
                +"}\n"
                
                +"public void m3bad(A z) { \n"
                +"  //@ assert x != z; \n" // Not necessarily
                +"}\n"
                +"}"
                ,"/tt/A.java:24: verify: The prover cannot establish an assertion (Assert) in method m2bad",7
                ,"/tt/A.java:27: verify: The prover cannot establish an assertion (Assert) in method m3bad",7
                );
    }

    @Test public void testReturn1good() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"public A(int k) { i = k; } \n "
                +"public int i; \n "
                +"/*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }\n "
                +"public void mm(A a) { boolean z; \n"
                +"//@ assume i == 1 && a.i == 2;\n"
                +"z = a.m(2); \n"
                +"//@ assert z; \n"
                +"}}"
                );
    }

    @Test public void testReturn1bad() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"public A(int k) { i = k; } \n "
                +"public int i; \n "
                +"/*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }\n "
                +"public void mm(A a) { boolean z; \n"
                +"//@ assume i == 1 && a.i == 2;\n"
                +"z = a.m(2); \n"
                +"//@ assert !z; \n"
                +"}}"
                ,"/tt/A.java:8: verify: The prover cannot establish an assertion (Assert) in method mm",5
                );
    }

    @Test public void testSuper() {
        helpEsc("tt.A","package tt; public class A { \n"
                +"static public int i; \n "
                +"//@ requires k > 0; assignable i; ensures i == k; \n "
                +"public A(int k) { i = k; } \n"
                +"static class B extends A {\n"
                +"   //@ assignable i; ensures i == 3;\n"
                +"   public B() { super(3); }\n"
                +"}}"
                );
    }

    @Test public void testSuperbad2() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"static public int i; \n "
                +"//@ requires k > 0; assignable i; ensures i == k; \n "
                +"public A(int k) { i = k; } \n"
                +"static class B extends A {\n"
                +"   //@ assignable i; ensures i == 2;\n"
                +"   public B() { super(3); }\n"
                +"}}"
                ,"/tt/A.java:7: verify: The prover cannot establish an assertion (Postcondition) in method B",11
                ,"/tt/A.java:6: verify: Associated declaration",22
                );
    }

    @Test public void testSuperbad() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"static public int i; \n "
                +"//@ requires k > 0; assignable i; ensures i == k; \n "
                +"public A(int k) { i = k; } \n"
                +"static class B extends A {\n"
                +"   //@ assignable i; ensures i == 3;\n"
                +"   public B() { super(0); }\n"
                +"}}"
                ,"/tt/A.java:7: verify: The prover cannot establish an assertion (Precondition) in method B",22
                ,"/tt/A.java:4: verify: Associated declaration",9
                ,"/tt/A.java:3: verify: Precondition conjunct is false: k > 0",17
                );
    }
    
    @Test public void testThis() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"static public int i; \n "
                +"//@ requires k > 0; assignable i; ensures i == k; \n "
                +"public A(int k) { i = k; } \n"
                +"//@ assignable i; ensures i == 1; \n "
                +"public A() { this(1); } \n"
                +"}"
                );
    }

    @Test public void testThisBad() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"static public int i; \n"
                +"//@ requires k > 0; assignable i; ensures i == k; \n "
                +"public A(int k) { i = k; } \n"
                +"//@ ensures i == 2; assignable i; \n"
                +"public A() { this(1); } \n"
                +"}"
                ,"/tt/A.java:6: verify: The prover cannot establish an assertion (Postcondition) in method A",8
                ,"/tt/A.java:5: verify: Associated declaration",5
                );
    }

    @Test public void testThisBad2() { 
        helpEsc("tt.A","package tt; public class A { \n"
                +"static public int i; \n"
                +"//@ requires k > 0; assignable i; ensures i == k; \n "
                +"public A(int k) { i = k; }\n"
                +"//@ ensures i == 0; \n"
                +"public A() { this(0); }\n"
                +"}"
                ,"/tt/A.java:6: verify: The prover cannot establish an assertion (Precondition) in method A",18
                ,"/tt/A.java:4: verify: Associated declaration",9
                ,"/tt/A.java:3: verify: Precondition conjunct is false: k > 0",16
                );
    }

    @Test public void testNullField() { 
        helpEsc("tt.A","package tt; import org.jmlspecs.annotation.*; public class A { \n"
                +"@NonNull static Integer i = 0; \n"
                +"public void m(@NonNull A a) { \n"
                +"@Nullable Integer k = a.i; \n"
                +"//@ assert k != null; \n"
                +"}\n"
                +"}"
                );
    }

    @Test public void testNullField2() { 
        helpEsc("tt.A","package tt; import org.jmlspecs.annotation.*; public class A { \n"
                +"@NonNull static Integer i = 0; \n"
                +"public void m(@NonNull A a) { \n"
                +"mm(); \n"
                +"@Nullable Integer k = a.i; \n"
                +"//@ assert k != null; \n"
                +"}\n"
                +"/*@ assignable \\everything; */ public void mm(){}\n"
                +"}"
                );
    }

    @Test public void testNullFieldBad() { 
        helpEsc("tt.A","package tt; import org.jmlspecs.annotation.*; public class A { \n"
                +"@Nullable static Integer i; \n"
                +"public void m(@NonNull A a) { \n"
                +"@Nullable Integer k = a.i; \n"
                +"//@ assert k != null; \n"
                +"}\n"
                +"}"
                ,"/tt/A.java:5: verify: The prover cannot establish an assertion (Assert) in method m",5
                );
    }

    @Test public void testNullFieldBad2() { 
        helpEsc("tt.A","package tt; import org.jmlspecs.annotation.*; public class A { \n"
                +"@Nullable static Integer i; \n"
                +"public void m(@NonNull A a) { \n"
                +"@NonNull Integer k = a.i; \n"
                +"}\n"
                +"}"
                ,"/tt/A.java:4: verify: The prover cannot establish an assertion (PossiblyNullInitialization) in method m: k",18
                );
    }

    @Test public void testNullFieldAssign() { 
        helpEsc("tt.A","package tt; import org.jmlspecs.annotation.*; public class A { \n"
                +"@NonNull static Integer i = 0; \n"
                +"public void m(@NonNull A a) { \n"
                +"@NonNull Integer k = 1; \n"
                +"a.i = k; \n"
                +"}\n"
                +"}"
                );
    }

    @Test public void testNullFieldAssignBad2() { 
        helpEsc("tt.A","package tt; import org.jmlspecs.annotation.*; public class A { \n"
                +"@NonNull static Integer i = 0; \n"
                +"public void m(@NonNull A a) { \n"
                +"@NonNull Integer k = 1; \n"
                +"a.i = k; \n"
                +"a.i = null; \n"
                +"}\n"
                +"}"
                ,"/tt/A.java:6: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m",5
                );
    }

    @Test public void testNullFieldAssignBad() { 
        helpEsc("tt.A","package tt; import org.jmlspecs.annotation.*; public class A { \n"
                +"@NonNull static Integer i = 0; \n"
                +"public void m(@NonNull A a, @Nullable Integer k) { \n"
                +"a.i = k; \n"
                +"}\n"
                +"}"
                ,"/tt/A.java:4: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m",5
                );
    }

    @Test
    public void testBreak() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures i == 0 ==> \\result == 6; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n"
                +"  public int m1good(int i) throws Exception {\n"
                +"      int k = 0;\n"
                +"       out: {\n"
                +"        in: { if (i ==1) break in;\n"
                +"              if (i ==2) break out;\n"
                +"              k=5;\n"
                +"        } k++; \n"
                +"       } \n"
                +"      return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 7; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n"
                +"  public int m1bad(int i) throws Exception { \n" // Line 19
                +"      int k = 0;\n"
                +"       out: {\n"
                +"        in: { if (i ==1) break in;\n"
                +"              if (i ==2) break out;\n"
                +"              k=5; \n" 
                +"        } k++; \n"
                +"       } \n"
                +"      return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 6; \n"
                +"  //@ ensures i == 1 ==> \\result == 2; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n"
                +"  public int m2bad(int i) throws Exception {\n"
                +"      int k = 0;\n"
                +"       out: {\n"
                +"        in: { if (i ==1) break in;\n"
                +"              if (i ==2) break out;\n"
                +"              k=5;\n"
                +"        } k++; \n"
                +"       } \n"
                +"      return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 6; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 9; \n"
                +"  public int m3bad(int i) throws Exception {\n"
                +"      int k = 0;\n"
                +"       out: {\n"
                +"        in: { if (i ==1) break in;\n"
                +"              if (i ==2) break out;\n"
                +"              k=5;\n"
                +"        } k++; \n"
                +"       } \n"
                +"      return k;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:27: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",7
                ,"/tt/TestJava.java:16: verify: Associated declaration",7
                ,"/tt/TestJava.java:40: verify: The prover cannot establish an assertion (Postcondition) in method m2bad",7
                ,"/tt/TestJava.java:30: verify: Associated declaration",7
                ,"/tt/TestJava.java:53: verify: The prover cannot establish an assertion (Postcondition) in method m3bad",7
                ,"/tt/TestJava.java:44: verify: Associated declaration",7
                );
    }
    
    @Test
    public void testSwitch2() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures i == 0 ==> \\result == 2; \n"
                +"  //@ ensures i == 1 ==> \\result == 3; \n"
                +"  //@ ensures i == 2 ==> \\result == 5; \n"
                +"  public int m1good(int i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 0; \n"
                +"  //@ ensures i == 1 ==> \\result == 3; \n"
                +"  //@ ensures i == 2 ==> \\result == 5; \n"
                +"  public int m1bad(int i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 2; \n"
                +"  //@ ensures i == 1 ==> \\result == 0; \n"
                +"  //@ ensures i == 2 ==> \\result == 5; \n"
                +"  public int m2bad(int i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 2; \n"
                +"  //@ ensures i == 1 ==> \\result == 3; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n"
                +"  public int m3bad(int i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",10
                ,"/tt/TestJava.java:13: verify: Associated declaration",7
                ,"/tt/TestJava.java:31: verify: The prover cannot establish an assertion (Postcondition) in method m2bad",10
                ,"/tt/TestJava.java:24: verify: Associated declaration",7
                ,"/tt/TestJava.java:41: verify: The prover cannot establish an assertion (Postcondition) in method m3bad",10
                ,"/tt/TestJava.java:35: verify: Associated declaration",7
                );
    }
    
    @Test
    public void testSwitchShort() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures i == 0 ==> \\result == 2; \n"
                +"  //@ ensures i == 1 ==> \\result == 3; \n"
                +"  //@ ensures i == 2 ==> \\result == 5; \n"
                +"  public int m1good(short i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 0; \n"
                +"  //@ ensures i == 1 ==> \\result == 3; \n"
                +"  //@ ensures i == 2 ==> \\result == 5; \n"
                +"  public int m1bad(short i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 2; \n"
                +"  //@ ensures i == 1 ==> \\result == 0; \n"
                +"  //@ ensures i == 2 ==> \\result == 5; \n"
                +"  public int m2bad(short i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 2; \n"
                +"  //@ ensures i == 1 ==> \\result == 3; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n"
                +"  public int m3bad(short i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",10
                ,"/tt/TestJava.java:13: verify: Associated declaration",7
                ,"/tt/TestJava.java:31: verify: The prover cannot establish an assertion (Postcondition) in method m2bad",10
                ,"/tt/TestJava.java:24: verify: Associated declaration",7
                ,"/tt/TestJava.java:41: verify: The prover cannot establish an assertion (Postcondition) in method m3bad",10
                ,"/tt/TestJava.java:35: verify: Associated declaration",7
                );
    }
    
    @Test
    public void testSwitchByte() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures i == 0 ==> \\result == 2; \n"
                +"  //@ ensures i == 1 ==> \\result == 3; \n"
                +"  //@ ensures i == 2 ==> \\result == 5; \n"
                +"  public int m1good(byte i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 0; \n"
                +"  //@ ensures i == 1 ==> \\result == 3; \n"
                +"  //@ ensures i == 2 ==> \\result == 5; \n"
                +"  public int m1bad(byte i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 2; \n"
                +"  //@ ensures i == 1 ==> \\result == 0; \n"
                +"  //@ ensures i == 2 ==> \\result == 5; \n"
                +"  public int m2bad(byte i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 2; \n"
                +"  //@ ensures i == 1 ==> \\result == 3; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n"
                +"  public int m3bad(byte i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",10
                ,"/tt/TestJava.java:13: verify: Associated declaration",7
                ,"/tt/TestJava.java:31: verify: The prover cannot establish an assertion (Postcondition) in method m2bad",10
                ,"/tt/TestJava.java:24: verify: Associated declaration",7
                ,"/tt/TestJava.java:41: verify: The prover cannot establish an assertion (Postcondition) in method m3bad",10
                ,"/tt/TestJava.java:35: verify: Associated declaration",7
                );
    }
    
    @Test
    public void testSwitchChar() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures i == 'z' ==> \\result == 2; \n"
                +"  //@ ensures i == 'a' ==> \\result == 3; \n"
                +"  //@ ensures i == 'b' ==> \\result == 5; \n"
                +"  public int m1good(char i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i=='a') { k=3; break;} else break; \n"
                +"        case 'b': k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 'z' ==> \\result == 0; \n"
                +"  //@ ensures i == 'a' ==> \\result == 3; \n"
                +"  //@ ensures i == 'b' ==> \\result == 5; \n"
                +"  public int m1bad(byte i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i=='a') { k=3; break;} else break; \n"
                +"        case 'b': k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 'z' ==> \\result == 2; \n"
                +"  //@ ensures i == 'a' ==> \\result == 0; \n"
                +"  //@ ensures i == 'b' ==> \\result == 5; \n"
                +"  public int m2bad(byte i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i=='a') { k=3; break;} else break; \n"
                +"        case 'b': k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 'z' ==> \\result == 2; \n"
                +"  //@ ensures i == 'a' ==> \\result == 3; \n"
                +"  //@ ensures i == 'b' ==> \\result == 0; \n"
                +"  public int m3bad(byte i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i=='a') { k=3; break;} else break; \n"
                +"        case 'b': k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",10
                ,"/tt/TestJava.java:13: verify: Associated declaration",7
                ,"/tt/TestJava.java:31: verify: The prover cannot establish an assertion (Postcondition) in method m2bad",10
                ,"/tt/TestJava.java:24: verify: Associated declaration",7
                ,"/tt/TestJava.java:41: verify: The prover cannot establish an assertion (Postcondition) in method m3bad",10
                ,"/tt/TestJava.java:35: verify: Associated declaration",7
                );
    }
    
    @Test
    public void testTryNested() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures i == 0 ==> \\result == 5; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 2; \n"
                +"  //@ ensures i == 3 ==> \\result == 3; \n"
                +"  //@ ensures i == 4 ==> \\result == 3; \n"
                +"  public int m1good(int i) throws Exception {\n" // Line 8
                +"      try {\n"
                +"        try { if (i>=1) return 1; \n"
                +"        } finally { \n"
                +"          if (i==2 || i == 4) return 2; \n"
                +"        }\n"
                +"      } finally { \n"
                +"          if (i>=3) return 3; \n"
                +"      }\n"
                +"      return 5;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 0; \n" // ERROR
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 2; \n"
                +"  //@ ensures i == 3 ==> \\result == 3; \n"
                +"  //@ ensures i == 4 ==> \\result == 3; \n"
                +"  public int m1bad(int i) throws Exception {\n" // Line 24
                +"      try {\n"
                +"        try { if (i>=1) return 1; \n"
                +"        } finally { \n"
                +"          if (i==2 || i == 4) return 2; \n"
                +"        }\n"
                +"      } finally { \n"
                +"          if (i>=3) return 3; \n"
                +"      }\n"
                +"      return 5;\n" // ERROR
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 5; \n"
                +"  //@ ensures i == 1 ==> \\result == 0; \n" // ERROR
                +"  //@ ensures i == 2 ==> \\result == 2; \n"
                +"  //@ ensures i == 3 ==> \\result == 3; \n"
                +"  //@ ensures i == 4 ==> \\result == 3; \n"
                +"  public int m2bad(int i) throws Exception {\n" // Line 40
                +"      try {\n"
                +"        try { if (i>=1) return 1; \n" // ERROR
                +"        } finally { \n"
                +"          if (i==2 || i == 4) return 2; \n"
                +"        }\n"
                +"      } finally { \n"
                +"          if (i>=3) return 3; \n"
                +"      }\n"
                +"      return 5;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 5; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n" // ERROR
                +"  //@ ensures i == 3 ==> \\result == 3; \n"
                +"  //@ ensures i == 4 ==> \\result == 3; \n"
                +"  public int m3bad(int i) throws Exception {\n" // Line 56
                +"      try {\n"
                +"        try { if (i>=1) return 1; \n"
                +"        } finally { \n"
                +"          if (i==2 || i == 4) return 2; \n" // ERROR
                +"        }\n"
                +"      } finally { \n"
                +"          if (i>=3) return 3; \n"
                +"      }\n"
                +"      return 5;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 5; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 2; \n"
                +"  //@ ensures i == 3 ==> \\result == 0; \n" // ERROR
                +"  //@ ensures i == 4 ==> \\result == 3; \n"
                +"  public int m4bad(int i) throws Exception {\n" // Line 72
                +"      try {\n"
                +"        try { if (i>=1) return 1; \n"
                +"        } finally { \n"
                +"          if (i==2 || i == 4) return 2; \n"
                +"        }\n"
                +"      } finally { \n"
                +"          if (i>=3) return 3; \n" // ERROR
                +"      }\n"
                +"      return 5;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 5; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 2; \n"
                +"  //@ ensures i == 3 ==> \\result == 3; \n"
                +"  //@ ensures i == 4 ==> \\result == 0; \n" // ERROR
                +"  public int m5bad(int i) throws Exception {\n" // Line 88
                +"      try {\n"
                +"        try { if (i>=1) return 1; \n"
                +"        } finally { \n"
                +"          if (i==2 || i == 4) return 2; \n"
                +"        }\n"
                +"      } finally { \n"
                +"          if (i>=3) return 3; \n" // ERROR
                +"      }\n"
                +"      return 5;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:33: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",7
                ,"/tt/TestJava.java:19: verify: Associated declaration",7
                ,"/tt/TestJava.java:42: verify: The prover cannot establish an assertion (Postcondition) in method m2bad",25
                ,"/tt/TestJava.java:36: verify: Associated declaration",7
                ,"/tt/TestJava.java:60: verify: The prover cannot establish an assertion (Postcondition) in method m3bad",31
                ,"/tt/TestJava.java:53: verify: Associated declaration",7
                ,"/tt/TestJava.java:79: verify: The prover cannot establish an assertion (Postcondition) in method m4bad",21
                ,"/tt/TestJava.java:70: verify: Associated declaration",7
                ,"/tt/TestJava.java:95: verify: The prover cannot establish an assertion (Postcondition) in method m5bad",21
                ,"/tt/TestJava.java:87: verify: Associated declaration",7
                );
    }
    
    @Test
    public void testAdd() { // Tests datagroup expansion
        helpEsc("tt.TestJava","package tt; \n"
           +"public class TestJava { \n"
           +" public java.util.LinkedList<Object> list = new java.util.LinkedList<>(); \n"
           +" //@ assigns list.objectState;  \n"
           +" public void m(Object o) { list.add(o); } \n"
           +"}\n"
           );
    }
}
