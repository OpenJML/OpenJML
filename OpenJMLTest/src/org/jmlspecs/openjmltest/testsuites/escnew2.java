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
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(int i) throws Exception {
                      if (i == 1) {
                          //@ assert i != 1;
                      } else if (i == 2) {
                          //@ assert false;
                      } else if (i == 3) {
                          //@ assert i != 3;
                      }
                  }
                }
                """
                ,anyorder(
                seq("/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m",15)
                ,seq("/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m",15)
                ,seq("/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m",15)
                )
                );
    }
    
    @Test
    public void testNullReceiver() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m() {};
                  public static void sm() {};
                  public void mm0(/*@ nullable*/TestJava t) throws Exception {
                      t.m();
                  }
                  //@ signals_only Exception;
                  public void mm1(/*@ nullable*/TestJava t) throws Exception {
                      t.m();
                  }
                  //@ signals_only Exception;
                  public void mm2(/*@ nullable*/TestJava t) throws Exception {
                      t.sm();
                  }
                  //@ signals_only Exception;
                  public void mm3(/*@ nullable*/TestJava t) throws Exception {
                      TestJava.sm();
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method mm0",8
                );
    }
    
    @Test public void testReceiver1good() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                public A(int k) { i = k; }
                 public int i;
                 /*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }
                 public void mm(A a) { boolean z;
                //@ assume i == 1 && a.i == 2;
                z = a.m(2);
                }}
                """
                );
    }

    @Test public void testReceiver1bad() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                public A(int k) { i = k; }
                 public int i;
                /*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }
                 public void mm(A a) { boolean z;
                //@ assume i == 1 && a.i == 2;
                z = a.m(1);
                }}
                """
                ,"/tt/A.java:7: verify: The prover cannot establish an assertion (Precondition) in method mm",8
                ,"/tt/A.java:4: verify: Associated declaration",57
                ,"/tt/A.java:4: verify: Precondition conjunct is false: i == j",16
                );
    }

    @Test public void testReceiver2good() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                public A(int k) { i = k; }
                 public int i;
                 /*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }
                 public void mm(A a) { boolean z;
                //@ assume i == 1 && a.i == 2;
                z = m(1);
                }}
                """
                );
    }

    @Test public void testReceiver2bad() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                public A(int k) { i = k; }
                 public int i;
                /*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }
                 public void mm(A a) { boolean z;
                //@ assume i == 1 && a.i == 2;
                z = m(2);
                }}
                """
                ,"/tt/A.java:7: verify: The prover cannot establish an assertion (Precondition) in method mm",6
                ,"/tt/A.java:4: verify: Associated declaration",57
                ,"/tt/A.java:4: verify: Precondition conjunct is false: i == j",16
                );
    }

    @Test public void testReceiver3good() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                public A(int k) { i = k; }
                 public int i;
                 /*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }
                 public void mm(A a) { boolean z;
                //@ assume i == 1 && a.i == 2;
                z = this.m(1);
                }}
                """
                );
    }

    @Test public void testReceiver3bad() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                public A(int k) { i = k; }
                 public int i;
                /*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }
                 public void mm(A a) { boolean z;
                //@ assume i == 1 && a.i == 2;
                z = this.m(2);
                }}
                """
                ,"/tt/A.java:7: verify: The prover cannot establish an assertion (Precondition) in method mm",11
                ,"/tt/A.java:4: verify: Associated declaration",57
                ,"/tt/A.java:4: verify: Precondition conjunct is false: i == j",16
                );
    }

    @Test public void testReceiver4() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                //@ ensures i == k;
                 public A(int k) { i = k; }
                 public int i;
                public static void main(String[] args) {
                A a = new A(1);
                //@ assert a.i == 1;
                }}
                """
                );
    }

    @Test public void testReceiver4a() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                //@ ensures i == k;
                 public A(int k) { i = k; }
                 public int i;
                public static void main(String[] args) {
                A a = new A(1);
                //@ assert a != null;
                }}
                """
                );
    }

    @Test public void testReceiver4bad() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                //@ ensures i == k;
                 public A(int k) { i = k; }
                 public int i;
                public static void main(String[] args) {
                A a = new A(1);
                //@ assert a.i == 2;
                }}
                """
                ,"/tt/A.java:7: verify: The prover cannot establish an assertion (Assert) in method main",5
                );
    }

    @Test public void testReceiver5() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                //@ ensures i == k;
                //@ pure
                 public A(int k) { i = k; }
                 public int i;
                public static void main(String[] args) {
                A a = new A(1);
                A b = new A(2);
                //@ assert a.i == 1;
                //@ assert b.i == 2;
                }}
                """
                );
    }

    @Test public void testReceiver6() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                //@ ensures i == k;
                //@ pure
                 public A(int k) { i = k; }
                 public int i;
                 public static A x;
                public static void main(String[] args) {
                  A a = new A(1);
                  A b = new A(1);
                  //@ assert a != b;
                }
                public void m() {
                  A a = new A(1);
                  //@ assert a != this;
                }
                public void m1(A z) {
                  A a = new A(1);
                  //@ assert a != z;
                }
                public void m2(A z) {
                  A a = new A(1);
                  //@ assert a != x;
                }
                public void m2bad(A z) {
                  //@ assert this != z;
                }
                public void m3bad(A z) {
                  //@ assert x != z;
                }
                }
                """
                ,"/tt/A.java:25: verify: The prover cannot establish an assertion (Assert) in method m2bad",7
                ,"/tt/A.java:28: verify: The prover cannot establish an assertion (Assert) in method m3bad",7
                );
    }

    @Test public void testReturn1good() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                public A(int k) { i = k; }
                 public int i;
                 /*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }
                 public void mm(A a) { boolean z;
                //@ assume i == 1 && a.i == 2;
                z = a.m(2);
                //@ assert z;
                }}
                """
                );
    }

    @Test public void testReturn1bad() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                public A(int k) { i = k; }
                 public int i;
                 /*@ requires i == j; ensures \\result; */ public boolean m(int j) { return true; }
                 public void mm(A a) { boolean z;
                //@ assume i == 1 && a.i == 2;
                z = a.m(2);
                //@ assert !z;
                }}
                """
                ,"/tt/A.java:8: verify: The prover cannot establish an assertion (Assert) in method mm",5
                );
    }

    @Test public void testSuper() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                static public int i;
                 //@ requires k > 0;
                 //@ assignable i;
                 //@ ensures i == k;
                 public A(int k) { i = k; }
                static class B extends A {
                   //@ assignable i;
                   //@ ensures i == 3;
                   public B() { super(3); }
                }}
                """
                );
    }

    @Test public void testSuperbad2() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                static public int i;
                 //@ requires k > 0;
                 //@ assignable i;
                 //@ ensures i == k;
                 public A(int k) { i = k; }
                static class B extends A {
                   //@ assignable i;
                   //@ ensures i == 2;
                   public B() { super(3); }
                }}
                """
                ,"/tt/A.java:10: verify: The prover cannot establish an assertion (Postcondition) in method B",11
                ,"/tt/A.java:9: verify: Associated declaration",8
                );
    }

    @Test public void testSuperbad() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                static public int i;
                 //@ requires k > 0;
                 //@ assignable i;
                 //@ ensures i == k;
                 public A(int k) { i = k; }
                static class B extends A {
                   //@ assignable i;
                   //@ ensures i == 3;
                   public B() { super(0); }
                }}
                """
                ,"/tt/A.java:10: verify: The prover cannot establish an assertion (Precondition) in method B",22
                ,"/tt/A.java:6: verify: Associated declaration",9
                ,"/tt/A.java:3: verify: Precondition conjunct is false: k > 0",17
                );
    }
    
    @Test public void testThis() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                static public int i;
                 //@ requires k > 0;
                 //@ assignable i;
                 //@ ensures i == k;
                 public A(int k) { i = k; }
                //@ assignable i;
                //@ ensures i == 1;
                 public A() { this(1); }
                }
                """
                );
    }

    @Test public void testThisBad() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                static public int i;
                //@ requires k > 0;
                //@ assignable i;
                //@ ensures i == k;
                 public A(int k) { i = k; }
                //@ ensures i == 2;
                //@ assignable i;
                public A() { this(1); }
                }
                """
                ,"/tt/A.java:9: verify: The prover cannot establish an assertion (Postcondition) in method A",8
                ,"/tt/A.java:7: verify: Associated declaration",5
                );
    }

    @Test public void testThisBad2() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                static public int i;
                //@ requires k > 0;
                //@ assignable i;
                //@ ensures i == k;
                 public A(int k) { i = k; }
                //@ ensures i == 0;
                public A() { this(0); }
                }
                """
                ,"/tt/A.java:8: verify: The prover cannot establish an assertion (Precondition) in method A",18
                ,"/tt/A.java:6: verify: Associated declaration",9
                ,"/tt/A.java:3: verify: Precondition conjunct is false: k > 0",16
                );
    }

    @Test public void testNullField() {
        helpEsc("tt.A",
                """
                package tt; import org.jmlspecs.annotation.*; public class A {
                @NonNull static Integer i = 0;
                public void m(@NonNull A a) {
                @Nullable Integer k = a.i;
                //@ assert k != null;
                }
                }
                """
                );
    }

    @Test public void testNullField2() {
        helpEsc("tt.A",
                """
                package tt; import org.jmlspecs.annotation.*; public class A {
                @NonNull static Integer i = 0;
                public void m(@NonNull A a) {
                mm();
                @Nullable Integer k = a.i;
                //@ assert k != null;
                }
                /*@ assignable \\everything; */ public void mm(){}
                }
                """
                );
    }

    @Test public void testNullFieldBad() {
        helpEsc("tt.A",
                """
                package tt; import org.jmlspecs.annotation.*; public class A {
                @Nullable static Integer i;
                public void m(@NonNull A a) {
                @Nullable Integer k = a.i;
                //@ assert k != null;
                }
                }
                """
                ,"/tt/A.java:5: verify: The prover cannot establish an assertion (Assert) in method m",5
                );
    }

    @Test public void testNullFieldBad2() {
        helpEsc("tt.A",
                """
                package tt; import org.jmlspecs.annotation.*; public class A {
                @Nullable static Integer i;
                public void m(@NonNull A a) {
                @NonNull Integer k = a.i;
                }
                }
                """
                ,"/tt/A.java:4: verify: The prover cannot establish an assertion (PossiblyNullInitialization) in method m: k",18
                );
    }

    @Test public void testNullFieldAssign() {
        helpEsc("tt.A",
                """
                package tt; import org.jmlspecs.annotation.*; public class A {
                @NonNull static Integer i = 0;
                public void m(@NonNull A a) {
                @NonNull Integer k = 1;
                a.i = k;
                }
                }
                """
                );
    }

    @Test public void testNullFieldAssignBad2() {
        helpEsc("tt.A",
                """
                package tt; import org.jmlspecs.annotation.*; public class A {
                @NonNull static Integer i = 0;
                public void m(@NonNull A a) {
                @NonNull Integer k = 1;
                a.i = k;
                a.i = null;
                }
                }
                """
                ,"/tt/A.java:6: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m",5
                );
    }

    @Test public void testNullFieldAssignBad() {
        helpEsc("tt.A",
                """
                package tt; import org.jmlspecs.annotation.*; public class A {
                @NonNull static Integer i = 0;
                public void m(@NonNull A a, @Nullable Integer k) {
                a.i = k;
                }
                }
                """
                ,"/tt/A.java:4: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m",5
                );
    }

    @Test
    public void testBreak() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures i == 0 ==> \\result == 6;
                  //@ ensures i == 1 ==> \\result == 1;
                  //@ ensures i == 2 ==> \\result == 0;
                  public int m1good(int i) throws Exception {
                      int k = 0;
                       out: {
                        in: { if (i ==1) break in;
                              if (i ==2) break out;
                              k=5;
                        } k++;
                       }
                      return k;
                  }
                  //@ ensures i == 0 ==> \\result == 7;
                  //@ ensures i == 1 ==> \\result == 1;
                  //@ ensures i == 2 ==> \\result == 0;
                  public int m1bad(int i) throws Exception {
                      int k = 0;
                       out: {
                        in: { if (i ==1) break in;
                              if (i ==2) break out;
                              k=5;
                        } k++;
                       }
                      return k;
                  }
                  //@ ensures i == 0 ==> \\result == 6;
                  //@ ensures i == 1 ==> \\result == 2;
                  //@ ensures i == 2 ==> \\result == 0;
                  public int m2bad(int i) throws Exception {
                      int k = 0;
                       out: {
                        in: { if (i ==1) break in;
                              if (i ==2) break out;
                              k=5;
                        } k++;
                       }
                      return k;
                  }
                  //@ ensures i == 0 ==> \\result == 6;
                  //@ ensures i == 1 ==> \\result == 1;
                  //@ ensures i == 2 ==> \\result == 9;
                  public int m3bad(int i) throws Exception {
                      int k = 0;
                       out: {
                        in: { if (i ==1) break in;
                              if (i ==2) break out;
                              k=5;
                        } k++;
                       }
                      return k;
                  }
                }
                """
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
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures i == 0 ==> \\result == 2;
                  //@ ensures i == 1 ==> \\result == 3;
                  //@ ensures i == 2 ==> \\result == 5;
                  public int m1good(int i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i==1) { k=3; break;} else break;
                        case 2: k = 5;
                       } return k;
                  }
                  //@ ensures i == 0 ==> \\result == 0;
                  //@ ensures i == 1 ==> \\result == 3;
                  //@ ensures i == 2 ==> \\result == 5;
                  public int m1bad(int i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i==1) { k=3; break;} else break;
                        case 2: k = 5;
                       } return k;
                  }
                  //@ ensures i == 0 ==> \\result == 2;
                  //@ ensures i == 1 ==> \\result == 0;
                  //@ ensures i == 2 ==> \\result == 5;
                  public int m2bad(int i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i==1) { k=3; break;} else break;
                        case 2: k = 5;
                       } return k;
                  }
                  //@ ensures i == 0 ==> \\result == 2;
                  //@ ensures i == 1 ==> \\result == 3;
                  //@ ensures i == 2 ==> \\result == 0;
                  public int m3bad(int i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i==1) { k=3; break;} else break;
                        case 2: k = 5;
                       } return k;
                  }
                }
                """
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
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures i == 0 ==> \\result == 2;
                  //@ ensures i == 1 ==> \\result == 3;
                  //@ ensures i == 2 ==> \\result == 5;
                  public int m1good(short i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i==1) { k=3; break;} else break;
                        case 2: k = 5;
                       } return k;
                  }
                  //@ ensures i == 0 ==> \\result == 0;
                  //@ ensures i == 1 ==> \\result == 3;
                  //@ ensures i == 2 ==> \\result == 5;
                  public int m1bad(short i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i==1) { k=3; break;} else break;
                        case 2: k = 5;
                       } return k;
                  }
                  //@ ensures i == 0 ==> \\result == 2;
                  //@ ensures i == 1 ==> \\result == 0;
                  //@ ensures i == 2 ==> \\result == 5;
                  public int m2bad(short i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i==1) { k=3; break;} else break;
                        case 2: k = 5;
                       } return k;
                  }
                  //@ ensures i == 0 ==> \\result == 2;
                  //@ ensures i == 1 ==> \\result == 3;
                  //@ ensures i == 2 ==> \\result == 0;
                  public int m3bad(short i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i==1) { k=3; break;} else break;
                        case 2: k = 5;
                       } return k;
                  }
                }
                """
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
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures i == 0 ==> \\result == 2;
                  //@ ensures i == 1 ==> \\result == 3;
                  //@ ensures i == 2 ==> \\result == 5;
                  public int m1good(byte i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i==1) { k=3; break;} else break;
                        case 2: k = 5;
                       } return k;
                  }
                  //@ ensures i == 0 ==> \\result == 0;
                  //@ ensures i == 1 ==> \\result == 3;
                  //@ ensures i == 2 ==> \\result == 5;
                  public int m1bad(byte i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i==1) { k=3; break;} else break;
                        case 2: k = 5;
                       } return k;
                  }
                  //@ ensures i == 0 ==> \\result == 2;
                  //@ ensures i == 1 ==> \\result == 0;
                  //@ ensures i == 2 ==> \\result == 5;
                  public int m2bad(byte i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i==1) { k=3; break;} else break;
                        case 2: k = 5;
                       } return k;
                  }
                  //@ ensures i == 0 ==> \\result == 2;
                  //@ ensures i == 1 ==> \\result == 3;
                  //@ ensures i == 2 ==> \\result == 0;
                  public int m3bad(byte i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i==1) { k=3; break;} else break;
                        case 2: k = 5;
                       } return k;
                  }
                }
                """
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
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures i == 'z' ==> \\result == 2;
                  //@ ensures i == 'a' ==> \\result == 3;
                  //@ ensures i == 'b' ==> \\result == 5;
                  public int m1good(char i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i=='a') { k=3; break;} else break;
                        case 'b': k = 5;
                       } return k;
                  }
                  //@ ensures i == 'z' ==> \\result == 0;
                  //@ ensures i == 'a' ==> \\result == 3;
                  //@ ensures i == 'b' ==> \\result == 5;
                  public int m1bad(byte i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i=='a') { k=3; break;} else break;
                        case 'b': k = 5;
                       } return k;
                  }
                  //@ ensures i == 'z' ==> \\result == 2;
                  //@ ensures i == 'a' ==> \\result == 0;
                  //@ ensures i == 'b' ==> \\result == 5;
                  public int m2bad(byte i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i=='a') { k=3; break;} else break;
                        case 'b': k = 5;
                       } return k;
                  }
                  //@ ensures i == 'z' ==> \\result == 2;
                  //@ ensures i == 'a' ==> \\result == 3;
                  //@ ensures i == 'b' ==> \\result == 0;
                  public int m3bad(byte i) throws Exception {
                      int k = 2;
                       switch (i) {
                        default: if (i=='a') { k=3; break;} else break;
                        case 'b': k = 5;
                       } return k;
                  }
                }
                """
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
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures i == 0 ==> \\result == 5;
                  //@ ensures i == 1 ==> \\result == 1;
                  //@ ensures i == 2 ==> \\result == 2;
                  //@ ensures i == 3 ==> \\result == 3;
                  //@ ensures i == 4 ==> \\result == 3;
                  public int m1good(int i) throws Exception {
                      try {
                        try { if (i>=1) return 1;
                        } finally {
                          if (i==2 || i == 4) return 2;
                        }
                      } finally {
                          if (i>=3) return 3;
                      }
                      return 5;
                  }
                  //@ ensures i == 0 ==> \\result == 0;
                  //@ ensures i == 1 ==> \\result == 1;
                  //@ ensures i == 2 ==> \\result == 2;
                  //@ ensures i == 3 ==> \\result == 3;
                  //@ ensures i == 4 ==> \\result == 3;
                  public int m1bad(int i) throws Exception {
                      try {
                        try { if (i>=1) return 1;
                        } finally {
                          if (i==2 || i == 4) return 2;
                        }
                      } finally {
                          if (i>=3) return 3;
                      }
                      return 5;
                  }
                  //@ ensures i == 0 ==> \\result == 5;
                  //@ ensures i == 1 ==> \\result == 0;
                  //@ ensures i == 2 ==> \\result == 2;
                  //@ ensures i == 3 ==> \\result == 3;
                  //@ ensures i == 4 ==> \\result == 3;
                  public int m2bad(int i) throws Exception {
                      try {
                        try { if (i>=1) return 1;
                        } finally {
                          if (i==2 || i == 4) return 2;
                        }
                      } finally {
                          if (i>=3) return 3;
                      }
                      return 5;
                  }
                  //@ ensures i == 0 ==> \\result == 5;
                  //@ ensures i == 1 ==> \\result == 1;
                  //@ ensures i == 2 ==> \\result == 0;
                  //@ ensures i == 3 ==> \\result == 3;
                  //@ ensures i == 4 ==> \\result == 3;
                  public int m3bad(int i) throws Exception {
                      try {
                        try { if (i>=1) return 1;
                        } finally {
                          if (i==2 || i == 4) return 2;
                        }
                      } finally {
                          if (i>=3) return 3;
                      }
                      return 5;
                  }
                  //@ ensures i == 0 ==> \\result == 5;
                  //@ ensures i == 1 ==> \\result == 1;
                  //@ ensures i == 2 ==> \\result == 2;
                  //@ ensures i == 3 ==> \\result == 0;
                  //@ ensures i == 4 ==> \\result == 3;
                  public int m4bad(int i) throws Exception {
                      try {
                        try { if (i>=1) return 1;
                        } finally {
                          if (i==2 || i == 4) return 2;
                        }
                      } finally {
                          if (i>=3) return 3;
                      }
                      return 5;
                  }
                  //@ ensures i == 0 ==> \\result == 5;
                  //@ ensures i == 1 ==> \\result == 1;
                  //@ ensures i == 2 ==> \\result == 2;
                  //@ ensures i == 3 ==> \\result == 3;
                  //@ ensures i == 4 ==> \\result == 0;
                  public int m5bad(int i) throws Exception {
                      try {
                        try { if (i>=1) return 1;
                        } finally {
                          if (i==2 || i == 4) return 2;
                        }
                      } finally {
                          if (i>=3) return 3;
                      }
                      return 5;
                  }
                }
                """
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
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                 public java.util.LinkedList<Object> list = new java.util.LinkedList<>();
                 //@ assigns list.objectState;
                 public void m(Object o) { list.add(o); }
                }
                """
                );
    }
}
