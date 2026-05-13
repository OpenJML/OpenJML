package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
// @RunWith(ParameterizedWithNames.class)
public class escall2 extends EscBase {

    public escall2() {
        super(null,"z3_4_3");
    }


    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        addOptions("--nullable-by-default"); // Tests were written this way
    }
    
    // @Parameters
    static public java.util.Collection<String[]> s() { return solversOnly(); }

    @Test
    public void testNNParam() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava {
                 public void m1(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(o);
                 }
                 public void m2(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(o); // ERROR
                 }
                 public void m3(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(o); // ERROR if default is NonNull
                 }
                 public void m4(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(oo);
                 }
                 public void m5(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(oo);
                 }
                 public void m6(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(oo);
                 }
                 public void m7(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(ooo);
                 }
                 public void m8(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(ooo);  // ERROR if default is Nullable
                 }
                 public void m9(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(ooo);
                 }
                 public void n1(@Nullable Object s) {}
                 public void n2(@NonNull Object s) {}
                 public void n3(Object s) {}
                 public TestJava() {}
                 }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Precondition) in method m2", 8
                ,"/tt/TestJava.java:32: verify: Associated declaration", 14
                ,"/tt/TestJava.java:8: verify: Precondition conjunct is false: _JML__tmp`7 != null", 9
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (Precondition) in method m8", 8
                ,"/tt/TestJava.java:32: verify: Associated declaration", 14
                ,"/tt/TestJava.java:26: verify: Precondition conjunct is false: _JML__tmp`47 != null", 9
//        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (NullFormal) in method m2: s in n2(@NonNull Object)",9
//        ,"/tt/TestJava.java:32: verify: Associated declaration",17
//        ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (NullFormal) in method m8: s in n2(@NonNull Object)",9
//        ,"/tt/TestJava.java:32: verify: Associated declaration",17
                );
    }

    @Test
    public void testNN2Param() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                @NullableByDefault public class TestJava {
                 public void m1(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(o);
                 }
                 public void m2(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(o); // ERROR
                 }
                 public void m3(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(o); // ERROR if default is NonNull
                 }
                 public void m4(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(oo);
                 }
                 public void m5(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(oo);
                 }
                 public void m6(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(oo);
                 }
                 public void m7(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(ooo);
                 }
                 public void m8(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(ooo);  // ERROR if default is Nullable
                 }
                 public void m9(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(ooo);
                 }
                 public void n1(@Nullable Object s) {}
                 public void n2(@NonNull Object oooo) {}
                 public void n3(Object s) {}
                 public TestJava() {}
                 }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Precondition) in method m2", 8
                ,"/tt/TestJava.java:32: verify: Associated declaration", 14
                ,"/tt/TestJava.java:8: verify: Precondition conjunct is false: _JML__tmp`7 != null", 9
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (Precondition) in method m8", 8
                ,"/tt/TestJava.java:32: verify: Associated declaration", 14
                ,"/tt/TestJava.java:26: verify: Precondition conjunct is false: _JML__tmp`47 != null", 9
//        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (NullFormal) in method m2: oooo in n2(@NonNull Object)",9
//        ,"/tt/TestJava.java:32: verify: Associated declaration",17
//        ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (NullFormal) in method m8: oooo in n2(@NonNull Object)",9
//        ,"/tt/TestJava.java:32: verify: Associated declaration",17
                );
    }

    @Test
    public void testNN3Param() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                @NonNullByDefault public class TestJava {
                 public void m1(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(o);
                 }
                 public void m2(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(o); // ERROR
                 }
                 public void m3(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(o); // ERROR if default is NonNull
                 }
                 public void m4(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(oo);
                 }
                 public void m5(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(oo);
                 }
                 public void m6(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(oo);
                 }
                 public void m7(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(ooo);
                 }
                 public void m8(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(ooo);  // ERROR if default is Nullable
                 }
                 public void m9(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(ooo);
                 }
                 public void n1(@Nullable Object s) {}
                 public void n2(@NonNull Object s) {}
                 public void n3(Object s) {}
                 public TestJava() {}
                 }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Precondition) in method m2",8
                ,"/tt/TestJava.java:32: verify: Associated declaration", 14
                ,"/tt/TestJava.java:8: verify: Precondition conjunct is false: _JML__tmp`7 != null", 9
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Precondition) in method m3", 8
                ,"/tt/TestJava.java:33: verify: Associated declaration", 14
                ,"/tt/TestJava.java:11: verify: Precondition conjunct is false: _JML__tmp`15 != null", 9
//        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (NullFormal) in method m2: s in n2(@NonNull Object)",9
//        ,"/tt/TestJava.java:32: verify: Associated declaration",17
//        ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (NullFormal) in method m3: s in n3(Object)",9
//        ,"/tt/TestJava.java:33: verify: Associated declaration",17
                );
    }
    @Test
    public void testNN4Param() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava {
                 public void m1(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(o);
                 }
                 public void m2(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(o); // ERROR
                 }
                 public void m3(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(o); // ERROR if default is NonNull
                 }
                 public void m4(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(oo);
                 }
                 public void m5(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(oo);
                 }
                 public void m6(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(oo);
                 }
                 public void m7(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(ooo);
                 }
                 public void m8(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(ooo);  // ERROR if default is Nullable
                 }
                 public void m9(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(ooo);
                 }
                 public void n1(@Nullable Object s) {}
                 public void n2(@NonNull Object s) {}
                 public void n3(Object s) {}
                 public TestJava() {}
                 }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Precondition) in method m2", 8
                ,"/tt/TestJava.java:32: verify: Associated declaration", 14
                ,"/tt/TestJava.java:8: verify: Precondition conjunct is false: _JML__tmp`7 != null", 9
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Precondition) in method m3", 8
                ,"/tt/TestJava.java:33: verify: Associated declaration", 14
                ,"/tt/TestJava.java:11: verify: Precondition conjunct is false: _JML__tmp`15 != null", 9

//        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (NullFormal) in method m2: s in n2(@NonNull Object)",9
//        ,"/tt/TestJava.java:32: verify: Associated declaration",17
//        ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (NullFormal) in method m3: s in n3(Object)",9
//        ,"/tt/TestJava.java:33: verify: Associated declaration",17
                );
    }

    @Test
    public void testNN5Param() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                @NullableByDefault public class TestJava {
                 public void m1(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(o);
                 }
                 public void m2(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(o); // ERROR
                 }
                 public void m3(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(o); // ERROR if default is NonNull
                 }
                 public void m4(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(oo);
                 }
                 public void m5(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(oo);
                 }
                 public void m6(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(oo);
                 }
                 public void m7(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(ooo);
                 }
                 public void m8(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(ooo);  // ERROR if default is Nullable
                 }
                 public void m9(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(ooo);
                 }
                 public void n1(@Nullable Object s) {}
                 public void n2(@NonNull Object s) {}
                 public void n3(Object s) {}
                 public TestJava() {}
                 }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Precondition) in method m2", 8
                ,"/tt/TestJava.java:32: verify: Associated declaration", 14
                ,"/tt/TestJava.java:8: verify: Precondition conjunct is false: _JML__tmp`7 != null", 9
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (Precondition) in method m8", 8
                ,"/tt/TestJava.java:32: verify: Associated declaration", 14
                ,"/tt/TestJava.java:26: verify: Precondition conjunct is false: _JML__tmp`47 != null", 9
//        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (NullFormal) in method m2: s in n2(@NonNull Object)",9
//        ,"/tt/TestJava.java:32: verify: Associated declaration",17
//        ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (NullFormal) in method m8: s in n2(@NonNull Object)",9
//        ,"/tt/TestJava.java:32: verify: Associated declaration",17
                );
    }

    @Test
    public void testNN6Param() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                @NonNullByDefault public class TestJava {
                 public void m1(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(o);
                 }
                 public void m2(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(o); // ERROR
                 }
                 public void m3(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(o); // ERROR if default is NonNull
                 }
                 public void m4(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(oo);
                 }
                 public void m5(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(oo);
                 }
                 public void m6(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(oo);
                 }
                 public void m7(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n1(ooo);
                 }
                 public void m8(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n2(ooo);  // ERROR if default is Nullable
                 }
                 public void m9(@Nullable Object o, @NonNull Object oo, Object ooo) {
                     n3(ooo);
                 }
                 public void n1(@Nullable Object s) {}
                 public void n2(@NonNull Object s) {}
                 public void n3(Object s) {}
                 public TestJava() {}
                 }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Precondition) in method m2", 8
                ,"/tt/TestJava.java:32: verify: Associated declaration", 14
                ,"/tt/TestJava.java:8: verify: Precondition conjunct is false: _JML__tmp`7 != null", 9
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Precondition) in method m3", 8
                ,"/tt/TestJava.java:33: verify: Associated declaration", 14
                ,"/tt/TestJava.java:11: verify: Precondition conjunct is false: _JML__tmp`15 != null", 9
//        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (NullFormal) in method m2: s in n2(@NonNull Object)",9
//        ,"/tt/TestJava.java:32: verify: Associated declaration",17
//        ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (NullFormal) in method m3: s in n3(Object)",9
//        ,"/tt/TestJava.java:33: verify: Associated declaration",17
                );
    }
    
    @Test
    public void testNNAssign() {
//        Assume.assumeTrue(runLongTests);
        // Use noInternalSpecs to help yices, which cannot handle the quantified statements in String specs
        addOptions("-no-internalSpecs");  // FIXME
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void m1() {
                    String s = null;
                  }
                  public void m1a() {
                    @NonNull String s = null;
                  }
                  public void m1b() {
                    @Nullable String s = null;
                  }
                  public void m2() {
                    String s;
                    s = null;
                  }
                  public void m2a() {
                    @NonNull String s;
                    s = null;
                  }
                  public void m2b() {
                    @Nullable String s;
                    s = null;
                  }
                  public String f; @NonNull public String ff; @Nullable public String fff;
                  public void m3() {
                    f = null;
                  }
                  public void m3a() {
                    ff = null;
                  }
                  public void m3b() {
                    fff = null;
                  }
                  public void m4(String s) {
                    s = null;
                  }
                  public void m4a(@NonNull String s) {
                    s = null;
                  }
                  public void m4b(@Nullable String s) {
                    s = null;
                  }
                  public TestJava() { f = ff = ""; }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullInitialization) in method m1a: s",21
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",7
                ,"/tt/TestJava.java:30: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m3a",8
                ,"/tt/TestJava.java:39: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m4a",7
                );
    }
    

    @Test
    public void testNNAssign2() {
//        Assume.assumeTrue(runLongTests);
        addOptions("-no-internalSpecs"); // F(XME
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                @NonNullByDefault public class TestJava {
                  public void m1() {
                    String s = null;
                  }
                  public void m1a() {
                    @NonNull String s = null;
                  }
                  public void m1b() {
                    @Nullable String s = null;
                  }
                  public void m2() {
                    String s;
                    s = null;
                  }
                  public void m2a() {
                    @NonNull String s;
                    s = null;
                  }
                  public void m2b() {
                    @Nullable String s;
                    s = null;
                  }
                  public String f; @NonNull public String ff; @Nullable public String fff;
                  public void m3() {
                    f = null;
                  }
                  public void m3a() {
                    ff = null;
                  }
                  public void m3b() {
                    fff = null;
                  }
                  public void m4(String s) {
                    s = null;
                  }
                  public void m4a(@NonNull String s) {
                    s = null;
                  }
                  public void m4b(@Nullable String s) {
                    s = null;
                  }
                  public TestJava() { f = ff = new String(); }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullInitialization) in method m1: s",12
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullInitialization) in method m1a: s",21
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2",7
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",7
                ,"/tt/TestJava.java:27: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m3",7
                ,"/tt/TestJava.java:30: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m3a",8
                ,"/tt/TestJava.java:36: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m4",7
                ,"/tt/TestJava.java:39: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m4a",7
                );
    }
    

    @Test
    public void testNNAssign3() {
//        Assume.assumeTrue(runLongTests);
        addOptions("-internalSpecs=false"); // Part of test // FIXME
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                @NullableByDefault public class TestJava {
                  public void m1() {
                    String s = null;
                  }
                  public void m1a() {
                    @NonNull String s = null;
                  }
                  public void m1b() {
                    @Nullable String s = null;
                  }
                  public void m2() {
                    String s;
                    s = null;
                  }
                  public void m2a() {
                    @NonNull String s;
                    s = null;
                  }
                  public void m2b() {
                    @Nullable String s;
                    s = null;
                  }
                  public String f; @NonNull public String ff; @Nullable public String fff;
                  public void m3() {
                    f = null;
                  }
                  public void m3a() {
                    ff = null;
                  }
                  public void m3b() {
                    fff = null;
                  }
                  public void m4(String s) {
                    s = null;
                  }
                  public void m4a(@NonNull String s) {
                    s = null;
                  }
                  public void m4b(@Nullable String s) {
                    s = null;
                  }
                  public TestJava() { f = ff = new String(); }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullInitialization) in method m1a: s",21
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",7
                ,"/tt/TestJava.java:30: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m3a",8
                ,"/tt/TestJava.java:39: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m4a",7
                );
    }

    @Test
    public void testNNAssignB() {
//        Assume.assumeTrue(runLongTests);
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava {
                  public static class A { /*@ assignable A.*; */ public A() { q = qq = new String(); r = rr = new String(); }
                      public String q; @NonNull public String qq; @Nullable public String qqq;
                      static public String r; static @NonNull public String rr; static @Nullable public String rrr;
                   }
                  public void m1() {
                    A a = new A();
                    a.q = null;
                  }
                  public void m1a() {
                    A a = new A();
                    a.qq = null;
                  }
                  public void m1b() {
                    A a = new A();
                    a.qqq = null;
                  }
                  public void m2() {
                    A.r = null;
                  }
                  public void m2a() {
                    A.rr = null;
                  }
                  public void m2b() {
                    A.rrr = null;
                  }
                }
                """
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m1a",10
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",10
                );
    }

    @Test
    public void testNNAssignB1() {
//        Assume.assumeTrue(runLongTests);
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                @NonNullByDefault public class TestJava {
                  public static class A {      /*@ assignable A.*; */ public A() { q = qq = new String(); r = rr = new String(); }
                      public String q; @NonNull public String qq; @Nullable public String qqq;
                      static public String r; static @NonNull public String rr; static @Nullable public String rrr;
                   }
                  public void m1() {
                    A a = new A();
                    a.q = null;
                  }
                  public void m1a() {
                    A a = new A();
                    a.qq = null;
                  }
                  public void m1b() {
                    A a = new A();
                    a.qqq = null;
                  }
                  public void m2() {
                    A.r = null;
                  }
                  public void m2a() {
                    A.rr = null;
                  }
                  public void m2b() {
                    A.rrr = null;
                  }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m1",9
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m1a",10
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2",9
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",10
                );
    }

    @Test
    public void testNNAssignB2() {
//        Assume.assumeTrue(runLongTests);
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                @NullableByDefault public class TestJava {
                  public static class A { /*@ assignable A.*; */ public A() { q = qq = new String(); r = rr = new String(); }
                      public String q; @NonNull public String qq; @Nullable public String qqq;
                      static public String r; static @NonNull public String rr; static @Nullable public String rrr;
                   }
                  public void m1() {
                    A a = new A();
                    a.q = null;
                  }
                  public void m1a() {
                    A a = new A();
                    a.qq = null;
                  }
                  public void m1b() {
                    A a = new A();
                    a.qqq = null;
                  }
                  public void m2() {
                    A.r = null;
                  }
                  public void m2a() {
                    A.rr = null;
                  }
                  public void m2b() {
                    A.rrr = null;
                  }
                }
                """
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m1a",10
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",10
                );
    }

    @Test
    public void testTypeCast() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void m(String s) {
                  }
                }
                """
                );
    }
    
    @Test
    public void testInvariantForOK() {
    	addOptions("-method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava extends P {
                  public void m() {
                     f = 10;
                     //@ assert \\invariant_for(this);
                     f = 1;
                  }
                }
                class P {
                  public int f;
                  //@ public invariant f >= 0;
                }
                """
                );
    }

    @Test
    public void testInvariantForVisibility() {
    	addOptions("--method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava extends P {
                  public void m() {
                     f = 10;
                     //@ assert \\invariant_for(this);
                     f = 1;
                  }
                }
                class P {
                  public int f;
                  //@ private invariant false;
                }
                """
                );
    }

    @Test
    public void testInvariantForVisibility2() {
    	addOptions("--method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava extends P {
                  public void m() {
                     f = 10;
                     //@ assert \\invariant_for(this);
                     f = 1;
                  }
                }
                class P {
                  public int f;
                  //@ public invariant true;
                }
                """
                );
    }
    
    @Test
    public void testInvariantFor() {
        addOptions("--method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava extends P {
                  public void m() {
                     f = -10;
                     //@ assert \\invariant_for(this);
                     f = 1;
                  }
                }
                class P {
                  public int f;
                  //@ public invariant f >= 0;
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m", 10
                );
    }

    @Test
    public void testInvariantForSeeStatic() {
        addOptions("--method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava extends P {
                  public void m() {
                     f = -10;
                     //@ assert \\invariant_for(this);
                     f = 1;
                  }
                }
                class P {
                  static public int f;
                  //@ static public invariant f >= 0;
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m", 10
                );
    }

    @Test
    public void testInvariantForStatic() {
        addOptions("--method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava extends P {
                  public void m() {
                     f = -10;
                     //@ assert \\invariant_for(TestJava);
                     f = 1;
                  }
                }
                class P {
                  public int f;
                  //@ public invariant f >= 0;
                }
                """
                );
    }

    @Test
    public void testInvariantForStatic1() {
    	addOptions("--method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava extends P {
                  static public int f; //@ static public invariant f >= 0;
                  public void m() {
                     f = -10;
                     //@ assert \\invariant_for(TestJava);
                     f = 1;
                  }
                }
                class P { }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test
    public void testInvariantForStatic2() {
    	addOptions("--method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava extends P {
                  static public int f; //@ static public invariant f >= 0;
                  public void m() {
                     f = -10;
                     //@ assert \\invariant_for(P);
                     f = 1;
                  }
                }
                class P { }
                """
                );
    }
    

    @Test
    public void testDZero() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void m() {
                    int q = 5;
                    int r = q/1;
                  }
                  public void ma() {
                    int q = 5;
                    int r = q%1;
                  }
                  public void m1() {
                    int z = 0; int q = 5;
                    int r = q/z;
                  }
                  public void m1a() {
                    int z = 0; int q = 5;
                    int r = q%z;
                  }
                  public void m2() {
                    int z = 0; int q = 5;
                    int r; r = q/z;
                  }
                  public void m2a() {
                    int z = 0; int q = 5;
                    int r; r = q%z;
                  }
                  public void m3() {
                    int z = 0; int q = 5;
                    q /= z;
                  }
                  public void m3a() {
                    int z = 0; int q = 5;
                    q %= z;
                  }
                }
                """
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1",14
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1a",14
                ,"/tt/TestJava.java:22: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2",17
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2a",17
                ,"/tt/TestJava.java:30: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m3",7
                ,"/tt/TestJava.java:34: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m3a",7
                );
    }

    @Test
    public void testDZero2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void m1() {
                    int q = 5;
                    int r = q/(1-1);
                  }
                  public void m2() {
                    int q = 5;
                    int r = q/0;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1",14
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2",14
                );
    }

    @Test  // Sometimes times out
    public void testInvariant1() {
        addOptions("--code-math=java","--spec-math=java","--solver-seed=42"); // Just to avoid overflow warnings; the seed attempts to avoid timeouts
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava {
                  static public int ii;
                  public int i;
                  //@ public invariant i >= 0;
                  //@ static public invariant ii >= 0;
                  //@ assignable \\everything;
                  public void m1bad() {
                    i = -i;
                  }
                  //@ assignable \\everything;
                  public void m2bad() {
                    ii = -ii;
                  }
                  //@ assignable \\everything;
                  static public void m3bad() {
                    ii = -ii;
                  }
                  //@ requires i < Integer.MAX_VALUE;
                  //@ assignable \\everything;
                  public void m1good() {
                    ++i;
                  }
                  //@ requires ii < Integer.MAX_VALUE;
                  //@ assignable \\everything;
                  public void m2good() {
                    ++ii;
                  }
                  //@ requires ii < Integer.MAX_VALUE;
                  //@ assignable \\everything;
                  static public void m3good() {
                    ++ii;
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (InvariantExit) in method m1bad",15
                ,"/tt/TestJava.java:6: verify: Associated declaration",14
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (InvariantExit) in method m2bad",15
                ,"/tt/TestJava.java:7: verify: Associated declaration",21
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (InvariantExit) in method m3bad",22
                ,"/tt/TestJava.java:7: verify: Associated declaration",21
                );
    }

    @Test
    public void testConstraint1() {
        addOptions("--code-math=java","--spec-math=java"); // Just to avoid overflow warnings
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava {
                  static public int ii;
                  public int i;
                  //@ public constraint i >= \\old(i);
                  //@ static public constraint ii >= \\old(ii);
                  //@ assignable \\everything;
                  public void m1bad() { //@ assume i > -2147483648;
                    i = -i;
                  }
                  //@ assignable \\everything;
                  public void m2bad() { //@ assume ii > -2147483648;
                    ii = -ii;
                  }
                  //@ assignable \\everything;
                  static public void m3bad() { //@ assume ii > -2147483648;
                    ii = -ii;
                  }
                  //@ requires i < Integer.MAX_VALUE;
                  //@ assignable \\everything;
                  public void m1good() {
                    ++i;
                  }
                  //@ requires ii < Integer.MAX_VALUE;
                  //@ assignable \\everything;
                  public void m2good() {
                    ++ii;
                  }
                  //@ requires ii < Integer.MAX_VALUE;
                  //@ assignable \\everything;
                  static public void m3good() {
                    ++ii;
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Constraint) in method m1bad",15
                ,"/tt/TestJava.java:6: verify: Associated declaration",14
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Constraint) in method m2bad",15
                ,"/tt/TestJava.java:7: verify: Associated declaration",21
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Constraint) in method m3bad",22
                ,"/tt/TestJava.java:7: verify: Associated declaration",21
                );
    }

    @Test
    public void testAxiom1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ axiom i == ii;
                  static int ii;
                  int i;
                  //@ assignable \\everything;
                  public void m1good() {
                    //@ assert i == ii;
                  }
                }
                """
// FIXME - use this: //@ axiom (\\forall TestJava o; o.i == o.ii);
                );
    }

    @Test
    public void testAxiom2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ axiom (\\forall TestJava o; o.i == o.ii);
                  static int ii;
                  int i;
                  //@ assignable \\nothing;
                  public void m1good() {
                    //@ assert i == ii;
                  }
                }
                """
                );
    }
    
    @Test // @Ignore // FIXME - long running or a loop?
    public void testAssignable1() { // FIXME - which of these methods here or in testAssignables2 takes so long? and why?
//        Assume.assumeTrue(runLongTests);

        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                @NonNullByDefault public class TestJava {
                  public TestJava t;
                  public int a;
                  public static int b;
                  //@ assignable this.a;
                  public void m1(TestJava o) {
                    o.a = 0;
                  }
                  //@ assignable \\nothing;
                  public void m2(TestJava o) {
                    o.a = 0;
                  }
                  //@ assignable \\everything;
                  public void m3(TestJava o) {
                    o.a = 0;
                  }
                  //@ assignable this.a;
                  public void m4(TestJava o) {
                    this.a = 0;
                  }
                  //@ assignable TestJava.b;
                  public void m4x(TestJava o) {
                    this.b = 0;
                  }
                  //@ assignable this.b;
                  public void m4y(TestJava o) {
                    TestJava.b = 0;
                  }
                  //@ assignable this.a;
                  public void m4a(TestJava o) {
                    o.a = 0;
                  }
                  //@ assignable this.a;
                  public void m4b(TestJava o) {
                    //@ assume this == o;
                    o.a = 0;
                  }
                  //@ public normal_behavior
                  //@   ensures t != null;
                  public TestJava() { t = new TestJava(); }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assignable) in method m1: o.a",9
                ,"/tt/TestJava.java:7: verify: Associated declaration",7
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assignable) in method m2: o.a",9
                ,"/tt/TestJava.java:11: verify: Associated declaration",7
                ,"/tt/TestJava.java:33: verify: The prover cannot establish an assertion (Assignable) in method m4a: o.a",9
                ,"/tt/TestJava.java:31: verify: Associated declaration",7
                );
    }

    @Test // @Ignore // FIXME - long running or a loop?
    public void testAssignable2() {
//        Assume.assumeTrue(runLongTests);

        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                @NonNullByDefault public class TestJava {
                  public TestJava t;
                  public int a;
                  public static int b;
                  //@ assignable this.a;
                  public void m5(TestJava o) {
                    a = 0;
                  }
                  //@ assignable a;
                  public void m6(TestJava o) {
                    a = 0;
                  }
                  //@ assignable \\nothing;
                  public void m7(TestJava o) {
                    a = 0;
                  }
                  //@ assignable \\nothing;
                  public void m8(TestJava o) {
                    int a; a = 0;
                  }
                  //@ assignable o.*;
                  public void m9(TestJava o) {
                    //@ assume this == o;
                    o.a = 0;
                  }
                  //@ assignable this.*;
                  public void m9b(TestJava o) {
                    o.a = 0;
                  }
                  //@ public normal_behavior
                  //@   ensures t != null;
                  public TestJava() { t = new TestJava(); }
                }
                """
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assignable) in method m7: a",7
                ,"/tt/TestJava.java:15: verify: Associated declaration",7
                ,"/tt/TestJava.java:30: verify: The prover cannot establish an assertion (Assignable) in method m9b: o.a",9
                ,"/tt/TestJava.java:28: verify: Associated declaration",7
                );
    }

    @Test
    public void testLoopWrites1() {
        helpEsc("A",
            """
            public class A {
              int i;
              //@ writes \\nothing;
              public void m1(int k) {
                int j;
                //@ loop_writes n, i, j;
                for (int n=0; n<10; n++) {
                  int m;
                  m = 9;
                  i = 1;
                }
              }
            }
            """
            ,"/A.java:6: verify: The prover cannot establish an assertion (Assignable) in method m1: `THIS.i", 24
            ,"/A.java:3: verify: Associated declaration", 7
        );
    }

    @Test
    public void testLoopWrites2() {
        expectedExit = 1;
        helpEsc("A",
            """
            public class A {
              int i;
              //@ writes \\everything;
              public void m2(int k) {
                int j;
                //@ loop_writes n;
                for (int n=0; n<10; n++) {
                  int m;
                  m = 9;
                  i = 1; // ERROR - fails but not reported since the error on j is reported before running smt
                  j = 2; // ERROR - fails before running smt
                }
              }
            }
            """
            ,"/A.java:11: error: Local variable is assigned but not present in loop frame clause: j not in //@ loop_writes n, \\count;", 7
        );
    }

    /** Tests a loop index declared in the loop initialization and an explicit loop_writes clause;
     * also checking a local variable not within the loop body */
    @Test
    public void testLoopWrites3() {
        helpEsc("A",
            """
            public class A {
              int i;
              //@ writes \\everything;
              public void m3(int k) {
                int j;
                //@ loop_writes j;
                for (int n=0; n<10; n++) { // OK
                  int m;
                  m = 9;
                  i = 1; // ERROR
                  j = 2;
                }
              }
            }
            """
            ,"/A.java:10: verify: The prover cannot establish an assertion (Assignable) in method m3: i", 9
            ,"/A.java:6: verify: Associated declaration", 9
        );
    }

    /** Tests a loop index not declared in the loop initialization and an explicit loop_writes clause */
    @Test
    public void testLoopWrites6() {
        expectedExit = 1;
        helpEsc("A",
            """
            public class A {
              int i;
              //@ writes \\everything;
              public void m6(int k) {
                int n, j;
                //@ loop_writes j;
                for (n=0; n<10; n++) { // ERROR
                  int m;
                  m = 9;
                  j = 1;
                }
              }
            }
            """
            ,"/A.java:7: error: Local variable is assigned but not present in loop frame clause: n not in //@ loop_writes j, \\count;", 21
        );
    }

    /** Tests that a loop variable not declared in the loop initialization is in the default loop_writes clause */
    @Test
    public void testLoopWrites4() {
        helpEsc("A",
            """
            public class A {
              int i;
              //@ writes \\everything;
              public void m4(int k) {
                int n;
                for (n=0; n<10; n++) { // OK
                }
              }
            }
            """
        );
    }

    /** Tests that the declared loop variable is automatically in the default loop_writes clause */
    @Test
    public void testLoopWrites5() {
        helpEsc("A",
            """
            public class A {
              int i;
              //@ writes \\everything;
              public void m5(int k) {
                for (int n=0; n<10; n++) { // OK
                }
              }
            }
            """
        );
    }

    /** Tests that multiple local to the loop variables are OK */
    @Test
    public void testLoopWrites7() {
        helpEsc("A",
            """
            public class A {
              int i;
              //@ writes \\everything;
              public void m7() {
                for (int n=0; n<10; n++) {
                  int j,k;
                  j = k = 1;
                }
              }
            }
            """
        );
    }

    @Test
    public void testPureMethod1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                 public class TestJava {
                  public TestJava t;
                  public int a;
                  public static int b;
                  //@ public normal_behavior
                  //@   requires b;
                  //@   ensures \\result == 5;
                  //@ also public normal_behavior
                  //@   requires !b;
                  //@   ensures \\result == 7;
                  @Pure public int m(boolean b) {
                    return b ? 5 : 7;
                  }
                  public void m1() {
                    //@ assert m(true) == 5;
                  }
                  public void m2() {
                    //@ assert m(false) == 7;
                  }
                  public void m1a(boolean bb) {
                    //@ assert m(bb) == 6;
                  }
                }
                """
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Assert) in method m1a",9
                );
    }

    @Test
    public void testPureMethod2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                 public class TestJava {
                  public TestJava t;
                  public int a;
                  public static int b;
                  //@ public normal_behavior
                  //@   requires b;
                  //@   ensures \\result == 5;
                  @Pure public int m(boolean b) {
                    return b ? 5 : 7;
                  }
                  public void m1() {
                    //@ assert m(true) == 5;
                  }
                  public void m2() {
                    //@ assert m(false) == 5;
                  }
                  public void m1a(boolean bb) {
                    //@ assert m(bb) == 5;
                  }
                  public void m1b() {
                    //@ assert m(true) == 7;
                  }
                }
                """
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m2",17
                ,"/tt/TestJava.java:10: verify: Associated declaration",20
                ,optional("/tt/TestJava.java:9: verify: Precondition conjunct is false: b",18)
                ,"/tt/TestJava.java:20: verify: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m1a",17
                ,"/tt/TestJava.java:10: verify: Associated declaration",20
                ,optional("/tt/TestJava.java:9: verify: Precondition conjunct is false: b",18)
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Assert) in method m1b",9
                 );
    }
   
    @Test
    public void testKeysOK() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1() {
                    //@ assert \\key(OPENJML);
                  }
                  public void m2() {
                    //@ assert !\\key(ZZZ,OPENJML);
                  }
                  public void m3() {
                    //@ assert !\\key(OPENJML,YYY);
                  }
                  public void m4() {
                    //@ assert !\\key(ZZZ,YYY);
                  }
                  public void q1() {
                    //@ assert \\key("OPENJML");
                  }
                  public void q2() {
                    //@ assert !\\key("ZZZ","OPENJML");
                  }
                  public void q3() {
                    //@ assert !\\key("OPENJML","YYY");
                  }
                  public void q4() {
                    //@ assert !\\key("ZZZ","YYY");
                  }
                }
                """
                );
    }

    @Test
    public void testKeysBad() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1() {
                    //@ assert \\key(0);
                  }
                }
                """
                ,"/tt/TestJava.java:4: error: An argument to \\key must be an identifier or a string literal: 0", 21
                );
    }
}
