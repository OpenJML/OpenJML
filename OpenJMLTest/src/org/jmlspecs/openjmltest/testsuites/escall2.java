package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
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
        helpEsc("tt.TestJava","package tt; \n"
        +" import org.jmlspecs.annotation.*; \n"
        +"public class TestJava { \n"
        +" public void m1(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(o); \n"
        +" } \n"
        +" public void m2(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(o); // ERROR \n"
        +" } \n"
        +" public void m3(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(o); // ERROR if default is NonNull \n"
        +" } \n"
        +" public void m4(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(oo); \n"
        +" } \n"
        +" public void m5(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(oo); \n"
        +" } \n"
        +" public void m6(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(oo); \n"
        +" } \n"
        +" public void m7(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(ooo); \n"
        +" } \n"
        +" public void m8(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(ooo);  // ERROR if default is Nullable \n"
        +" } \n"
        +" public void m9(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(ooo); \n"
        +" } \n"
        +" public void n1(@Nullable Object s) {} \n"
        +" public void n2(@NonNull Object s) {} \n"
        +" public void n3(Object s) {} \n"
        +" public TestJava() {}\n"
        +" } \n"
        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (NullFormal) in method m2: s in n2(@NonNull Object)",9
        ,"/tt/TestJava.java:32: verify: Associated declaration",17
        ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (NullFormal) in method m8: s in n2(@NonNull Object)",9
        ,"/tt/TestJava.java:32: verify: Associated declaration",17
        );
    }

    @Test
    public void testNN2Param() {
        addOptions("--method=m2","--show");
        helpEsc("tt.TestJava","package tt; \n"
        +" import org.jmlspecs.annotation.*; \n"
        +"@NullableByDefault public class TestJava { \n"
        +" public void m1(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(o); \n"
        +" } \n"
        +" public void m2(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(o); // ERROR \n"
        +" } \n"
        +" public void m3(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(o); // ERROR if default is NonNull \n"
        +" } \n"
        +" public void m4(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(oo); \n"
        +" } \n"
        +" public void m5(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(oo); \n"
        +" } \n"
        +" public void m6(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(oo); \n"
        +" } \n"
        +" public void m7(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(ooo); \n"
        +" } \n"
        +" public void m8(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(ooo);  // ERROR if default is Nullable \n"
        +" } \n"
        +" public void m9(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(ooo); \n"
        +" } \n"
        +" public void n1(@Nullable Object s) {} \n"
        +" public void n2(@NonNull Object oooo) {} \n"
        +" public void n3(Object s) {} \n"
        +" public TestJava() {}\n"
        +" } \n"
        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (NullFormal) in method m2: oooo in n2(@NonNull Object)",9
        ,"/tt/TestJava.java:32: verify: Associated declaration",17
        ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (NullFormal) in method m8: oooo in n2(@NonNull Object)",9
        ,"/tt/TestJava.java:32: verify: Associated declaration",17
        );
    }

    @Test
    public void testNN3Param() {
        helpEsc("tt.TestJava","package tt; \n"
        +" import org.jmlspecs.annotation.*; \n"
        +"@NonNullByDefault public class TestJava { \n"
        +" public void m1(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(o); \n"
        +" } \n"
        +" public void m2(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(o); // ERROR \n"
        +" } \n"
        +" public void m3(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(o); // ERROR if default is NonNull \n"
        +" } \n"
        +" public void m4(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(oo); \n"
        +" } \n"
        +" public void m5(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(oo); \n"
        +" } \n"
        +" public void m6(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(oo); \n"
        +" } \n"
        +" public void m7(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(ooo); \n"
        +" } \n"
        +" public void m8(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(ooo);  // ERROR if default is Nullable \n"
        +" } \n"
        +" public void m9(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(ooo); \n"
        +" } \n"
        +" public void n1(@Nullable Object s) {} \n"
        +" public void n2(@NonNull Object s) {} \n" // Line 32
        +" public void n3(Object s) {} \n"    // Line 33
        +" public TestJava() {}\n"
        +" } \n"
        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (NullFormal) in method m2: s in n2(@NonNull Object)",9
        ,"/tt/TestJava.java:32: verify: Associated declaration",17
        ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (NullFormal) in method m3: s in n3(Object)",9
        ,"/tt/TestJava.java:33: verify: Associated declaration",17
        );
    }
    @Test
    public void testNN4Param() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava","package tt; \n"
        +" import org.jmlspecs.annotation.*; \n"
        +"public class TestJava { \n"
        +" public void m1(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(o); \n"
        +" } \n"
        +" public void m2(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(o); // ERROR \n"
        +" } \n"
        +" public void m3(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(o); // ERROR if default is NonNull \n"
        +" } \n"
        +" public void m4(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(oo); \n"
        +" } \n"
        +" public void m5(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(oo); \n"
        +" } \n"
        +" public void m6(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(oo); \n"
        +" } \n"
        +" public void m7(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(ooo); \n"
        +" } \n"
        +" public void m8(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(ooo);  // ERROR if default is Nullable \n"
        +" } \n"
        +" public void m9(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(ooo); \n"
        +" } \n"
        +" public void n1(@Nullable Object s) {} \n"
        +" public void n2(@NonNull Object s) {} \n"
        +" public void n3(Object s) {} \n"
        +" public TestJava() {}\n"
        +" } \n"
        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (NullFormal) in method m2: s in n2(@NonNull Object)",9
        ,"/tt/TestJava.java:32: verify: Associated declaration",17
        ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (NullFormal) in method m3: s in n3(Object)",9
        ,"/tt/TestJava.java:33: verify: Associated declaration",17
        );
    }

    @Test
    public void testNN5Param() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava","package tt; \n"
        +" import org.jmlspecs.annotation.*; \n"
        +"@NullableByDefault public class TestJava { \n"
        +" public void m1(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(o); \n"
        +" } \n"
        +" public void m2(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(o); // ERROR \n"
        +" } \n"
        +" public void m3(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(o); // ERROR if default is NonNull \n"
        +" } \n"
        +" public void m4(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(oo); \n"
        +" } \n"
        +" public void m5(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(oo); \n"
        +" } \n"
        +" public void m6(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(oo); \n"
        +" } \n"
        +" public void m7(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(ooo); \n"
        +" } \n"
        +" public void m8(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(ooo);  // ERROR if default is Nullable \n"
        +" } \n"
        +" public void m9(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(ooo); \n"
        +" } \n"
        +" public void n1(@Nullable Object s) {} \n"
        +" public void n2(@NonNull Object s) {} \n"
        +" public void n3(Object s) {} \n"
        +" public TestJava() {}\n"
        +" } \n"
        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (NullFormal) in method m2: s in n2(@NonNull Object)",9
        ,"/tt/TestJava.java:32: verify: Associated declaration",17
        ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (NullFormal) in method m8: s in n2(@NonNull Object)",9
        ,"/tt/TestJava.java:32: verify: Associated declaration",17
        );
    }

    @Test
    public void testNN6Param() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava","package tt; \n"
        +" import org.jmlspecs.annotation.*; \n"
        +"@NonNullByDefault public class TestJava { \n"
        +" public void m1(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(o); \n"
        +" } \n"
        +" public void m2(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(o); // ERROR \n"
        +" } \n"
        +" public void m3(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(o); // ERROR if default is NonNull \n"
        +" } \n"
        +" public void m4(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(oo); \n"
        +" } \n"
        +" public void m5(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(oo); \n"
        +" } \n"
        +" public void m6(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(oo); \n"
        +" } \n"
        +" public void m7(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n1(ooo); \n"
        +" } \n"
        +" public void m8(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n2(ooo);  // ERROR if default is Nullable \n"
        +" } \n"
        +" public void m9(@Nullable Object o, @NonNull Object oo, Object ooo) { \n"
        +"     n3(ooo); \n"
        +" } \n"
        +" public void n1(@Nullable Object s) {} \n"
        +" public void n2(@NonNull Object s) {} \n" // Line 32
        +" public void n3(Object s) {} \n"    // Line 33
        +" public TestJava() {}\n"
        +" } \n"
        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (NullFormal) in method m2: s in n2(@NonNull Object)",9
        ,"/tt/TestJava.java:32: verify: Associated declaration",17
        ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (NullFormal) in method m3: s in n3(Object)",9
        ,"/tt/TestJava.java:33: verify: Associated declaration",17
        );
    }
    
    @Test
    public void testNNAssign() {
//        Assume.assumeTrue(runLongTests);
        // Use noInternalSpecs to help yices, which cannot handle the quantified statements in String specs
        addOptions("-no-internalSpecs");  // FIXME
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  public void m1() {\n"
                +"    String s = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m1a() {\n"
                +"    @NonNull String s = null;\n" // ERROR
                +"  }\n"
                
                +"  public void m1b() {\n"
                +"    @Nullable String s = null;\n"
                +"  }\n"
                
                +"  public void m2() {\n"
                +"    String s;\n"
                +"    s = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m2a() {\n"
                +"    @NonNull String s;\n"
                +"    s = null;\n"  // ERROR
                +"  }\n"
                
                +"  public void m2b() {\n"
                +"    @Nullable String s;\n"
                +"    s = null;\n"
                +"  }\n"
                
                +"  public String f; @NonNull public String ff; @Nullable public String fff; \n"
                
                +"  public void m3() {\n"
                +"    f = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m3a() {\n"
                +"    ff = null;\n" // ERROR
                +"  }\n"
                
                +"  public void m3b() {\n"
                +"    fff = null;\n" 
                +"  }\n"
                
                +"  public void m4(String s) {\n"
                +"    s = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m4a(@NonNull String s) {\n"
                +"    s = null;\n"  // ERROR
                +"  }\n"
                
                +"  public void m4b(@Nullable String s) {\n"
                +"    s = null;\n"
                +"  }\n"
                
                +"  public TestJava() { f = ff = \"\"; }\n"
                +"}"
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
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public void m1() {\n"
                +"    String s = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m1a() {\n"
                +"    @NonNull String s = null;\n" // ERROR
                +"  }\n"
                
                +"  public void m1b() {\n"
                +"    @Nullable String s = null;\n"
                +"  }\n"
                
                +"  public void m2() {\n"
                +"    String s;\n"
                +"    s = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m2a() {\n"
                +"    @NonNull String s;\n"
                +"    s = null;\n"  // ERROR
                +"  }\n"
                
                +"  public void m2b() {\n"
                +"    @Nullable String s;\n"
                +"    s = null;\n"
                +"  }\n"
                
                +"  public String f; @NonNull public String ff; @Nullable public String fff; \n"
                
                +"  public void m3() {\n"
                +"    f = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m3a() {\n"
                +"    ff = null;\n" // ERROR
                +"  }\n"
                
                +"  public void m3b() {\n"
                +"    fff = null;\n" 
                +"  }\n"
                
                +"  public void m4(String s) {\n"
                +"    s = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m4a(@NonNull String s) {\n"
                +"    s = null;\n"  // ERROR
                +"  }\n"
                
                +"  public void m4b(@Nullable String s) {\n"
                +"    s = null;\n"
                +"  }\n"
                
                +"  public TestJava() { f = ff = new String(); }\n"
                +"}"
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
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NullableByDefault public class TestJava { \n"
                
                +"  public void m1() {\n"
                +"    String s = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m1a() {\n"
                +"    @NonNull String s = null;\n" // ERROR
                +"  }\n"
                
                +"  public void m1b() {\n"
                +"    @Nullable String s = null;\n"
                +"  }\n"
                
                +"  public void m2() {\n"
                +"    String s;\n"
                +"    s = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m2a() {\n"
                +"    @NonNull String s;\n"
                +"    s = null;\n"  // ERROR
                +"  }\n"
                
                +"  public void m2b() {\n"
                +"    @Nullable String s;\n"
                +"    s = null;\n"
                +"  }\n"
                
                +"  public String f; @NonNull public String ff; @Nullable public String fff; \n"
                
                +"  public void m3() {\n"
                +"    f = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m3a() {\n"
                +"    ff = null;\n" // ERROR
                +"  }\n"
                
                +"  public void m3b() {\n"
                +"    fff = null;\n" 
                +"  }\n"
                
                +"  public void m4(String s) {\n"
                +"    s = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m4a(@NonNull String s) {\n"
                +"    s = null;\n"  // ERROR
                +"  }\n"
                
                +"  public void m4b(@Nullable String s) {\n"
                +"    s = null;\n"
                +"  }\n"
                
                +"  public TestJava() { f = ff = new String(); }\n"
                +"}"
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullInitialization) in method m1a: s",21
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",7
                ,"/tt/TestJava.java:30: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m3a",8
                ,"/tt/TestJava.java:39: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m4a",7
                );
    }
    
    @Test
    public void testNNAssignB() {
//        Assume.assumeTrue(runLongTests);
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  public static class A { /*@ assignable A.*; */ public A() { q = qq = new String(); r = rr = new String(); }\n" 
                +"      public String q; @NonNull public String qq; @Nullable public String qqq; \n"
                +"      static public String r; static @NonNull public String rr; static @Nullable public String rrr; \n"
                +"   }\n"
                
                +"  public void m1() {\n"
                +"    A a = new A();\n"
                +"    a.q = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m1a() {\n"
                +"    A a = new A();\n"
                +"    a.qq = null;\n" // ERROR
                +"  }\n"
                
                +"  public void m1b() {\n"
                +"    A a = new A();\n"
                +"    a.qqq = null;\n" 
                +"  }\n"
                
                +"  public void m2() {\n"
                +"    A.r = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m2a() {\n"
                +"    A.rr = null;\n" // ERROR 
                +"  }\n"
                
                +"  public void m2b() {\n"
                +"    A.rrr = null;\n" 
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m1a",10
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",10
                );
    }
        
    @Test
    public void testNNAssignB1() {
//        Assume.assumeTrue(runLongTests);
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public static class A {" // Tests whether this gets the enclosing class's annotation; global option is nullable
                +"      /*@ assignable A.*; */ public A() { q = qq = new String(); r = rr = new String(); }\n"
                +"      public String q; @NonNull public String qq; @Nullable public String qqq; \n"
                +"      static public String r; static @NonNull public String rr; static @Nullable public String rrr; \n"
                +"   }\n"
                
                +"  public void m1() {\n"
                +"    A a = new A();\n"
                +"    a.q = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m1a() {\n"
                +"    A a = new A();\n"
                +"    a.qq = null;\n" // ERROR
                +"  }\n"
                
                +"  public void m1b() {\n"
                +"    A a = new A();\n"
                +"    a.qqq = null;\n" 
                +"  }\n"
                
                +"  public void m2() {\n"
                +"    A.r = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m2a() {\n"
                +"    A.rr = null;\n" // ERROR 
                +"  }\n"
                
                +"  public void m2b() {\n"
                +"    A.rrr = null;\n" 
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m1",9
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m1a",10
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2",9
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",10
                );
    }
    
    @Test
    public void testNNAssignB2() {
//        Assume.assumeTrue(runLongTests);
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NullableByDefault public class TestJava { \n"
                
                +"  public static class A { /*@ assignable A.*; */ public A() { q = qq = new String(); r = rr = new String(); }\n" 
                +"      public String q; @NonNull public String qq; @Nullable public String qqq; \n"
                +"      static public String r; static @NonNull public String rr; static @Nullable public String rrr; \n"
                +"   }\n"
                
                +"  public void m1() {\n"
                +"    A a = new A();\n"
                +"    a.q = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m1a() {\n"
                +"    A a = new A();\n"
                +"    a.qq = null;\n" // ERROR
                +"  }\n"
                
                +"  public void m1b() {\n"
                +"    A a = new A();\n"
                +"    a.qqq = null;\n" 
                +"  }\n"
                
                +"  public void m2() {\n"
                +"    A.r = null;\n" // ERROR if default is nonnull
                +"  }\n"
                
                +"  public void m2a() {\n"
                +"    A.rr = null;\n" // ERROR 
                +"  }\n"
                
                +"  public void m2b() {\n"
                +"    A.rrr = null;\n" 
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m1a",10
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",10
                );
    }
    
    @Test
    public void testTypeCast() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  public void m(String s) {\n"
                +"  }\n"
                
                +"}"
                );
    }
    
    @Test
    public void testInvariantForOK() {
    	addOptions("-method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava extends P { \n"
                
                +"  public void m() {\n"
                +"     f = 10; \n"
                +"     //@ assert \\invariant_for(this);\n" // OK - invariant is true
                +"     f = 1; \n"
                +"  }\n"
                
                +"} class P { public int f; //@ public invariant f >= 0; \n"
                +"}\n"
                );
    }
    
    @Test
    public void testInvariantForVisibility() {
    	addOptions("--method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava extends P { \n"
                
                +"  public void m() {\n"
                +"     f = 10; \n"
                +"     //@ assert \\invariant_for(this);\n" // OK - does not see invariant
                +"     f = 1; \n"
                +"  }\n"
                
                +"} class P { public int f; //@ private invariant false; \n"
                +"}\n"
                );
    }
    
    @Test
    public void testInvariantForVisibility2() {
    	addOptions("--method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava extends P { \n"
                
                +"  public void m() {\n"
                +"     f = 10; \n"
                +"     //@ assert \\invariant_for(this);\n" // OK - sees invariant
                +"     f = 1; \n"
                +"  }\n"
                
                +"} class P { public int f; //@ public invariant true; \n"
                +"}\n"
                );
    }
    
    @Test
    public void testInvariantFor() {
        addOptions("--method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava extends P { \n"
                
                +"  public void m() {\n"
                +"     f = -10; \n"
                +"     //@ assert \\invariant_for(this);\n" // ERROR - should see inherited invariant and fail
                +"     f = 1; \n"
                +"  }\n"
                
                +"} class P { public int f; //@ public invariant f >= 0; \n"
                +"}\n"
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m", 10
                );
    }
    
    @Test
    public void testInvariantForSeeStatic() {
        addOptions("--method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava extends P { \n"
                
                +"  public void m() {\n"
                +"     f = -10; \n"
                +"     //@ assert \\invariant_for(this);\n" // ERROR - should see static invariant
                +"     f = 1; \n"
                +"  }\n"
                
                +"} class P { static public int f; //@ static public invariant f >= 0; \n"
                +"}\n"
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m", 10
                );
    }
    
    @Test
    public void testInvariantForStatic() {
        addOptions("--method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava extends P { \n"
                
                +"  public void m() {\n"
                +"     f = -10; \n"
                +"     //@ assert \\invariant_for(TestJava);\n" // OK - sees only static invariants
                +"     f = 1; \n"
                +"  }\n"
                
                +"} class P { public int f; //@ public invariant f >= 0; \n"
                +"}\n"
                );
    }

    @Test
    public void testInvariantForStatic1() {
    	addOptions("--method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava extends P { \n"
                +"  static public int f; //@ static public invariant f >= 0; \n"
                
                +"  public void m() {\n"
                +"     f = -10; \n"
                +"     //@ assert \\invariant_for(TestJava);\n" // ERROR - should see static invariant
                +"     f = 1; \n"
                +"  }\n"
                
                +"} class P { }\n "
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m",10
                );
    }
    
    @Test
    public void testInvariantForStatic2() {
    	addOptions("--method=m"); // Part of test - don't test constructor
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava extends P { \n"
                +"  static public int f; //@ static public invariant f >= 0; \n"
                
                +"  public void m() {\n"
                +"     f = -10; \n"
                +"     //@ assert \\invariant_for(P);\n" // OK
                +"     f = 1; \n"
                +"  }\n"
                
                +"} class P { }\n "
                );
    }
    

    @Test
    public void testDZero() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  public void m() {\n"
                +"    int q = 5;\n"
                +"    int r = q/1;\n"
                +"  }\n"
                
                +"  public void ma() {\n"
                +"    int q = 5;\n"
                +"    int r = q%1;\n"
                +"  }\n"
                
                +"  public void m1() {\n"
                +"    int z = 0; int q = 5;\n"
                +"    int r = q/z;\n" // ERROR
                +"  }\n"
                
                +"  public void m1a() {\n"
                +"    int z = 0; int q = 5;\n"
                +"    int r = q%z;\n" // ERROR
                +"  }\n"
                
                +"  public void m2() {\n"
                +"    int z = 0; int q = 5;\n"
                +"    int r; r = q/z;\n" // ERROR
                +"  }\n"
                
                +"  public void m2a() {\n"
                +"    int z = 0; int q = 5;\n"
                +"    int r; r = q%z;\n" // ERROR
                +"  }\n"

                +"  public void m3() {\n"
                +"    int z = 0; int q = 5;\n"
                +"    q /= z;\n" // ERROR
                +"  }\n"
                
                +"  public void m3a() {\n"
                +"    int z = 0; int q = 5;\n"
                +"    q %= z;\n" // ERROR
                +"  }\n"
                
                +"}"
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
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  public void m1() {\n"
                +"    int q = 5;\n"
                +"    int r = q/(1-1);\n" // ERROR
                +"  }\n"
                
                +"  public void m2() {\n"
                +"    int q = 5;\n"
                +"    int r = q/0;\n" // ERROR
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1",14
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2",14
                );
    }

    @Test  // Sometimes times out
    public void testInvariant1() {
        addOptions("--code-math=java","--spec-math=java","--solver-seed=42"); // Just to avoid overflow warnings; the seed attempts to avoid timeouts
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  static public int ii;\n"
                +"  public int i;\n"
                
                +"  //@ public invariant i >= 0;\n"
                +"  //@ static public invariant ii >= 0;\n"
                
                +"  //@ assignable \\everything; \n"
                +"  public void m1bad() {\n"
                +"    i = -i;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything; \n"
                +"  public void m2bad() {\n"
                +"    ii = -ii;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything; \n"
                +"  static public void m3bad() {\n"
                +"    ii = -ii;\n"
                +"  }\n"
                
                +"  //@ requires i < Integer.MAX_VALUE;\n"
                +"  //@ assignable \\everything; \n"
                +"  public void m1good() {\n"
                +"    ++i;\n"
                +"  }\n"
                
                +"  //@ requires ii < Integer.MAX_VALUE;\n"
                +"  //@ assignable \\everything; \n"
                +"  public void m2good() {\n"
                +"    ++ii;\n"
                +"  }\n"
                
                +"  //@ requires ii < Integer.MAX_VALUE;\n"
                +"  //@ assignable \\everything; \n"
                +"  static public void m3good() {\n"
                +"    ++ii;\n"
                +"  }\n"
                
                
                +"}"
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
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava {\n"
                
                +"  static public int ii;\n"
                +"  public int i;\n"
                
                +"  //@ public constraint i >= \\old(i);\n"
                +"  //@ static public constraint ii >= \\old(ii);\n"
                
                +"  //@ assignable \\everything; \n"
                +"  public void m1bad() { //@ assume i > -2147483648;\n"
                +"    i = -i;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything; \n"
                +"  public void m2bad() { //@ assume ii > -2147483648;\n"
                +"    ii = -ii;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything; \n"
                +"  static public void m3bad() { //@ assume ii > -2147483648;\n"
                +"    ii = -ii;\n"
                +"  }\n"
                
                +"  //@ requires i < Integer.MAX_VALUE;\n"
                +"  //@ assignable \\everything; \n"
                +"  public void m1good() {\n"
                +"    ++i;\n"
                +"  }\n"
                
                +"  //@ requires ii < Integer.MAX_VALUE;\n"
                +"  //@ assignable \\everything; \n"
                +"  public void m2good() {\n"
                +"    ++ii;\n"
                +"  }\n"
                
                +"  //@ requires ii < Integer.MAX_VALUE;\n"
                +"  //@ assignable \\everything; \n"
                +"  static public void m3good() {\n"
                +"    ++ii;\n"
                +"  }\n"
                
                
                +"}"
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
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
// FIXME - use this               // +"  //@ axiom (\\forall TestJava o; o.i == o.ii);\n"
                +"  //@ axiom i == ii;\n"
                +"  static int ii;\n"
                +"  int i;\n"
                
               
                +"  //@ assignable \\everything; \n"
                +"  public void m1good() {\n"
                +"    //@ assert i == ii;\n"
                +"  }\n"
                
                +"}"
                );
    }
    
    @Test
    public void testAxiom2() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  //@ axiom (\\forall TestJava o; o.i == o.ii);\n"
                +"  static int ii;\n"
                +"  int i;\n"
                
               
                +"  //@ assignable \\nothing; \n"
                +"  public void m1good() {\n"
                +"    //@ assert i == ii;\n"
                +"  }\n"
                
                +"}"
                );
    }
    
    @Test // @Ignore // FIXME - long running or a loop?
    public void testAssignable1() { // FIXME - which of these methods here or in testAssignables2 takes so long? and why?
//        Assume.assumeTrue(runLongTests);

        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  //@ assignable this.a;\n"
                +"  public void m1(TestJava o) {\n"
                +"    o.a = 0;\n"  // BAD
                +"  }\n" // Line 10
                
                +"  //@ assignable \\nothing;\n"
                +"  public void m2(TestJava o) {\n"
                +"    o.a = 0;\n"  // BAD
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  public void m3(TestJava o) {\n"
                +"    o.a = 0;\n"  // OK
                +"  }\n"
                
                +"  //@ assignable this.a;\n"
                +"  public void m4(TestJava o) {\n"
                +"    this.a = 0;\n"  // OK
                +"  }\n"
                
                +"  //@ assignable TestJava.b;\n"
                +"  public void m4x(TestJava o) {\n"
                +"    this.b = 0;\n"  // OK
                +"  }\n"
                
                +"  //@ assignable this.b;\n"
                +"  public void m4y(TestJava o) {\n"
                +"    TestJava.b = 0;\n"  // OK
                +"  }\n" // Line 30
                
                +"  //@ assignable this.a;\n"
                +"  public void m4a(TestJava o) {\n"
                +"    o.a = 0;\n"  // BAD
                +"  }\n"
                
                +"  //@ assignable this.a;\n"
                +"  public void m4b(TestJava o) {\n"
                +"    //@ assume this == o; \n"
                +"    o.a = 0;\n"  // OK
                +"  }\n"
                
                +"  //@ public normal_behavior ensures t != null;\n"
                +"  public TestJava() { t = new TestJava(); }\n"
                +"}"
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

        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                
                +"  //@ assignable this.a;\n" // Line 7
                +"  public void m5(TestJava o) {\n"
                +"    a = 0;\n"  // OK
                +"  }\n"
                
                +"  //@ assignable a;\n"
                +"  public void m6(TestJava o) {\n"
                +"    a = 0;\n"  // OK
                +"  }\n"
                
                +"  //@ assignable \\nothing;\n"
                +"  public void m7(TestJava o) {\n"
                +"    a = 0;\n"  // BAD // Line 17
                +"  }\n"
                
                +"  //@ assignable \\nothing;\n"
                +"  public void m8(TestJava o) {\n"
                +"    int a; a = 0;\n"  // OK
                +"  }\n"
                
                +"  //@ assignable o.*;\n"
                +"  public void m9(TestJava o) {\n"
                +"    //@ assume this == o; \n"
                +"    o.a = 0;\n"  // OK
                +"  }\n"
                
                +"  //@ assignable this.*;\n"
                +"  public void m9b(TestJava o) {\n"
                +"    o.a = 0;\n"  // BAD
                +"  }\n"
                +"  //@ public normal_behavior ensures t != null;\n"
                +"  public TestJava() { t = new TestJava(); }\n"
                +"}"
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
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +" public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  //@ public normal_behavior requires b; ensures \\result == 5; \n"
                +"  //@ also public normal_behavior requires !b; ensures \\result == 7; \n"
                +"  @Pure public int m(boolean b) {\n"
                +"    return b ? 5 : 7;\n"
                +"  }\n"
                
                +"  public void m1() {\n"
                +"    //@ assert m(true) == 5; \n"
                +"  }\n"
                
                +"  public void m2() {\n"
                +"    //@ assert m(false) == 7; \n"
                +"  }\n"
                
                +"  public void m1a(boolean bb) {\n"
                +"    //@ assert m(bb) == 6; \n"
                +"  }\n"
                
                
                +"}" 
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (Assert) in method m1a",9
                );
    }
   
    @Test
    public void testPureMethod2() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +" public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  //@ public normal_behavior requires b; ensures \\result == 5; \n"
                +"  @Pure public int m(boolean b) {\n"
                +"    return b ? 5 : 7;\n"
                +"  }\n"
                
                +"  public void m1() {\n"
                +"    //@ assert m(true) == 5; \n"
                +"  }\n"
                
                +"  public void m2() {\n"
                +"    //@ assert m(false) == 5; \n"
                +"  }\n"
                
                +"  public void m1a(boolean bb) {\n"
                +"    //@ assert m(bb) == 5; \n"
                +"  }\n"
                
                +"  public void m1b() {\n"
                +"    //@ assert m(true) == 7; \n"
                +"  }\n"
        
        
                +"}"
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m2",17
                ,"/tt/TestJava.java:8: verify: Associated declaration",20
                ,optional("/tt/TestJava.java:7: verify: Precondition conjunct is false: b",39)
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m1a",17
                ,"/tt/TestJava.java:8: verify: Associated declaration",20
                ,optional("/tt/TestJava.java:7: verify: Precondition conjunct is false: b",39)
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Assert) in method m1b",9
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
