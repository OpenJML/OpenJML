package tests;


public class esc2 extends EscBase {

    protected void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        options.put("-noPurityCheck","");
        options.put("-nullableByDefault",""); // Because the tests were written this way
//        options.put("-jmlverbose",   "");
//        options.put("-showbb","");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //options.put("-trace",   "");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
    }
    
    public void testNNParam() {
        helpTCX("tt.TestJava","package tt; \n"
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
        ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Precondition) in method m2",8
        ,"/tt/TestJava.java:32: warning: Associated declaration",17
        ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Precondition) in method m8",8
        ,"/tt/TestJava.java:32: warning: Associated declaration",17
        );
    }

    public void testNN2Param() {
        helpTCX("tt.TestJava","package tt; \n"
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
        ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Precondition) in method m2",8
        ,"/tt/TestJava.java:32: warning: Associated declaration",17
        ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Precondition) in method m8",8
        ,"/tt/TestJava.java:32: warning: Associated declaration",17
        );
    }

    public void testNN3Param() {
        helpTCX("tt.TestJava","package tt; \n"
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
        ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Precondition) in method m2",8
        ,"/tt/TestJava.java:32: warning: Associated declaration",17
        ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Precondition) in method m3",8
        ,"/tt/TestJava.java:33: warning: Associated declaration",24
        );
    }
    public void testNN4Param() {
        options.put("-nullableByDefault",null);
        options.put("-nonnullByDefault","");
        helpTCX("tt.TestJava","package tt; \n"
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
        ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Precondition) in method m2",8
        ,"/tt/TestJava.java:32: warning: Associated declaration",17
        ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Precondition) in method m3",8
        ,"/tt/TestJava.java:33: warning: Associated declaration",24
        );
    }

    public void testNN5Param() {
        options.put("-nullableByDefault",null);
        options.put("-nonnullByDefault","");
        helpTCX("tt.TestJava","package tt; \n"
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
        ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Precondition) in method m2",8
        ,"/tt/TestJava.java:32: warning: Associated declaration",17
        ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Precondition) in method m8",8
        ,"/tt/TestJava.java:32: warning: Associated declaration",17
        );
    }

    public void testNN6Param() {
        options.put("-nullableByDefault",null);
        options.put("-nonnullByDefault","");
        helpTCX("tt.TestJava","package tt; \n"
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
        ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Precondition) in method m2",8
        ,"/tt/TestJava.java:32: warning: Associated declaration",17
        ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Precondition) in method m3",8
        ,"/tt/TestJava.java:33: warning: Associated declaration",24
        );
    }

    public void testNNAssign() {
        helpTCX("tt.TestJava","package tt; \n"
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
                
                +"  String f; @NonNull String ff; @Nullable String fff; \n"
                
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
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNullInitialization) in method m1a",21
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",7
                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m3a",8
                ,"/tt/TestJava.java:39: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m4a",7
                );
    }
    

    public void testNNAssign2() {
        helpTCX("tt.TestJava","package tt; \n"
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
                
                +"  String f; @NonNull String ff; @Nullable String fff; \n"
                
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
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNullInitialization) in method m1",12
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNullInitialization) in method m1a",21
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2",7
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",7
                ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m3",7
                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m3a",8
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m4",7
                ,"/tt/TestJava.java:39: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m4a",7
                );
    }
    

    public void testNNAssign3() {
        helpTCX("tt.TestJava","package tt; \n"
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
                
                +"  String f; @NonNull String ff; @Nullable String fff; \n"
                
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
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNullInitialization) in method m1a",21
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",7
                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m3a",8
                ,"/tt/TestJava.java:39: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m4a",7
                );
    }
    
    public void testNNAssignB() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  public static class A {\n" 
                +"      String q; @NonNull String qq; @Nullable String qqq; \n"
                +"      static String r; static @NonNull String rr; static @Nullable String rrr; \n"
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
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m1a",10
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",10
                );
    }
        
    public void testNNAssignB1() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public static class A {\n" // Tests whether this gets the enclosing class's annotation
                +"      String q; @NonNull String qq; @Nullable String qqq; \n"
                +"      static String r; static @NonNull String rr; static @Nullable String rrr; \n"
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
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m1",9
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m1a",10
                ,"/tt/TestJava.java:21: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2",9
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",10
                );
    }
    
    public void testNNAssignB2() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NullableByDefault public class TestJava { \n"
                
                +"  public static class A {\n" 
                +"      String q; @NonNull String qq; @Nullable String qqq; \n"
                +"      static String r; static @NonNull String rr; static @Nullable String rrr; \n"
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
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m1a",10
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2a",10
                );
    }
    
    public void testDZero() {
        //options.put("-showbb","");
        helpTCX("tt.TestJava","package tt; \n"
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
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1",14
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1a",14
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2",17
                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2a",17
                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m3",7
                ,"/tt/TestJava.java:34: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m3a",7
                );
    }
    
//    // THIS ONE BLOWS THE PROVER ??? FIXME (literal divide by zero)
//    public void testDZero2() {
////        options.put("-showbb","");
//        helpTCX("tt.TestJava","package tt; \n"
//                +" import org.jmlspecs.annotation.*; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1() {\n"
//                +"    int q = 5;\n"
//                +"    int r = q/(1-1);\n" // ERROR
//                +"  }\n"
//                
//                +"  public void m2() {\n"
//                +"    int q = 5;\n"
//                +"    int r = q/0;\n" // ERROR
//                +"  }\n"
//                
//                +"}"
//                );
//    }

    public void testArrayAccess() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NullableByDefault public class TestJava { \n"
                
                +"  public void m1() {\n"
                +"    int[] a = null;\n"
                +"    a[0] = 0;\n" // ERROR 
                +"  }\n"
                
                +"  public void m2() {\n"
                +"    int[] a = null;\n"
                +"    int i = (a)[0];\n" // ERROR 
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m1",6
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m2",16
                );
    }
   
    public void testAssignable() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  //@ assignable this.a;\n"
                +"  public void m1(TestJava o) {\n"
                +"    o.a = 0;\n"  // BAD
                +"  }\n"
                
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
                
                +"  //@ assignable this.a;\n"
                +"  public void m4x(TestJava o) {\n"
                +"    this.b = 0;\n"  // OK
                +"  }\n"
                
                +"  //@ assignable this.a;\n"
                +"  public void m4y(TestJava o) {\n"
                +"    TestJava.b = 0;\n"  // OK
                +"  }\n"
                
                +"  //@ assignable this.a;\n"
                +"  public void m4a(TestJava o) {\n"
                +"    o.a = 0;\n"  // BAD
                +"  }\n"
                
                +"  //@ assignable this.a;\n"
                +"  public void m4b(TestJava o) {\n"
                +"    //@ assume this == o; \n"
                +"    o.a = 0;\n"  // OK
                +"  }\n"
                
                +"  //@ assignable this.a;\n"
                +"  public void m5(TestJava o) {\n"
                +"    a = 0;\n"  // OK
                +"  }\n"
                
                +"  //@ assignable a;\n"
                +"  public void m6(TestJava o) {\n"
                +"    a = 0;\n"  // OK
                +"  }\n"
                
                +"  //@ assignable \\nothing;\n"
                +"  public void m7(TestJava o) {\n"
                +"    a = 0;\n"  // BAD
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
                
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assignable) in method m1",9
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assignable) in method m2",9
                ,"/tt/TestJava.java:33: warning: The prover cannot establish an assertion (Assignable) in method m4a",9
                ,"/tt/TestJava.java:50: warning: The prover cannot establish an assertion (Assignable) in method m7",7
                ,"/tt/TestJava.java:63: warning: The prover cannot establish an assertion (Assignable) in method m9b",9
                );
    }
   

}