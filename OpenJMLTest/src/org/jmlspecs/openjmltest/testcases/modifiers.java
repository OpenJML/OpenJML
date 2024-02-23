package org.jmlspecs.openjmltest.testcases;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjmltest.TCBase;
import org.junit.*;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class modifiers extends TCBase {

    @Before
    public void setUp() throws Exception {
      //noCollectDiagnostics = true;
      //jmldebug = true;
      super.setUp();
      main.addOptions("-no-require-white-space");
    }
    

    @Test public void testClassMods() {
        helpTCF("t/A.java","package t; \n /*@ pure */class A{}");
    }
    
    @Test public void testClassMods2() {
        helpTCF("t/A.java","package t; \n /*@ helper */class A{}",
                "/t/A.java:2: error: This JML modifier is not allowed for a type declaration", 6
                );
    }
    
    @Test public void testClassMods3() {
        helpTCF("t/A.java","package t; \n  static class A{}",
            "/t/A.java:2: error: modifier static not allowed here", 10);
    }
    
    @Test public void testClassMods4() {
        String s = "public class A{}";
        helpTCF("A.java",s);
    }
    
    @Test public void testClassMods5() {
        String s = "protected class A{}";
        helpTCF("A.java",s,
                "/A.java:1: error: modifier protected not allowed here",11
                );
    }
    
    @Test public void testClassMods6() {
        helpTCF("t/A.java","package t; \n /*@ pure pure */class A{}",
                "/t/A.java:2: error: org.jmlspecs.annotation.Pure is not a repeatable annotation interface", 11);
    }
    
    @Test public void testClassMods7() {
        helpTCF("t/A.java","package t; \n /*@ pure */public class A{}");
    }
    
    @Test public void testClassMods8() {
        helpTCF("t/A.java","package t; \n public /*@ pure */class A{}");
    }
    
    @Test public void testClassMods9() {
        helpTCF("t/A.java","package t; import org.jmlspecs.annotation.*; \n public /*@ pure */ @Pure class A{}",
                "/t/A.java:2: error: org.jmlspecs.annotation.Pure is not a repeatable annotation interface", 21
                );
    }
    
    /** Testing annotations without the import */
    @Test public void testClassMods10() {
        helpTCF("t/A.java","package t;  \n public /*@ pure */ @Pure class A{}",
                "/t/A.java:2: error: cannot find symbol\n  symbol: class Pure", 22
		);
    }
    
    @Test public void testClassMods11() {
        helpTCF("A.java"," \n public /*@ helper */  class A{}",
                "/A.java:2: error: This JML modifier is not allowed for a type declaration", 13);
    }
    
    @Test public void testClassMods12() {
        helpTCF("A.java"," \n @Deprecated public class A{}"
                );
    }
    
    @Test public void testClassMods13() {
        helpTCF("A.java"," \n //@ public model class A{}");
    }
    
    @Test public void testClassMods13a() {
        helpTCF("A.java","import org.jmlspecs.annotation.*;\n //@ public @Model class A{}");
    }
    
    @Test public void testClassMods13b() {
        helpTCF("A.java"," \n public /*@ model*/ class A{}"
                ,"/A.java:2: error: A Java declaration (not within a JML annotation) may not be either ghost or model: A",13
                );
    }
    
    @Test public void testClassMods13c() {
        helpTCF("A.java","import org.jmlspecs.annotation.*;\n public /*@ Model*/ class A{}"
                ,"/A.java:2: error: Unexpected or misspelled JML token: Model",13);
    }
    
    @Test public void testClassMods13d() { // No import, so cannot resolve Model
        helpTCF("A.java","\n //@ public @Model class A{}"
                ,"/A.java:2: error: cannot find symbol\n  symbol: class Model",14
                ,"/A.java:2: error: A method or type declaration within a JML annotation must be model: A", 20
                );
    }
    
    @Test public void testClassMods13e() { // No import, so cannot resolve Model
        helpTCF("A.java","\n     public @Model class A{}"
                ,"/A.java:2: error: cannot find symbol\n  symbol: class Model",14
                );
    }
    
    @Test public void testClassMods14() {
        helpTCF("A.java","public class A{} \n //@        ghost class B{}\n   class C{}"
                ,"/A.java:2: error: A method or type declaration within a JML annotation must be model: B",19
                ,"/A.java:2: error: This JML modifier is not allowed for a type declaration", 13
                );
    }
    
    @Test public void testClassMods14a() {
        helpTCF("A.java"," \n public /*@ghost*/ class A{}"
                ,"/A.java:2: error: This JML modifier is not allowed for a type declaration", 12
                );
    }
    
    @Test public void testClassMods14b() {
        helpTCF("A.java","import org.jmlspecs.annotation.*;\n //@  @Ghost class B{}\n public class A {}"
                ,"/A.java:2: error: A method or type declaration within a JML annotation must be model: B",14
                ,"/A.java:2: error: This JML modifier is not allowed for a type declaration", 7
                );
    }
  

    @Test public void testClassMods14c() {
        // Don't need the runtime path, since the @Ghost annotation is looked up on the classpath,
        // but this makes the compiler look for specs for Ghost as a binary class, and exercises a different
        // code path
        specs.setSpecsPath(new String[]{"$A","$B","$SY"});
        helpTCF("A.java","import org.jmlspecs.annotation.*;  \n public @Ghost class A{}"
        		,"/A.java:2: error: This JML modifier is not allowed for a type declaration", 9);
    }
    
    @Test public void testClassMods14d() {
        // Don't need the runtime path, since the @Ghost annotation is looked up on the classpath,
        // but this makes the compiler look for specs for Ghost as a binary class, and exercises a different
        // code path
        specs.setSpecsPath(new String[]{"$A","$B","$SY"});
        helpTCF("A.java","import org.jmlspecs.annotation.*;  \n public @Ghost class A{}"
                ,"/A.java:2: error: This JML modifier is not allowed for a type declaration", 9
                );
    }
    
    @Test public void testClassMods15() {
        specs.setSpecsPath(new String[]{"$A","$B","$SY"});
        helpTCF("A.java","import org.jmlspecs.annotation.*;  \n public @NullableByDefault class A{}"
                );
    }
    
    @Test public void testClassMods15a() {
        specs.setSpecsPath(new String[]{"$A","$B","$SY"});
        helpTCF("A.java","import org.jmlspecs.annotation.*;  \n public @NonNullByDefault class A{}"
                );
    }
    
    @Test public void testClassMods15b() {
        specs.setSpecsPath(new String[]{"$A","$B","$SY"});
        helpTCF("A.java","public /*@nullable_by_default*/ class A{}"
                );
    }
    
    @Test public void testClassMods15c() {
        specs.setSpecsPath(new String[]{"$A","$B","$SY"});
        helpTCF("A.java","public /*@non_null_by_default*/ class A{}"
                );
    }
    
    @Test public void testClassMods15d() {
        specs.setSpecsPath(new String[]{"$A","$B","$SY"});
        helpTCF("A.java","public /*@nullable_by_default non_null_by_default*/ class A{}"
                ,"/A.java:1: error: A declaration may not be both non_null_by_default and nullable_by_default",31
                );
    }
    
    @Test public void testClassMods15e() {
        specs.setSpecsPath(new String[]{"$A","$B","$SY"});
        helpTCF("AAA.java","import org.jmlspecs.annotation.*;  \n public @NonNullByDefault @NullableByDefault class AAA{}"
                ,"/AAA.java:2: error: A declaration may not be both non_null_by_default and nullable_by_default",27
                );
    }
    
    @Test public void testOnlyModelClass() {
        helpTCF("A.java","public class A {}\n //@ public model class B{}\n\n",
                "/A.java:2: error: class B is public, should be declared in a file named B.java", 19);
    }
    
    @Test public void testOnlyModelClass1() {
        helpTCF("A.java","public class A {}\n //@ class B{}\n\n",
                "/A.java:2: error: A method or type declaration within a JML annotation must be model: B", 6);
    }
    
    @Test public void testOnlyModelClass2() {
        helpTCF("A.java","public class A {}\n public /*@ model*/ class B{}"
                ,"/A.java:2: error: class B is public, should be declared in a file named B.java", 21
                ,"/A.java:2: error: A Java declaration (not within a JML annotation) may not be either ghost or model: B", 13
                );
    }

    @Test public void testOnlyModelClass3() {
        helpTCF("A.java","public class A {}\n //@ model class B{}\n\n"
                );
    }
    
    // Tests 4, 4a, 4b check that JML comments at the very end of a file
    // are indeed processed.  There had been a bug in the OpenJDK scanner that 
    // ignored comments at the end of a file.
    @Test public void testOnlyModelClass4() {
        helpTCF("A.java","public class A {}\n //@ public model class B{}",
                "/A.java:2: error: class B is public, should be declared in a file named B.java", 19);
    }
    
    @Test public void testOnlyModelClass4a() {
        helpTCF("A.java","public class A {}\n //@ public model class B{}\n",
                "/A.java:2: error: class B is public, should be declared in a file named B.java", 19);
    }
    
    @Test public void testOnlyModelClass4b() {
        helpTCF("A.java","public class A {}\n /*@ public model class B{}*/",
                "/A.java:2: error: class B is public, should be declared in a file named B.java", 19);
    }
    
    @Test public void testOnlyModelClass6() {
        helpTCF("A.java","public class A {}\n @Model class B{}\n\n"
                ,"/A.java:2: error: cannot find symbol\n  symbol: class Model",3
                );
    }
    
    @Test public void testOnlyModelClass7() {
        helpTCF("A.java","public class A {}\n //@ @Model class B{}\n\n"
                ,"/A.java:2: error: cannot find symbol\n  symbol: class Model",7
                ,"/A.java:2: error: A method or type declaration within a JML annotation must be model: B", 13
                );
    }
    
    @Test public void testOnlyModelClass6a() {
        helpTCF("A.java","import org.jmlspecs.annotation.*;\npublic class A {}\n @Model class B{}\n\n"
                ,"/A.java:3: error: A Java declaration (not within a JML annotation) may not be either ghost or model: B", 2
                );
    }
   @Test public void testOnlyModelClass7a() {
        helpTCF("A.java","import org.jmlspecs.annotation.*;\npublic class A {}\n //@ @Model class B{}\n\n"
                );
    }
    
    
    @Test public void testCUMods() {
        helpTCF("t/A.java","@Pure package t; import org.jmlspecs.annotation.*;  \n public /*@ pure */ @Pure class A{}",
                "/t/A.java:1: error: package annotations should be in file package-info.java",1,
                "/t/A.java:2: error: org.jmlspecs.annotation.Pure is not a repeatable annotation interface", 21
                );
    }
    
    @Test public void testCUMods2() {
        helpTCF("t/A.java","package t; import org.jmlspecs.annotation.*;  \n public /*@ pure */ @Pure class A{}"
                ,"/t/A.java:2: error: org.jmlspecs.annotation.Pure is not a repeatable annotation interface", 21
                );
    }
    
    @Test public void testCUMods3() {
        helpTCF("t/A.java","package t; /*@ pure */ import org.jmlspecs.annotation.*; \n public /*@ pure */ class A{}"
                ,"/t/A.java:1: error: No modifiers are allowed on an import statement", 16
                );
    }
    
    @Test public void testCUMods4() {
        helpTCF("t/A.java","package t; import org.jmlspecs.annotation.*; \n public /*@ pure */ @Pure class A{}"
                ,"/t/A.java:2: error: org.jmlspecs.annotation.Pure is not a repeatable annotation interface", 21
                );
    }
    
    @Test public void testCUMods5() {
        helpTCF("t/A.java","package t; @Pure import org.jmlspecs.annotation.*; \n public @Pure class A{}"
                ,"/t/A.java:1: error: class, interface, enum, or record expected", 18
                );
    }
    
    @Test public void testInterface1() {
        helpTCF("t/A.java","package t; \n interface I { /*@ instance model  int i; */ } public class A implements I { /*@ represents i = 8; */ }"
                );  // OK no errors
    }
    
    @Test public void testInterface1a() {
        helpTCF("t/A.java","package t; \n interface I { /*@  model static int i; */ } public class A implements I { /*@ represents i = 8; */ }"
                ,"/t/A.java:2: error: A represents clause and its associated model field must both be static or both not be static",80
                ,"/t/A.java:2: error: A represents clause must be declared in the same class as the static model field it represents: t.I.i",91
                ,"/t/A.java:2: Note: Associated declaration: /t/A.java:2:",38
                );  
    }
    
    @Test public void testInterface1b() {
        helpTCF("t/A.java","package t; \n interface I { /*@ model instance int i; */ } public class A implements I { /*@ static represents i = 8; */ }"
                ,"/t/A.java:2: error: A represents clause and its associated model field must both be static or both not be static",88
                );  
    }
    
    @Test public void testInterface1c() {
        helpTCF("t/A.java","package t; \n interface I { /*@ model static int i; */ } public class A implements I { /*@ static represents i = 8; */ }"
                ,"/t/A.java:2: error: A represents clause must be declared in the same class as the static model field it represents: t.I.i",97
                ,"/t/A.java:2: Note: Associated declaration: /t/A.java:2:",37
                ); 
    }
    
    // make sure ghost fields are not final by default; should be static by default
    @Test public void testInterface2() {
        helpTCF("t/A.java","package t; \n interface I { /*@ ghost int i; */ } public class A implements I { static void m() { /*@ set i = 8; */ }}"
                ); // OK - no errors
    }
    
    // make sure that instance works
    @Test public void testInterface3() {
        helpTCF("t/A.java","package t; \n interface I { /*@ instance ghost int i; */ } public class A implements I { static void m() { /*@ set i = 8; */ }}"
                ,"/t/A.java:2: error: non-static variable i cannot be referenced from a static context",103
                );
    }
    
    // cannot be model and final
    @Test public void testInterface4() {
        helpTCF("t/A.java","package t; \n interface I { /*@ final model static int i; */ } public class A implements I { /*@ final model instance int j = 0;*/ }"
//                ,"/t/A.java:2: error: A declaration may not be both model and final",26
//                ,"/t/A.java:2: error: A declaration may not be both model and final",84
                );
    }
    
    @Test public void testMatchClass() {
        addMockFile("$A/A.jml"," class A {}");
        helpTCF("A.java","public class A{}"
                ,"/$A/A.jml:1: error: The type A in the specification matches a Java type with different modifiers: public", 2
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:", 8
                );
    }
    
    @Test public void testMatchClass2() {
        addMockFile("$A/A.jml","public class A<T> {}");
        helpTCF("A.java","public class A<T,U>{}"
                ,"/$A/A.jml:1: error: The type A<T> in the specification matches a Java type A<T,U> with a different number of type arguments", 8
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:", 8
                );
    }
    
    @Test public void testMatchClass3() { // FIXME - this should fail - need to compare the type parameters
        addMockFile("$A/A.jml","public class A<T> {}");
        helpTCF("A.java","public class A<T extends java.util.List>{}");//,
               // "/A.java:1: error: The type A in the specification matches a Java type A with different modifiers: public ", 2);
    }
    
    @Test public void testMatchField() {
        addMockFile("$A/A.jml","public class A { int k; }");
        helpTCF("A.java","public class A{}",
                "/$A/A.jml:1: error: There is no field to match this Java declaration in the specification file: A.k", 22);
    }
    
    @Test public void testMatchField2() {
        addMockFile("$A/A.jml","public class A { /*@ ghost int k; */}");
        helpTCF("A.java","public class A{}");  // OK
    }
    
    @Test public void testMatchField2a() {
        addMockFile("$A/A.jml","public class A { /*@ model int k; */}");
        helpTCF("A.java","public class A{}");  // OK
    }
    
    @Test public void testMatchField3() { 
        addMockFile("$A/A.jml","public class A { /*@ ghost int k; */}");
        helpTCF("A.java","public class A{}");  // OK
    }
    
    /** Missing a ghost or model modifier */
    @Test public void testMatchField3a() {
        addMockFile("$A/A.jml","public class A { /*@ int k; */}");
        helpTCF("A.java","public class A{}"
                ,"/$A/A.jml:1: error: A declaration within a JML annotation must be either ghost or model: A.k", 26
                ); 
    }
    
    @Test public void testMatchField4() {
        addMockFile("$A/A.jml","public class A { int k=0; }");
        helpTCF("A.java","public class A{ int k; }",
                "/$A/A.jml:1: error: Field initializers are not permitted in specification files: A.k", 24);
    }
    
    @Test public void testMatchField5() {
        addMockFile("$A/A.jml","public class A { public int k; }");
        helpTCF("A.java","public class A{ protected int k; }"
                ,"/$A/A.jml:1: error: The field A.k in the specification matches a Java field with different modifiers: public protected", 29
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:", 31
                );
    }

    @Test public void testMatchField6() { 
        addMockFile("$A/A.jml","public class A { boolean k; }");
        helpTCF("A.java","public class A{ int k; }"
                ,"/$A/A.jml:1: error: Type of field A.k in specification differs from type in source/binary: boolean vs. int",18
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:",21
                );
    }
    
    @Test public void testMatchField7() {  
        addMockFile("$A/A.jml","public class A { String k; }");
        helpTCF("A.java","public class A{ Object k; }",
                "/$A/A.jml:1: error: Type of field A.k in specification differs from type in source/binary: java.lang.String vs. java.lang.Object",18
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:",24
        		);
    }
    
    @Test public void testMatchField8() { 
        addMockFile("$A/A.jml","public class A { Object k; }");
        helpTCF("A.java","public class A{ java.lang.Object k; }"); // OK
    }
    
    @Test public void testMatchField9() { 
        addMockFile("$A/A.jml","public class A { Class<String> k; }");
        helpTCF("A.java","public class A{ Class<Object> k; }",
                "/$A/A.jml:1: error: Type of field A.k in specification differs from type in source/binary: java.lang.Class<java.lang.String> vs. java.lang.Class<java.lang.Object>", 23
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:",31
        		); 
    }
    
    @Test public void testMatchMethod() { 
        addMockFile("$A/A.jml","public class A { void m(int i); }");
        helpTCF("A.java","public class A{ void m(boolean i) {} void m(int i) {} }"); 
    }
    
    @Test public void testMatchMethod1() { 
        addMockFile("$A/A.jml","public class A { void m(int i); }");
        helpTCF("A.java","public class A{ void m(boolean i) {} void m(Object i) {} }",
                "/$A/A.jml:1: error: There is no method to match this Java declaration in the specification file: A.m(int)", 23
                ); 
    }
    
    @Test public void testMatchMethod2() { // Should be OK
        addMockFile("$A/A.jml","public class A { void m(Object i); }");
        helpTCF("A.java","public class A{ void m(boolean i) {} void m(java.lang.Object i) {} }"); 
    }
    
    @Test public void testMatchMethod3() { 
        addMockFile("$A/A.jml","public class A { void m(int i, boolean j); }");
        helpTCF("A.java","public class A{ void m(boolean i) {} void m(int i) {} }"
                ,"/$A/A.jml:1: error: There is no method to match this Java declaration in the specification file: A.m(int,boolean)", 23
                ); 
    }
    
    @Test public void testMatchMethod4() { 
        addMockFile("$A/A.jml","public class A { public void m(int i); }");
        helpTCF("A.java","public class A{ void m(boolean i) {} void m(int i) { } }"
                ,"/$A/A.jml:1: error: The method A.m(int) in the specification matches a Java method with different modifiers: public", 30
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:",43); 
    }
    
    @Test public void testMatchMethod5() { 
        addMockFile("$A/A.jml","public class A { public Object m(int i); }");
        helpTCF("A.java","public class A{ void m(boolean i) {}  private java.lang.Object m(int i) { return null; } }"
                ,"/$A/A.jml:1: error: The method A.m(int) in the specification matches a Java method with different modifiers: public private", 32
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:",64
                ); 
    }
    
    @Test public void testMatchMethod6() {
        addMockFile("$A/A.jml","public class A { public void m(int i); }");
        helpTCF("A.java","public class A{ void m(boolean i) {}  public String m(int i) { return null; } }"
                ,"/$A/A.jml:1: error: The result type of method A.m(int) in the specification differs from the type in the source/binary: void vs. java.lang.String", 25
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:", 53
                ); 
    }
    
    @Test public void testMatchMethod6a() {
        addMockFile("$A/A.jml","public class A { public void m(int i); }");
        helpTCF("A.java","public class A{ public void m(int i) {}  public String m(int i) { return null; } }"
        		,"/A.java:1: error: method m(int) is already defined in class A", 56
                ); 
    }
    
    @Test public void testMatchMethod6b() {
        addMockFile("$A/A.jml","public class A { public void m(boolean i); }");
        helpTCF("A.java","public class A{ public void m(boolean i) {}  public void m(int i) { } }"
                ); 
    }
    
    @Test public void testMatchMethod7() { 
        addMockFile("$A/A.jml","public class A { public void m(int j, Object k); }");
        helpTCF("A.java","public class A{ void m(boolean i) {}  public String m(int i, Object mm) { return null; } }"
                ,"/$A/A.jml:1: error: The result type of method A.m(int,java.lang.Object) in the specification differs from the type in the source/binary: void vs. java.lang.String",25
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:", 53
                );
    }

    @Test public void testMatchMethod8() { 
        addMockFile("$A/A.jml","public class A { public void m() {} }");
        helpTCF("A.java","public class A{ void m(boolean i) {}  public void m() {  } }",
                "/$A/A.jml:1: error: The specification of the method A.m() must not have a body",34); 
    }
    
    @Test public void testTopLevelClass() {
        helpTCF("A.java","/*@pure nullable_by_default*/ public class A{ }"
        );
    }
    
    @Test public void testTopLevelClass2() {
        helpTCF("A.java","/*@helper ghost spec_public*/ public class A{ }"
                ,"/A.java:1: error: This JML modifier is not allowed for a type declaration",4
                ,"/A.java:1: error: This JML modifier is not allowed for a type declaration",11
                ,"/A.java:1: warning: There is no point to a declaration being both public and spec_public",17
        );
    }
    
    @Test public void testTopLevelClass3() {
        helpTCF("A.java","/*@ model */ public class A{ }"
                ,"/A.java:1: error: A Java declaration (not within a JML annotation) may not be either ghost or model: A",5
        );
    }
    
    @Test public void testTopLevelInterface() {
        helpTCF("A.java","/*@pure nullable_by_default*/ public interface A{ }"
        );
    }
    
    @Test public void testTopLevelInterface2() {
        helpTCF("A.java","/*@helper ghost spec_protected*/ public interface A{ }"
                ,"/A.java:1: error: This JML modifier is not allowed for a type declaration",4
                ,"/A.java:1: error: This JML modifier is not allowed for a type declaration",11
                ,"/A.java:1: warning: There is no point to a declaration being both public and spec_protected",17
        );
    }
    
    @Test public void testTopLevelInterface3() {
        helpTCF("A.java","/*@ model*/ public interface A{ }"
                ,"/A.java:1: error: A Java declaration (not within a JML annotation) may not be either ghost or model: A",5
        );
    }
    
    @Test public void testNestedClass() {
        helpTCF("A.java","public class A{ /*@pure spec_public*/ private class B {}}"
        );
    }
    
    @Test public void testNestedClass2() {
        helpTCF("A.java","public class A{ /*@pure spec_protected*/ private class B {}}"
        );
    }
    
    @Test public void testNestedClass3() {
        helpTCF("A.java","public class A{ /*@helper ghost */ public class B {}}"
                ,"/A.java:1: error: This JML modifier is not allowed for a nested type declaration",20
                ,"/A.java:1: error: This JML modifier is not allowed for a nested type declaration",27
        );
    }

    // TODO - It seems this should be allowed, but check the JML definition
    @Test public void testNestedClass3a() {
        helpTCF("A.java","public class A{ /*@nullable_by_default*/ public class B {}}"
        );
    }
    
    @Test public void testNestedClass4() {
        helpTCF("A.java","public class A{ /*@spec_public spec_protected*/ private class B {}}"
                ,"/A.java:1: error: A declaration may not be both spec_public and spec_protected",32
        );
    }
    
    @Test public void testNestedClass5() {
        helpTCF("A.java","public class A{ /*@ model*/ private class B {}}"
                ,"/A.java:1: error: A Java declaration (not within a JML annotation) may not be either ghost or model: A.B",21
        );
    }
    
    @Test public void testNestedInterface() {
        helpTCF("A.java","public class A{ /*@pure spec_public*/ private interface B {}}"
        );
    }
    
    @Test public void testNestedInterface2() {
        helpTCF("A.java","public class A{ /*@pure spec_protected*/ private interface B {}}"
        );
    }
    
    @Test public void testNestedInterface3() {
        helpTCF("A.java","public class A{ /*@helper ghost */ public interface B {}}"
                ,"/A.java:1: error: This JML modifier is not allowed for a nested type declaration",20
                ,"/A.java:1: error: This JML modifier is not allowed for a nested type declaration",27
        );
    }
    
    @Test public void testNestedInterface4() {
        helpTCF("A.java","public class A{ /*@ model */ public interface B {}}"
        		,"/A.java:1: error: A Java declaration (not within a JML annotation) may not be either ghost or model: A.B",21
        );
    }
    
    // TODO - It seems this should be allowed, but check the JML definition
    @Test public void testNestedInterface5() {
        helpTCF("A.java","public class A{ /*@nullable_by_default*/ public interface B {}}"
        );
    }
    
    @Test public void testNestedInterface6() {
        helpTCF("A.java","public class A{ /*@spec_public spec_protected*/ private interface B {}}"
                ,"/A.java:1: error: A declaration may not be both spec_public and spec_protected",32
                ); 
    }
    
    @Test public void testLocalClass() {
        helpTCF("A.java","public class A{ void m() {\n /*@ pure  */ class C {}; } }"
                ); 
        
    }
    
    @Test public void testLocalClass1() {
        helpTCF("A.java","public class A{ void m() {\n /*@ model  */ class C {}; } }"
                ,"/A.java:2: error: A Java declaration (not within a JML annotation) may not be either ghost or model: C",6
                ); 
        
    }
    
    @Test public void testLocalClass2() {
        helpTCF("A.java","public class A{ void m() {\n /*@ model   class C {}*/ } }"
                ); 
        
    }
    
    @Test public void testLocalClass2a() {
        helpTCF("A.java","public class A{ void m() {\n /*@         class C {};*/ } }"
        		,"/A.java:2: error: A method or type declaration within a JML annotation must be model: C", 14
                ); 
        
    }
    
    @Test public void testLocalClass3() {
        helpTCF("A.java","public class A{ void m() {\n /*@ helper spec_public */ class C {}; } }"
                ,"/A.java:2: error: This JML modifier is not allowed for a local type declaration",6
                ,"/A.java:2: error: This JML modifier is not allowed for a local type declaration",13
                ); 
        
    }
    
    @Test public void testLocalClass4() {
        helpTCF("A.java","public class A{ void m() {\n /*@ ghost  class C {} */ } }"
                ,"/A.java:2: error: A method or type declaration within a JML annotation must be model: C",13
                ,"/A.java:2: error: This JML modifier is not allowed for a local type declaration",6
                ); 
        
    }
    
    @Test public void testField() {
        helpTCF("A.java","public class A{ /*@spec_public spec_protected*/ Object o;}"
                ,"/A.java:1: error: A declaration may not be both spec_public and spec_protected",32
                );
    }
    
    @Test public void testField1() {
        helpTCF("A.java","public class A{ /*@non_null nullable*/ Object o;}"
                ,"/A.java:1: error: A declaration may not be both non_null and nullable",29  // FIXME - duplicate messages
                ,"/A.java:1: error: A type may not be declared both non_null and nullable",40
                );
    }
    
    @Test public void testField2() {
        helpTCF("A.java","public class A{ /*@spec_public instance monitored non_null*/ Object o;}"
                );
    }
    
    @Test public void testField3() {
        helpTCF("A.java","public class A{ /*@spec_protected instance monitored nullable*/ Object o;}"
                );
    }
    
    @Test public void testField4() {
        helpTCF("A.java","public class A{ /*@helper*/ Object o;}"
                ,"/A.java:1: error: This JML modifier is not allowed for a field declaration",20
                );
    }
    
    @Test public void testGhostField() {
        helpTCF("A.java","public class A{ /*@ghost Object o; */}"
                );
    }
    
    @Test public void testGhostField1() {
        helpTCF("A.java","public class A{ /*@ghost non_null nullable Object o; */}"
                ,"/A.java:1: error: A declaration may not be both non_null and nullable", 35
                ,"/A.java:1: error: A type may not be declared both non_null and nullable", 44 // FIXME - duplicate
                );
    }
    
    @Test public void testGhostField2() {
        helpTCF("A.java","public class A{ /*@ghost instance monitored non_null Object o; */}"
                );
    }
    
    @Test public void testGhostField3() {
        helpTCF("A.java","public class A{ /*@ghost instance monitored nullable Object o; */}"
                );
    }
    
    @Test public void testGhostField4() {
        helpTCF("A.java","public class A{ /*@ghost helper spec_protected Object o;*/}" // FIXME - name modifier and need messages for both
                ,"/A.java:1: error: This JML modifier is not allowed for a ghost field declaration",26
                ,"/A.java:1: error: This JML modifier is not allowed for a ghost field declaration",33
                );
    }
     
    @Test public void testGhostField5() {
        helpTCF("A.java","public class A{ /*@ghost helper spec_public Object o;*/}" // FIXME - name modifier and need messages for both
                ,"/A.java:1: error: This JML modifier is not allowed for a ghost field declaration",26
                ,"/A.java:1: error: This JML modifier is not allowed for a ghost field declaration",33
                );
    }
     
    
    @Test public void testModelField() {
        helpTCF("A.java","public class A{ /*@model ghost Object oooo; */}"
                ,"/A.java:1: error: This JML modifier is not allowed for a ghost field declaration",20
                );
    }
    
    @Test public void testModelField1() {
        helpTCF("A.java","public class A{ /*@model non_null nullable Object o; */}"
                ,"/A.java:1: error: A declaration may not be both non_null and nullable", 35
                ,"/A.java:1: error: A type may not be declared both non_null and nullable", 44
                );
    }
    
    @Test public void testModelField2() {
        helpTCF("A.java","public class A{ /*@model instance non_null Object o; */}"
                );
    }
    
    @Test public void testModelField3() {
        helpTCF("A.java","public class A{ /*@model instance nullable Object o; */}"
                );
    }
    
    @Test public void testModelField4() {
        helpTCF("A.java","public class A{ /*@model helper monitored spec_public Object o;*/}"
                ,"/A.java:1: error: This JML modifier is not allowed for a model field declaration",26
                ,"/A.java:1: error: This JML modifier is not allowed for a model field declaration",33
                ,"/A.java:1: error: This JML modifier is not allowed for a model field declaration",43
                );
    }
     
    @Test public void testModelField5() {
        helpTCF("A.java","public class A{ /*@model helper monitored spec_protected Object o;*/}"
                ,"/A.java:1: error: This JML modifier is not allowed for a model field declaration",26
                ,"/A.java:1: error: This JML modifier is not allowed for a model field declaration",33
                ,"/A.java:1: error: This JML modifier is not allowed for a model field declaration",43
                );
    }
     
    @Test public void testMethod() {
        helpTCF("A.java","public class A{ /*@ pure spec_protected extract non_null */ Object m(){ return null; } }"
                );
    }
     
    @Test public void testMethod0() {
        helpTCF("A.java","public class A{ /*@ pure helper private extract non_null */ Object m(){ return null; } }"
                );
    }
     
    @Test public void testInterfaceMethod() {
        helpTCF("A.java","public interface A{ /*@ pure spec_protected extract non_null */ Object m(); }"
                ,"/A.java:1: error: This JML modifier is not allowed for a interface method declaration",45
                );
    }
     
    @Test public void testMethod2() {
        helpTCF("A.java","public class A{ /*@ pure spec_public nullable */ Object m(){ return null;} }"
                );
    }
     
    @Test public void testMethod2a() {
        helpTCF("A.java","public class A{ /*@ pure helper private nullable */ Object m(){ return null;} }"
                );
    }
     
    @Test public void testMethod3() {
        helpTCF("A.java","public class A{ /*@ query */ void m(){} }"
                );
    }
     
    @Test public void testMethod4() {
        helpTCF("A.java","public class A{ /*@ spec_public spec_protected */ void m(){} }"
                ,"/A.java:1: error: A declaration may not be both spec_public and spec_protected",33
                );
    }
     
    @Test public void testMethod5() {
        helpTCF("A.java","public class A{ /*@ non_null nullable */ Object m(){return null;} }"
                ,"/A.java:1: error: A declaration may not be both non_null and nullable",30
                );
    }
     
    @Test public void testConstructor() {
        helpTCF("A.java","public class A{ /*@ pure spec_protected extract */ A(){} }"
                );
    }
     
    @Test public void testConstructor0() {
        helpTCF("A.java","public class A{ /*@ pure extract helper private */ A(){} }"
                );
    }
     
    @Test public void testConstructor1() {
        helpTCF("A.java","public class A{ /*@ pure spec_public */ A(){} }"
                );
    }
     
    @Test public void testConstructor1a() {
        helpTCF("A.java","public class A{ /*@ pure helper private */ A(){} }"
                );
    }
     
    @Test public void testConstructor3() {
        helpTCF("A.java","public class A{ \n/*@ instance non_null nullable */ A(){} }"
                ,"/A.java:2: error: This JML modifier is not allowed for a constructor declaration",5
                ,"/A.java:2: error: This JML modifier is not allowed for a constructor declaration",14
                ,"/A.java:2: error: This JML modifier is not allowed for a constructor declaration",23
                );
    }
     
    @Test public void testConstructor4() {
        helpTCF("A.java","public class A{ \n/*@ spec_public spec_protected */ A(){} }"
                ,"/A.java:2: error: A declaration may not be both spec_public and spec_protected",17
                );
    }
     
    
    @Test public void testModelMethod() {
        helpTCF("A.java","public class A{ /*@ model pure extract non_null Object m(){ return null; } */ }"
                );
    }
     
    @Test public void testModelMethod0() {
        helpTCF("A.java","public class A{ /*@ model pure extract private helper non_null Object m(){ return null; } */ }"
                );
    }
     
    @Test public void testInterfaceModelMethod() {
        helpTCF("A.java","public interface A{ /*@ model pure extract non_null Object m(); */ }"
                ,"/A.java:1: error: This JML modifier is not allowed for a interface model method declaration",36
                );
    }
     
    @Test public void testModelMethod1() {
        helpTCF("A.java","public class A{ /*@ model pure nullable Object m(){ return null; } */ }"
                );
    }
     
    @Test public void testModelMethod1a() {
        helpTCF("A.java","public class A{ /*@ model pure private helper nullable Object m(); */ }"
                );
    }
     
    @Test public void testModelMethod2() {
        helpTCF("A.java","public class A{ /*@ model instance spec_public spec_protected void m(){}*/  }"
                ,"/A.java:1: error: This JML modifier is not allowed for a model method declaration",27
                ,"/A.java:1: error: This JML modifier is not allowed for a model method declaration",36
                ,"/A.java:1: error: This JML modifier is not allowed for a model method declaration",48
                );
    }
     
    @Test public void testModelMethod3() {
        helpTCF("A.java","public class A{ /*@ model non_null nullable  Object m(){ return null; }*/ }"
                ,"/A.java:1: error: A declaration may not be both non_null and nullable",36
                );
    }
     
    @Test public void testModelMethod4() {  // 
        helpTCF("A.java","public class A{ /*@ model non_null */  Object m(){ return null;} }"
                ,"/A.java:1: error: A Java method declaration must not be marked model: A.m()",21
                );
    }
     
    
    @Test public void testModelConstructor() {
        helpTCF("A.java","public class A{ A(int i) {} \n/*@ model pure extract  A(){} */ }"
                );
    }
     
    @Test public void testModelConstructor0() {
        helpTCF("A.java","public class A{ A(int i) {} \n/*@ model pure private helper extract  A(){} */ }"
                );
    }
     
    @Test public void testModelConstructor1() {
        helpTCF("A.java","public class A{ /*@ model pure  */ A(){} }"
                ,"/A.java:1: error: A Java method declaration must not be marked model: A.A()",21
                );
    }
     
    @Test public void testModelConstructor1a() {
        helpTCF("A.java","public class A{ /*@  pure private helper */ A(){} }"
                );
    }
     
     
    @Test public void testModelConstructor2() {
        helpTCF("A.java","public class A{ A(int i) {} \n/*@ model instance spec_public spec_protected A(){} */ }"
                ,"/A.java:2: error: This JML modifier is not allowed for a model constructor declaration",11
                ,"/A.java:2: error: This JML modifier is not allowed for a model constructor declaration",20
                ,"/A.java:2: error: This JML modifier is not allowed for a model constructor declaration",32
                );
    }
     
    @Test public void testModelConstructor2a() {
        helpTCF("A.java","public class A{ A(int i) {} \n/*@ model non_null nullable A(){} */ }"
                ,"/A.java:2: error: This JML modifier is not allowed for a model constructor declaration",11
                ,"/A.java:2: error: This JML modifier is not allowed for a model constructor declaration",20
                );
    }
     
    @Test public void testFormal() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  void m(\n" +
        		"/*@ non_null */ Object o, \n" +
        		"/*@ nullable */ Object oo, \n" +
        		"/*@ ghost non_null nullable */ Object ooo, \n" +
        		"/*@ non_null non_null */ Object ooob, \n" +
        		"/*@ spec_public */ Object oooo) {} }"
                ,"/A.java:6: error: org.jmlspecs.annotation.NonNull is not a repeatable annotation interface", 14
                ,"/A.java:5: error: This JML modifier is not allowed for a formal parameter",5
                ,"/A.java:5: error: A declaration may not be both non_null and nullable",20
                ,"/A.java:5: error: A type may not be declared both non_null and nullable", 32 // FIXME - duplicate
                ,"/A.java:7: error: This JML modifier is not allowed for a formal parameter",5
                );
    }
     
    @Test public void testLocalVar() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  void m() {\n /*@ uninitialized non_null */ Object o;} }"
                );
    }
     
    @Test public void testLocalVar1() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  void m() {\n /*@ uninitialized nullable */ Object o;} }"
                );
    }
     
    @Test public void testLocalVar2() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  void m() {\n /*@ ghost non_null */ Object o;} }"
                ,"/A.java:3: error: A Java local variable declaration (not within a JML annotation) may not be ghost: o in A.m()",31
                );
    }
     
    @Test public void testLocalVar3() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  void m() {\n /*@ ghost non_null Object o; */} }"
                );
    }
     
    @Test public void testLocalVar4() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  void m() {\n /*@ non_null non_null Object o; */} }"
                ,"/A.java:3: error: org.jmlspecs.annotation.NonNull is not a repeatable annotation interface",15
                ,"/A.java:3: error: A local declaration within a JML annotation must be ghost: o in A.m()",31
                );
    }
     
    @Test public void testLocalVar5() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  void m() {\n /*@ non_null nullable */ Object o; } }"
                ,"/A.java:3: error: A declaration may not be both non_null and nullable", 15
                ,"/A.java:3: error: A type may not be declared both non_null and nullable", 27 // FIXME - duplicate
                );
    }
     
    @Test public void testLocalVar6() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  void m() {\n /*@ helper */ Object o; } }"
                ,"/A.java:3: error: This JML modifier is not allowed for a local variable declaration",6
                );
    }
     
    @Test public void testLocalVar7() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  void m() {\n /*@ helper ghost  Object o; */} }"
                ,"/A.java:3: error: This JML modifier is not allowed for a local variable declaration",6
                );
    }
     
    @Test public void testLocalVar8() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  void m() {\n /*@   Object o; */} }"
                ,"/A.java:3: error: A local declaration within a JML annotation must be ghost: o in A.m()",15
                );
    }
     
    @Test public void testSpec() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  //@ public requires true;\n" +
                "  void m() {} }"
                ,"/A.java:2: error: No modifiers are allowed prior to a lightweight specification case",7
                );
    }
     
    @Test public void testSpec2() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  //@ pure requires true;\n" +
                "  void m() {} }"
                ,"/A.java:2: error: No modifiers are allowed prior to a lightweight specification case",7
                );
    }
     
    @Test public void testSpec3() {
        expectedExit = 0;
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  //@ code requires true;\n" +
                "  void m() {} }"
                ,"/A.java:2: warning: This code token is misplaced - it must be just prior to a behavior or example token",7
                );
    }
     
    @Test public void testSpec4() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  //@ public behavior requires true;\n" +
                "  public void m() {} }"
                ); // OK
    }
     
    @Test public void testSpec5() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  //@ pure behavior requires true;\n" +
                "  public void m() {} }"
                ,"/A.java:2: error: This JML modifier is not allowed for a specification case",7
                );
    }
     
    @Test public void testSpec6() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  //@ private code behavior requires true;\n" +
                "  void m() {} }"
                ); // OK
    }
     
    @Test public void testSpec7() {
    	expectedExit = 0;
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  //@ public also behavior requires true;\n" +
                "  void m() {} }"
                ,"/A.java:2: warning: No modifiers are allowed prior to a also token",7
                ,"/A.java:2: warning: Method m does not override parent class methods and so its specification may not begin with 'also'",14
                );
    }
     
    @Test public void testSpec8() {
    	expectedExit = 0;
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  //@ pure also behavior requires true;\n" +
                "  void m() {} }"
                ,"/A.java:2: warning: No modifiers are allowed prior to a also token",7
                ,"/A.java:2: warning: Method m does not override parent class methods and so its specification may not begin with 'also'",12
                );
    }
     
    @Test public void testSpec9() {
        expectedExit = 0;
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  //@ code also behavior requires true;\n" +
                "  void m() {} }"
                ,"/A.java:2: warning: This code token is misplaced - it must be just prior to a behavior or example token",7
                );
    }

    @Test public void testSpec10() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  //@ private public behavior requires true;\n" +
                "  void m() {} }"
                ,"/A.java:2: error: illegal combination of modifiers: public and private",22
                );
    }
     
    @Test public void testSpec11() {
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  //@ private spec_protected public behavior requires true;\n" +
                "  void m() {} }"
                ,"/A.java:2: error: illegal combination of modifiers: public and private", 37
                ,"/A.java:2: error: This JML modifier is not allowed for a specification case",15
                );
    }
     
    // FIXME - do we allow normal JML keywords in these contexts?
    
    @Test public void testQuantified() {
        helpTCF("A.java","import org.jmlspecs.annotation.*; public class A{ A(int i) {} \n" +
//                "  //@ invariant (\\exists nullable Object o; o == null); \n" +
//                "  //@ invariant (\\exists non_null Object o; o == null); \n" +
                "  //@ invariant (\\exists final Object o; o == null); \n" +
                "  //@ invariant (\\exists \\readonly Object o; o == null); \n" +
                "  //@ invariant (\\exists @Nullable Object o; o == null); \n" +
                "  //@ invariant (\\exists @Pure Object o; o == null); \n" +
                "  }"
                ,"/A.java:2: error: No Java modifiers are allowed in a quantified expression: final",26
                ,"/A.java:5: error: This JML modifier is not allowed for a quantified expression",26
                );
    }
     
    @Test public void testSetComp() {
        helpTCF("A.java","import org.jmlspecs.annotation.*; public class A{ A(int i) {} \n" +
//                "  //@ invariant null != new Object { nullable Integer i | i < 10 }; \n" +
//                "  //@ invariant null != new Object { non_null Integer i | i < 10 }; \n" +
                "  //@ invariant null != new Object { final Integer i | i < 10 }; \n" +
                "  //@ invariant null != new Object { @Nullable Integer i | i < 10 };\n" +
                "  //@ invariant null != new Object { @Pure Integer i | i < 10 };\n" +
                "  //@ invariant null != new Object { \\readonly Integer i | i < 10 }; \n" +
                "  }"
                ,"/A.java:2: error: No Java modifiers are allowed in a set comprehension expression: final",36
                ,"/A.java:4: error: This JML modifier is not allowed for a set comprehension expression",38
                );
    }
          
    @Test public void testOld() {
        helpTCF("A.java","import org.jmlspecs.annotation.*; public class A{ A(int i) {} \n" +
                "  //@ old nullable Object o1 = null; \n" +
                "  //@ old non_null Object o2 = null; \n" +
                "  //@ old readonly Object o3 = null; \n" +
                "  //@ old @Nullable Object o4 = null; \n" +
                "  //@ old @Pure Object o5 = null; \n" +
                "  //@ old pure Object o6 = null; \n" +
                "  //@ old final Object o7 = null; \n" +
                "  void m() {} }"
                ,"/A.java:6: error: This JML modifier is not allowed for a old clause declaration",11
                ,"/A.java:7: error: This JML modifier is not allowed for a old clause declaration",11
                ,"/A.java:8: error: No Java modifiers are allowed in a old clause declaration: final",11
                );
    }
     
    @Test public void testInvariant() {
        helpTCF("A.java","import org.jmlspecs.annotation.*; public class A{ A(int i) {} \n" +
                "  //@ invariant true; \n" +
                "  //@ public invariant true; \n" +
                "  //@ pure invariant true; \n" +
                "  //@ private invariant true; \n" +
                "  //@ public private invariant true; \n" +
                "  //@ non_null invariant true; \n" +
                "  //@ spec_public invariant true; \n" +
                "  void m() {} }"
                ,"/A.java:4: error: This JML modifier is not allowed for a invariant clause", 7
                ,"/A.java:6: error: illegal combination of modifiers: public and private", 22
                ,"/A.java:7: error: This JML modifier is not allowed for a invariant clause", 7
                ,"/A.java:8: error: This JML modifier is not allowed for a invariant clause", 7
                );
    }
     
    @Test public void testInvariant2() {
    	expectedExit = 1;
        helpTCF("A.java","import org.jmlspecs.annotation.*; public class A{ int m() { return 0; } \n" +
                "  //@ invariant (new A() { int m() { return 5; } }) != null; \n" +
                "  void p() {} }"
                ,"/A.java:2: error: Object allocation is not permitted in specification expressions",18
                ,"/A.java:2: warning: A non-pure method is being called where it is not permitted: A..()",18
                );
    }
     
    @Test public void testInvariant2a() {
    	expectedExit = 1;
        helpTCF("A.java","import org.jmlspecs.annotation.*; public class A{ A(int i){} int m() { return 0; } \n" +
                "  //@ invariant (new A(1) { int m() { return 5; } }) != null; \n" +
                "  void p() {} }"
                ,"/A.java:2: error: Object allocation is not permitted in specification expressions",18
                ,"/A.java:2: warning: A non-pure method is being called where it is not permitted: A..(int)",18
                );
    }
     
    @Test public void testConstraint() {
        helpTCF("A.java","import org.jmlspecs.annotation.*; public class A{ A(int i) {} \n" +
                "  //@ constraint true; \n" +
                "  //@ public constraint true; \n" +
                "  //@ pure constraint true; \n" +
                "  //@ private constraint true; \n" +
                "  //@ public private constraint true; \n" +
                "  //@ helper constraint true; \n" +
                "  //@ spec_public constraint true; \n" +
                "  void m() {} }"
                ,"/A.java:4: error: This JML modifier is not allowed for a constraint clause", 7
                ,"/A.java:6: error: illegal combination of modifiers: public and private", 22
                ,"/A.java:7: error: This JML modifier is not allowed for a constraint clause", 7
                ,"/A.java:8: error: This JML modifier is not allowed for a constraint clause", 7
                );
    }
     
    @Test public void testAxiom() {
        helpTCF("A.java","import org.jmlspecs.annotation.*; public class A{ A(int i) {} \n" +
                "  //@ axiom true; \n" +
                "  //@ public axiom true; \n" +  // ERROR
                "  //@ pure axiom true; \n" +    // ERROR
                "  //@ private axiom true; \n" + // ERROR
                "  //@ public private axiom true; \n" + // ERROR
                "  //@ non_null axiom true; \n" +       // ERROR
                "  //@ spec_public axiom true; \n" +    // ERROR
                "  void m() {} }"
                ,"/A.java:3: error: These modifiers are not allowed here: public", 14
                ,"/A.java:4: error: This JML modifier is not allowed for a axiom clause", 7
                ,"/A.java:5: error: These modifiers are not allowed here: private", 15
                ,"/A.java:6: error: These modifiers are not allowed here: public private", 22
                ,"/A.java:7: error: This JML modifier is not allowed for a axiom clause", 7
                ,"/A.java:8: error: This JML modifier is not allowed for a axiom clause", 7
                );
    }
     
    @Test public void testInitially() {
        helpTCF("A.java","import org.jmlspecs.annotation.*; public class A{ A(int i) {} \n" +
                "  //@ initially true; \n" +
                "  //@ public initially true; \n" +
                "  //@ pure initially true; \n" +
                "  //@ private initially true; \n" +
                "  //@ public private initially true; \n" +
                "  //@ non_null initially true; \n" +
                "  //@ spec_public initially true; \n" +
                "  //@ static initially true; \n" +
                "  //@ instance initially true; \n" +
                "  void m() {} }"
                ,"/A.java:4: error: This JML modifier is not allowed for a initially clause", 7
                ,"/A.java:6: error: illegal combination of modifiers: public and private", 22
                ,"/A.java:7: error: This JML modifier is not allowed for a initially clause", 7
                ,"/A.java:8: error: This JML modifier is not allowed for a initially clause", 7
                );
    }
     
    // TODO - test type parameters
    // TODO - test interaction between access and spec_public/protected
    // TODO - test instance and interaction with static
    // TODO - model methods in interfaces are not implicitly abstract and may be instance
    // TODO - non_null, nullable must have a return type
    
    // TODO - test initializers

    // FIXME
    @Test public void testBinaryMods() {
        addMockFile("$A/java/lang/Math.jml",
                "package java.lang; public final class Math {\n"
                +"//@ spec_public spec_protected\n"
                +"public int addExact(int x, int y);}");
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  boolean m() { return new Object().equals(null); } }"
                ,"/$A/java/lang/Math.jml:2: error: A declaration may not be both spec_public and spec_protected",17
                ,"/$A/java/lang/Math.jml:2: warning: There is no point to a declaration being both public and spec_protected",17
                ,"/$A/java/lang/Math.jml:2: warning: There is no point to a declaration being both public and spec_public",5
                );
    }
    
    @Test public void testBinaryModsNN() {
        addMockFile("$A/java/lang/Math.jml",
                "package java.lang; /*@ non_null */ public class Math {\n"
                +"public int addExact(int x, int y);}");
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  boolean m() {  int i = Math.addExact(5,6); } }"
                ,"/$A/java/lang/Math.jml:1: error: The type java.lang.Math in the specification matches a Java type with different modifiers: final", 43
                ,"/$A/java/lang/Math.jml:1: error: This JML modifier is not allowed for a type declaration",24
                );
    }
    
    // Checking for missing package declaration
    @Test public void testBinaryPackage1() {
        addMockFile("$A/java/lang/Math.jml",
                "public class Math {}\n");
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  boolean m() {  int i = Math.addExact(5,6); } }"
                ,"/$A/java/lang/Math.jml:1: error: Specification package does not match Java package: unnamed package vs. java.lang",2
                );
    }
    
    // Checking for incorrect package declaration
    @Test public void testBinaryPackage2() {
        addMockFile("$A/java/lang/Math.jml",
        		"  package java.utils; \n public class Math {}\n");
        helpTCF("A.java","public class A{ A(int i) {} \n" +
                "  boolean m() {  int i = Math.addExact(5,6); } }"
                ,"/$A/java/lang/Math.jml:1: error: Specification package does not match Java package: java.utils vs. java.lang",3
                );
    }
    
    @Test public void testQuery() {
        helpTCF("t/A.java","package t; import org.jmlspecs.annotation.*; \n public class A{ @Query int m() { return 0; } }"
                );
        checkMessages();
    }
     
    @Test public void testSecret() {
        helpTCF("t/A.java","package t; import org.jmlspecs.annotation.*; \n public class A{ /*@ secret model int a; */ @Secret(\"a\") int m() { return 0; } }"
                );
    }
     
    @Test public void testSecret2() {
        helpTCF("t/A.java","package t; import org.jmlspecs.annotation.*; \n public class A{ @Secret(\"x\") int m() { return 0; } //@ model secret int x;  }"
                );
    }
    
    @Test public void testAnnotations1() {
    	JmlPretty.useJmlModifier = false;
    	JmlPretty.useFullAnnotationTypeName = false;
        addMockFile("$A/A.jml","  public class A {}");
        expectedExit = 0;
        helpTCF("A.java","import org.jmlspecs.annotation.*;\n" +
                "public @Pure class A{}",
                "/A.java:2: warning: Annotations in a .java file are superseded (and ignored) by the specifications in the corresponding .jml file: @org.jmlspecs.annotation.Pure on class A", 8);
    }

    @Test
    public void testBadModifiers() {
        helpTCF("A.java","package tt; \n"
                +"/*@ nonnull_by_default*/ public class A { \n" // Purposely misspelled non_null_by_default
                                
                +"}"
                ,"/A.java:2: error: Unexpected or misspelled JML token: nonnull_by_default",5
                );
    }
    
    // FIXME - needs better error messages and better recovery
    @Test
    public void testBadModifiers2() {
        helpTCF("A.java","package tt; \n"
                +"public class A { \n"
                
                +"  //@ requires a[i]>0;\n"
                +"  public void m1bad(/*@ nonnull */ int[] a, int i) {\n" // Purposely misspelled non_null
                +"  }\n"
                
                +"}"
                ,"/A.java:4: error: Expected an identifier, found end of JML comment instead",33
                );
    }
    
    @Test
    public void testMisc() {
        helpTCF("A.java","package tt; \n"
                +"/* */ public class A { \n"
                
                +"  //@ requires a[i]>0;\n"
                +"  public void m1bad(int[] a, int i) {\n"
                +"  }\n"
                
                +"  //@ requires i >= 0 && i < a.length;\n"
                +"  //@ requires a[i]>0;\n"
                +"  public void m1good(int[] a, int i) {\n"
                +"  }\n"
                
                +"}"
                );
    }

    
    @Test public void testHelper1() {
        helpTCF("A.java","public class A{ /*@ helper */ void mzzz(){} }"
                ,"/A.java:1: error: A helper method must be private or pure: mzzz",21
                );
    }
     
    @Test public void testHelper2() {
        helpTCF("A.java","public class A{ /*@ helper protected */ void mzzz(){} }"
                ,"/A.java:1: error: A helper method must be private or pure: mzzz",21
                );
    }
     
    @Test public void testHelper3() {
        helpTCF("A.java","public class A{ /*@ helper public */ void mzzz(){} }"
                ,"/A.java:1: error: A helper method must be private or pure: mzzz",21
                );
    }
     
    @Test public void testHelper4() {
        helpTCF("A.java","public class A{ /*@ helper private */ void mzzz(){} }"
                );
    }
     
    @Test public void testHelper5() {
        helpTCF("A.java","public class A{ /*@ helper private spec_protected*/ void mzzz(){} }"
                ,"/A.java:1: error: A helper method must be private or pure: mzzz",21
                );
    }
     
    @Test public void testHelper6() {
        helpTCF("A.java","public class A{ /*@ helper private spec_public */ void m(){} }"
                ,"/A.java:1: error: A helper method must be private or pure: m",21
                );
    }
     
    

    // FIXME - also need to test this for when a .class file has a JML annotation that the spec file does not - is that tested for Java m
    // FIXME - these need implementing - error for the different in annotations
}
