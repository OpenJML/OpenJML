package org.jmlspecs.openjmltest.testcases;

import java.util.ArrayList;
import java.util.Collection;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** These tests check various improper declarations of model and ghost
 * methods and fields.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class modelghost extends TCBase {

    
    @Parameters
    static public Collection<Boolean[]> parameters() {
        Collection<Boolean[]> data = new ArrayList<>(2);
        data.add(new Boolean[]{false});
        data.add(new Boolean[]{true});
        return data;
    }
    
    public modelghost(Boolean b) {
    	useSystemSpecs = b;
    }

    
    @Test
    public void testClassSimple() {
    	helpTCF("A.java",
    			"public class A { /*@ model int m() { return B.n; } */ C mm() { return C.nn; }}\n" +
    	        "/*@ model class B { public static int n; } */\n" +
    		    "class C { public static C nn; }"
    		    );
    }
    
    @Test
    public void testClassSimple2() {
    	helpTCF("A.java",
    			"public class A { /*@ model int m() { return B.n; } */ B mm() { return B.nn; }}\n" +
    	        "/*@ model class B { public static int n; } */\n"
    		    ,"/A.java:1: error: cannot find symbol\n  symbol:   class B\n  location: class A",55
    		    ,"/A.java:1: error: cannot find symbol\n  symbol:   variable B\n  location: class A",71
    		    );
    }
    
    @Test
    public void testClassSimple3() {
    	helpTCF("A.java",
    			"public class A { /*@ model B m() { return B.n; }  */ }\n" +
    	        "/*@ model class B { public static B n; } */\n"
    		    );
    }
    
    @Test
    public void testMethod() {
        helpTCF("A.java",
                "public class A { \n" +
                "  void m() {}\n" +  // OK
                "  //@ model int m1() { return 0; }\n" + // OK
                "  /*@ model */ int m2() { return 9; }\n" + // BAD
                "  void p();\n" +  // BAD
                "  //@ model int p1();\n" +  // OK
                "  /*@ model */ int p2();\n" +  // BAD
                "  //@ int q();\n" +  // BAD
                
                "  static public class II {\n" +  // Line 9
                "  void m() {}\n" +  // OK
                "  //@ model int m1() { return 0; }\n" + // OK
                "  /*@ model */ int m2() { return 9; }\n" + // BAD
                "  void p();\n" +  // BAD
                "  //@ model int p1();\n" +  // OK
                "  /*@ model */ int p2();\n" +  // BAD
                "  //@ int q();\n" +  // BAD
                "  }\n" +
                
                "  /*@ static model public class III {\n" +  // Line 18
                "  void m() {}\n" +  // OK
                "  model int m1() { return 0; }\n" + // NO NESTING
                "  void p();\n" +  // OK - FIXME - resolve the rules about model methods and embedded model declarations
                "  model int p1();\n" +  // NO NESTING
                "  }*/\n" +
                
                "}\n" +
                
                "/*@ model class B { \n" +  // Line 25
                "  void m() {}\n" +  // OK
                "   model int m1() { return 0; }\n" + // NO NESTING
                "  void p();\n" +  // OK -- FIXME - as above
                "   model int p1();\n" +  // NO NESTING
                "}\n*/" +
                
                " class C { \n" +  // Line 31
                "  void m() {}\n" +  // OK
                "  //@ model int m1() { return 0; }\n" + // OK
                "  /*@ model */ int m2() { return 9; }\n" + // BAD
                "  void p();\n" +  // BAD
                "  //@ model int p1();\n" +  // OK
                "  /*@ model */ int p2();\n" +  // BAD
                "  //@ int q();\n" +  // BAD
                "}"
                // errors in a different order in Java 8
                ,"/A.java:4: error: A Java method declaration must not be marked either ghost or model: m2 (owner: A)",7
                ,"/A.java:7: error: A Java method declaration must not be marked either ghost or model: p2 (owner: A)",7
                ,"/A.java:12: error: A Java method declaration must not be marked either ghost or model: m2 (owner: A.II)",7
                ,"/A.java:15: error: A Java method declaration must not be marked either ghost or model: p2 (owner: A.II)",7
                ,"/A.java:34: error: A Java method declaration must not be marked either ghost or model: m2 (owner: C)",7
                ,"/A.java:37: error: A Java method declaration must not be marked either ghost or model: p2 (owner: C)",7

                ,"/A.java:5: error: missing method body, or declare abstract",8
                ,"/A.java:7: error: missing method body, or declare abstract",20
                ,"/A.java:8: error: missing method body, or declare abstract",20

                ,"/A.java:16: error: A method or type declaration within a JML annotation must be model",11
                ,"/A.java:20: error: A model type may not contain model declarations",13
                ,"/A.java:8: error: A method or type declaration within a JML annotation must be model",11
                //,"/A.java:21: error: missing method body, or declare abstract",8
                //,"/A.java:22: error: missing method body, or declare abstract",13
                ,"/A.java:22: error: A model type may not contain model declarations",13
                ,"/A.java:27: error: A model type may not contain model declarations",14
                //,"/A.java:28: error: missing method body, or declare abstract",8
                //,"/A.java:29: error: missing method body, or declare abstract",14
                ,"/A.java:29: error: A model type may not contain model declarations",14
                ,"/A.java:38: error: A method or type declaration within a JML annotation must be model",11  // FIXME - beginning of declaration?

                
                
//                ,"/A.java:8: error: A JML annotation must start with a JML keyword or have a Model or Ghost annotation: error: int",7
//                ,"/A.java:16: error: A JML annotation must start with a JML keyword or have a Model or Ghost annotation: error: int",7
//                ,"/A.java:38: error: A JML annotation must start with a JML keyword or have a Model or Ghost annotation: error: int",7
//                ,"/A.java:4: error: A Java class declaration must not be marked either ghost or model: B (owner: unnamed package)",20
//                ,"/A.java:5: error: missing method body, or declare abstract",8
//                ,"/A.java:7: error: missing method body, or declare abstract",20
//                ,"/A.java:7: error: A Java class declaration must not be marked either ghost or model: B (owner: unnamed package)",20
//                ,"/A.java:12: error: A Java class declaration must not be marked either ghost or model: B (owner: unnamed package)",20
//                ,"/A.java:13: error: missing method body, or declare abstract",8
//                ,"/A.java:15: error: missing method body, or declare abstract",20
//                ,"/A.java:15: error: A Java class declaration must not be marked either ghost or model: B (owner: unnamed package)",20
//                ,"/A.java:20: error: A model type may not contain model declarations",13
//                ,"/A.java:21: error: missing method body, or declare abstract",8
//                ,"/A.java:22: error: missing method body, or declare abstract",13
//                ,"/A.java:22: error: A model type may not contain model declarations",13
//                ,"/A.java:34: error: A Java class declaration must not be marked either ghost or model: B (owner: unnamed package)",20
//                ,"/A.java:35: error: missing method body, or declare abstract",8
//                ,"/A.java:37: error: missing method body, or declare abstract",20
//                ,"/A.java:37: error: A Java class declaration must not be marked either ghost or model: B (owner: unnamed package)",20
//                ,"/A.java:27: error: A model type may not contain model declarations",14
//                ,"/A.java:28: error: missing method body, or declare abstract",8
//                ,"/A.java:29: error: missing method body, or declare abstract",14
//                ,"/A.java:29: error: A model type may not contain model declarations",14
                );
    }
    
    @Test
    public void testUseMethod() {
        helpTCF("A.java",
                "public class A { \n" +
                "  /*@ pure */ boolean m() {}\n" +  // OK
                "  //@ model pure boolean m1() { return true; }\n" + // OK
                
                "  //@ invariant m() && m1();\n" +
                
                "  //@ requires m() && m1();\n" +
                "  void p() {} ;\n" +
                
                "  //@ requires m() && m1();\n" + // BAD - VISIBILITY PROBLEMS
                "  public void pp() {} ;\n" +
                
                "}\n"
                ,"/A.java:7: error: An identifier with package visibility may not be used in a requires clause with public visibility",16
                ,"/A.java:7: error: An identifier with package visibility may not be used in a requires clause with public visibility",23
                );
        
    }

    @Test
    public void testUseMethod2() {
        helpTCF("A.java",
                "public class A { \n" +
                
                "  //@ requires B.m() && B.m1();\n" +
                "  static void p() {};\n" +
                
                "  //@ requires B.m() && B.m1();\n" + // BAD - VISIBILITY PROBLEMS
                "  public static void pp() {} ;\n" +
                
                "}\n" +
                "class B { \n" +
                "  static /*@ pure */ boolean m() {}\n" +  // OK
                "  //@ model pure static boolean m1() { return true; }\n" + // OK
                
                "  //@ static invariant m() && m1();\n" +
                
                "}\n"
                ,"/A.java:4: error: An identifier with package visibility may not be used in a requires clause with public visibility",17
                ,"/A.java:4: error: An identifier with package visibility may not be used in a requires clause with public visibility",26
                );
        
    }

    @Test
    public void testUseJML() {
    	if (!useSystemSpecs) return; // Irrelevant if useSystemSpecs is false
        helpTCF("A.java",
                "import org.jmlspecs.lang.JML; public class A { \n" +
                
                "  //@ requires JML.erasure(\\typeof(this)) == JML.erasure(\\type(A));\n" +
                "  void p() {};\n" +
                
                "}\n"
                );
        
    }

    @Test
    public void testClass() {
        helpTCF("A.java",
                "public class A { \n" +
                "  //@ model static public class B{}\n" +
                "  /*@ model */ static public class C{}\n" +  // NOT MODEL
                "  //@ static public class D{}\n" + // SHOULD BE MODEL
                "  public class AA { \n" +
                "    //@ model  public class B{}\n" +
                "    /*@ model */  public class C{}\n" +  // NOT MODEL
                "    //@  public class D{}\n" +  // SHOULD BE MODEL
                "  }\n" +
                "  /*@ model public class M { \n" +                  // Line 10
                "    model  public class B{}\n" +  // NO POINT
                "     public class C{}\n" +
                "  }*/\n" +
                "}\n" +

                "/*@ model */ class Y { \n" + // BAD
                "}\n" +

                "/*@ model class Q { \n" +
                "  model  public class C{}\n" + // NO POINT
                "   public class D{}\n" + 
                "}*/\n" +                                       // Line 20

                "class Z { \n" +
                "  //@ model  public class B{}\n" +
                "  /*@ model */  public class C{}\n" + // BAD
                "  //@  public class D{}\n" + // BAD
                "}\n"
                // Java 8
                ,"/A.java:3: error: A Java class declaration must not be marked either ghost or model: C (owner: A)",7
                ,"/A.java:4: error: A JML class declaration must be marked either ghost or model: D (owner: A)", 21
                ,"/A.java:7: error: A Java class declaration must not be marked either ghost or model: C (owner: A.AA)",9
                ,"/A.java:8: error: A JML class declaration must be marked either ghost or model: D (owner: A.AA)", 17
                ,"/A.java:11: error: A model type may not contain model declarations: B in A.M",19
                ,"/A.java:15: error: A Java class declaration must not be marked either ghost or model: Y (owner: unnamed package)",5
                ,"/A.java:18: error: A model type may not contain model declarations: C in Q",17
                ,"/A.java:23: error: A Java class declaration must not be marked either ghost or model: C (owner: Z)",7
                ,"/A.java:24: error: A JML class declaration must be marked either ghost or model: D (owner: Z)", 15
                // Java 7
//                ,"/A.java:4: error: A JML annotation must start with a JML keyword or have a Model or Ghost annotation: error: class",21
//                ,"/A.java:8: error: A JML annotation must start with a JML keyword or have a Model or Ghost annotation: error: class",17
//                ,"/A.java:24: error: A JML annotation must start with a JML keyword or have a Model or Ghost annotation: error: class",15
//                ,"/A.java:3: error: A Java class declaration must not be marked either ghost or model: B (owner: unnamed package)",30
//                ,"/A.java:7: error: A Java class declaration must not be marked either ghost or model: B (owner: unnamed package)",26
//                ,"/A.java:11: error: A model type may not contain model declarations",19
//                ,"/A.java:15: error: A Java class declaration must not be marked either ghost or model: B (owner: unnamed package)",14
//                ,"/A.java:23: error: A Java class declaration must not be marked either ghost or model: B (owner: unnamed package)",24
//                ,"/A.java:18: error: A model type may not contain model declarations",17

        );
                
    }
    
    @Test
    public void testField() {
        helpTCF("A.java",
                "public class A { \n" +
                "  int m;\n" +  // OK
                "  //@ model int m1;\n" + // OK
                "  //@ ghost int m1a;\n" + // OK
                "  /*@ model */ int m2;\n" + // BAD
                "  /*@ ghost */ int m2a;\n" + // BAD
                "  //@ int q;\n" +  // BAD
                
                "  static public class II {\n" +  // Line 8
                "  int m;\n" +  // OK
                "  //@ model int m1;\n" + // OK
                "  //@ ghost int m1a;\n" + // OK
                "  /*@ model */ int m2;\n" + // BAD
                "  /*@ ghost */ int m2a;\n" + // BAD
                "  //@ int q;\n" +  // BAD
                "  }\n" +
                
                "  /*@ static model public class III {\n" +  // Line 16
                "    int m;\n" +  // OK
                "    model int m1;\n" + // NO NESTING
                "    ghost int m1a;\n" + // NO NESTING
                "    \n" +  
                "  }*/\n" +
                
                "}\n" +
                
                "/*@ model class B { \n" +  // Line 23
                "  int m;\n" +  // OK
                "   model int m1; ghost int m2; \n" + // NO NESTING
                "}\n*/" +
                
                " class C { \n" +  // Line 31
                "  int m;\n" +  // OK
                "  //@ model int m1;\n" + // OK
                "  //@ ghost int m1a;\n" + // OK
                "  /*@ model */ int m2;\n" + // BAD
                "  /*@ ghost */ int m2a;\n" + // BAD
                "  //@ int q;\n" +  // BAD
                "}"
                // Order changed for Java8
                ,"/A.java:5: error: A Java field declaration must not be marked either ghost or model: m2 (owner: A)",7
                ,"/A.java:6: error: A Java field declaration must not be marked either ghost or model: m2a (owner: A)",7
                ,"/A.java:7: error: A declaration within a JML annotation must be either ghost or model",11
                ,"/A.java:12: error: A Java field declaration must not be marked either ghost or model: m2 (owner: A.II)",7
                ,"/A.java:13: error: A Java field declaration must not be marked either ghost or model: m2a (owner: A.II)",7
                ,"/A.java:14: error: A declaration within a JML annotation must be either ghost or model",11
                ,"/A.java:18: error: A model type may not contain model declarations",15
                ,"/A.java:19: error: A model type may not contain ghost declarations",15
                ,"/A.java:25: error: A model type may not contain model declarations",14
                ,"/A.java:25: error: A model type may not contain ghost declarations",28
                ,"/A.java:31: error: A Java field declaration must not be marked either ghost or model: B (owner: unnamed package)",20
                ,"/A.java:32: error: A Java field declaration must not be marked either ghost or model: B (owner: unnamed package)",20
                ,"/A.java:33: error: A declaration within a JML annotation must be either ghost or model",11 // FIXME - beginning of declaration?
                
                
                
//                ,"/A.java:7: error: A JML annotation must start with a JML keyword or have a Model or Ghost annotation: error: int",7
//                ,"/A.java:14: error: A JML annotation must start with a JML keyword or have a Model or Ghost annotation: error: int",7
//                ,"/A.java:33: error: A JML annotation must start with a JML keyword or have a Model or Ghost annotation: error: int",7
//                ,"/A.java:5: error: A Java class declaration must not be marked either ghost or model: C (owner: unnamed package)",20
//                ,"/A.java:6: error: A Java class declaration must not be marked either ghost or model: C (owner: unnamed package)",20
//                ,"/A.java:12: error: A Java class declaration must not be marked either ghost or model: C (owner: unnamed package)",20
//                ,"/A.java:13: error: A Java class declaration must not be marked either ghost or model: C (owner: unnamed package)",20
//                ,"/A.java:18: error: A model type may not contain model declarations",15
//                ,"/A.java:19: error: A model type may not contain ghost declarations",15
//                ,"/A.java:31: error: A Java class declaration must not be marked either ghost or model: C (owner: unnamed package)",20
//                ,"/A.java:32: error: A Java class declaration must not be marked either ghost or model: C (owner: unnamed package)",20
//                ,"/A.java:25: error: A model type may not contain model declarations",14
//                ,"/A.java:25: error: A model type may not contain ghost declarations",28
                );
    }
    
    @Test
    public void testInitializer() {
        addMockFile("$A/A.jml","public class A { { i = 2; } }");
        helpTCF("A.java","public class A { int i; { i = 1; } } "
                ,"/$A/A.jml:1: error: Initializer blocks are not allowed in specifications",18
        );
    }

    @Test
    public void testInitializer2() {
        addMockFile("$A/A.jml","public class A { } /*@ model  class B { int i;   } */ ");
        helpTCF("A.java","public class A { int i; { i = 1; } } "
        );
    }

    @Test
    public void testInitializer2a() {
        addMockFile("$A/A.jml","public class A { } /*@ model public class B { int i;   } */ ");
        helpTCF("A.java","public class A { int i; { i = 1; } } "
        		,"/$A/A.jml:1: error: class B is public, should be declared in a file named B.java",37
        );
    }

    @Test
    public void testInitializer3() {
        addMockFile("$A/A.jml","public class A { } /*@ model  class B { int i;  { i = 2; } } */ ");
        helpTCF("A.java","public class A { int i; { i = 1; } } "
        		,"/$A/A.jml:1: error: Initializer blocks are not allowed in specifications",49
        );
    }

    @Test
    public void testPackage() {
        addMockFile("$A/A.jml","package p; public class A { /*@ model public class B { int i;  { i = 2; } } */ }");
        helpTCF("A.java","package p; public class A { int i; { i = 1; } } "
        );
    }

    @Test
    public void testPackage2() {
        addMockFile("$A/A.jml","package pp; public class A { /*@ model public class B { int i;  { i = 2; } } */ }");
        helpTCF("A.java","package p; public class A { int i; { i = 1; } } "
        );
    }

    @Test public void testInterface() {
        helpTCF("TestJava.java","package tt; \n"
                +"public interface TestJava { \n"

                +"  //@ public model instance int z;\n"
                +"  //@ static model int z2;\n"
                +"  public static int zz = 0;\n"
                +"}"
                );
    }
        
     
}
