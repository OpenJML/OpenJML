package tests;

import org.junit.Test;

/** These tests check various improper declarations of model and ghost
 * methods and fields.
 * @author David R. Cok
 *
 */
public class modelghost extends TCBase {


    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
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
                "  void p();\n" +  // BAD
                "  model int p1();\n" +  // NO NESTING
                "  }*/\n" +
                
                "}\n" +
                
                "/*@ model class B { \n" +  // Line 25
                "  void m() {}\n" +  // OK
                "   model int m1() { return 0; }\n" + // NO NESTING
                "  void p();\n" +  // BAD
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
                ,"/A.java:4: A Java declaration (not within a JML annotation) may not be either ghost or model",20
                ,"/A.java:5: missing method body, or declare abstract",8
                ,"/A.java:7: missing method body, or declare abstract",20
                ,"/A.java:7: A Java declaration (not within a JML annotation) may not be either ghost or model",20
                ,"/A.java:12: A Java declaration (not within a JML annotation) may not be either ghost or model",20
                ,"/A.java:13: missing method body, or declare abstract",8
                ,"/A.java:15: missing method body, or declare abstract",20
                ,"/A.java:15: A Java declaration (not within a JML annotation) may not be either ghost or model",20
                ,"/A.java:16: A method or type declaration within a JML annotation must be model",11
                ,"/A.java:8: A method or type declaration within a JML annotation must be model",11
                ,"/A.java:20: A model type may not contain model declarations",13
                ,"/A.java:21: missing method body, or declare abstract",8
                ,"/A.java:22: missing method body, or declare abstract",13
                ,"/A.java:22: A model type may not contain model declarations",13
                ,"/A.java:34: A Java declaration (not within a JML annotation) may not be either ghost or model",20
                ,"/A.java:35: missing method body, or declare abstract",8
                ,"/A.java:37: missing method body, or declare abstract",20
                ,"/A.java:37: A Java declaration (not within a JML annotation) may not be either ghost or model",20
                ,"/A.java:38: A method or type declaration within a JML annotation must be model",11
                ,"/A.java:27: A model type may not contain model declarations",14
                ,"/A.java:28: missing method body, or declare abstract",8
                ,"/A.java:29: missing method body, or declare abstract",14
                ,"/A.java:29: A model type may not contain model declarations",14
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
                ,"/A.java:3: A Java declaration (not within a JML annotation) may not be either ghost or model",30
                ,"/A.java:7: A Java declaration (not within a JML annotation) may not be either ghost or model",26
                ,"/A.java:8: A method or type declaration within a JML annotation must be model",17
                ,"/A.java:4: A method or type declaration within a JML annotation must be model",21
                ,"/A.java:11: A model type may not contain model declarations",19
                ,"/A.java:15: A Java declaration (not within a JML annotation) may not be either ghost or model",14
                ,"/A.java:23: A Java declaration (not within a JML annotation) may not be either ghost or model",24
                ,"/A.java:24: A method or type declaration within a JML annotation must be model",15
                ,"/A.java:18: A model type may not contain model declarations",17

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
                ,"/A.java:5: A Java declaration (not within a JML annotation) may not be either ghost or model",20
                ,"/A.java:6: A Java declaration (not within a JML annotation) may not be either ghost or model",20
                ,"/A.java:12: A Java declaration (not within a JML annotation) may not be either ghost or model",20
                ,"/A.java:13: A Java declaration (not within a JML annotation) may not be either ghost or model",20
                ,"/A.java:14: A declaration within a JML annotation must be either ghost or model",11
                ,"/A.java:7: A declaration within a JML annotation must be either ghost or model",11
                ,"/A.java:18: A model type may not contain model declarations",15
                ,"/A.java:19: A model type may not contain ghost declarations",15
                ,"/A.java:31: A Java declaration (not within a JML annotation) may not be either ghost or model",20
                ,"/A.java:32: A Java declaration (not within a JML annotation) may not be either ghost or model",20
                ,"/A.java:33: A declaration within a JML annotation must be either ghost or model",11
                ,"/A.java:25: A model type may not contain model declarations",14
                ,"/A.java:25: A model type may not contain ghost declarations",28
                );
    }
    
    @Test
    public void testInitializer() {
        addMockFile("$A/A.jml","public class A { { i = 2; } }");
        helpTCF("A.java","public class A { int i; { i = 1; } } "
                ,"/$A/A.jml:1: Initializer blocks are not allowed in specifications",18
        );
    }

    @Test
    public void testInitializer2() {
        addMockFile("$A/A.jml","public class A { /*@ model public class B { int i;  { i = 2; } } */ }");
        helpTCF("A.java","public class A { int i; { i = 1; } } "
        );
    }

    @Test public void testInterface() {
        helpTCF("TestJava.java","package tt; \n"
                +"public interface TestJava { \n"

                +"  //@ public model int z;\n"
                +"  //@ static model int z2;\n"
                +"  public static int zz = 0;\n"
                +"}"
                );
    }
        
     
}
