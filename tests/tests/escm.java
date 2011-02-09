package tests;

import org.jmlspecs.openjml.esc.JmlEsc;

import com.sun.tools.javac.util.Options;

public class escm extends EscBase {

    protected void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        options.put("-noPurityCheck","");
//        options.put("-jmlverbose",   "");
//        options.put("-showbb","");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //options.put("-trace",   "");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
    }
    
    /** This test checks that nested, local and anonymous classes are handled */
    public void testNestedClass() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m1(TestJava o) {\n"
                +"       class C { void m() { /*@ assert false; */ }};\n"
                +"       C x;\n"
                +"       C y = new C() { void m() {/*@ assert false; */}};\n"
                +"       //@ assert false;\n"
                +"  }\n"
                
                +"  public static class A {\n"
                +"     public void m2() {\n"
                +"       //@ assert false;\n"
                +"     }\n"
                +"  }\n"
                

                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",33
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m",38
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method m1",12
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method m2",12
                
                );
    }
   
    /** This test checks that the specs of methods in nested, local and anonymous classes are used */
    public void testNestedMethodSpecs() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m1(TestJava o) {\n"
                +"       class C { /*@ ensures false; */ void m() {  }};\n"
                +"       C x;\n"
                +"       class D { void m() {  }};\n" // Line 10
                +"       D y = new D() { /*@ ensures false; */ void m() {}};\n"
                +"       class E { /*@ ensures false; */void m() {  }};\n"
                +"       E z = new E() {  void m() {}};\n"
                +"  }\n"
                
                +"  public static class A {\n"
                +"       //@ ensures false;\n"
                +"     public void m2() {\n"
                +"     }\n"
                +"  }\n"
                

                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m",45
                ,"/tt/TestJava.java:8: warning: Associated declaration",30
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Postcondition) in method m",51
                ,"/tt/TestJava.java:11: warning: Associated declaration",36
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Postcondition) in method m",44
                ,"/tt/TestJava.java:12: warning: Associated declaration",30
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Postcondition) in method m",30
                ,"/tt/TestJava.java:12: warning: Associated declaration",30
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Postcondition) in method m2",18
                ,"/tt/TestJava.java:16: warning: Associated declaration",20
                
                );
    }
   
    /** This test checks that the specs of nested, local and anonymous classes are used */
    public void testNestedClassSpecs() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m1(TestJava o) {\n"
                +"       class C {  \n"
                +"           //@ invariant false;\n" 
                +"           void m() {  }};\n"  // Line 10
                +"       C x;\n"
                +"       class D { void m() {  }};\n"
                +"       D y = new D() { /*@ invariant false;*/ void m() {}};\n"
                +"       class E { /*@ invariant false;*/void m() {  }};\n"
                +"       E z = new E() {  void m() {}};\n"
                +"  }\n"
                
                +"  public static class A {\n"
                +"     //@ invariant false;\n"
                +"     public void m2() {\n"
                +"     }\n"
                +"  }\n"
                

                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Invariant) in method <init>",8
                ,"/tt/TestJava.java:9: warning: Associated declaration",26
                ,"/tt/TestJava.java:10: warning: Invariants+Preconditions appear to be contradictory in method m()",17
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Invariant) in method <init>",22
                ,"/tt/TestJava.java:13: warning: Associated declaration",38
                ,"/tt/TestJava.java:13: warning: Invariants+Preconditions appear to be contradictory in method m()",52
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Invariant) in method <init>",8
                ,"/tt/TestJava.java:14: warning: Associated declaration",32
                ,"/tt/TestJava.java:14: warning: Invariants+Preconditions appear to be contradictory in method m()",45
                ,"/tt/TestJava.java:15: warning: Invariants+Preconditions appear to be contradictory in method m()",30
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Invariant) in method <init>",17
                ,"/tt/TestJava.java:18: warning: Associated declaration",20
                ,"/tt/TestJava.java:19: warning: Invariants+Preconditions appear to be contradictory in method m2()",18

                );
    }
   

}