package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.*;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

import com.sun.tools.javac.util.Options;

// Tests the rules about which specification cases are enforced by a method's implementation

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escvisibility extends EscBase {

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        addOptions("-no-purityCheck");
        String z = java.io.File.pathSeparator;
        String testspecpath = "$A"+z+"$B";
        Options.instance(context).put("--class-path",   testspecpath);
        Options.instance(context).put("--source-path",   testspecpath);
        addOptions("-specspath",   testspecpath);
        addOptions("-quiet");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
        addOptions("-jmltesting");
    }

    // Invariant inherited from same package
    
    @Test
    public void testPrivate() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  private boolean b = false; public boolean bb = true;\n"
                +"  //@ private invariant b; \n"
                +"  //@ ensures bb;\n"
                +"  public void change() { b = false; }"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  public void m1() throws Exception {\n"
                +"      change();\n"
                +"  }\n"
                
                +"}"
                );
    }
    
    @Test
    public void testPublic() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  public boolean b = true;\n"
                +"  //@ public invariant b; \n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  public void m1() throws Exception {\n"
                +"      b = false;\n"
                +"  }\n"
                
                +"}"
                
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (InvariantExit) in method m1",15
                ,"/tt/TestJava.java:4: warning: Associated declaration",14
                );
    }
    
    @Test
    public void testProtected() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  protected boolean b = true;\n"
                +"  //@ protected invariant b; \n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  public void m1() throws Exception {\n"
                +"      b = false;\n"
                +"  }\n"
                
                +"}"
                
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (InvariantExit) in method m1",15
                ,"/tt/TestJava.java:4: warning: Associated declaration",17
                );
    }
    
    @Test
    public void testPackage() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  boolean b = true;\n"
                +"  //@ invariant b; \n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  public void m1() throws Exception {\n"
                +"      b = false;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (InvariantExit) in method m1",15
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }
    
    // Invariant in same class
    
    @Test
    public void testPrivate2() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  private boolean b = true;\n"
                +"  //@ private invariant b; \n"
                +"  public void m1() {\n"
                +"      b = false;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (InvariantExit) in method m1",15
                ,"/tt/TestJava.java:6: warning: Associated declaration",15
                );
    }
    
    @Test
    public void testPublic2() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  public boolean b = true;\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  //@ public invariant b; \n"
                +"  public void m1() {\n"
                +"      b = false;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (InvariantExit) in method m1",15
                ,"/tt/TestJava.java:6: warning: Associated declaration",14
                );
    }
    
    @Test
    public void testProtected2() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  protected boolean b = true;\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  //@ protected invariant b; \n"
                +"  public void m1() {\n"
                +"      b = false;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (InvariantExit) in method m1",15
                ,"/tt/TestJava.java:6: warning: Associated declaration",17
                );
    }
    
    @Test
    public void testPackage2() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  boolean b = true;\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  //@ invariant b; \n"
                +"  public void m1() {\n"
                +"      b = false;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (InvariantExit) in method m1",15
                ,"/tt/TestJava.java:6: warning: Associated declaration",7
                );
    }
    
    // Inherited method spec in same package
    
    @Test
    public void testPrivate3() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  //@ private normal_behavior ensures false;\n"
                +"  public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                );
    }
    
    @Test
    public void testPublic3() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  //@ public normal_behavior ensures false;\n"
                +"  public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:3: warning: Associated declaration",30
                );
    }
    
    @Test
    public void testProtected3() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  //@ protected normal_behavior ensures false;\n"
                +"  public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:3: warning: Associated declaration",33
                );
    }
    
    @Test
    public void testPackage3() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  //@ normal_behavior ensures false;\n"
                +"  public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:3: warning: Associated declaration",23
                );
    }
    
    // Inherited lightweight method spec in same package
    
    @Test
    public void testPrivate3a() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  //@   ensures false;\n"
                +"  private void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                );
    }
    
    @Test
    public void testPublic3a() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  //@  ensures false;\n"
                +"  public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:3: warning: Associated declaration",8
                );
    }
    
    @Test
    public void testProtected3a() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  //@  ensures false;\n"
                +"  protected void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:3: warning: Associated declaration",8
                );
    }
    
    @Test
    public void testPackage3a() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  //@  ensures false;\n"
                +"  void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:3: warning: Associated declaration",8
                );
    }
    
    // Inherited method spec in same class
    
    @Test
    public void testPrivate4() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  //@ also private normal_behavior ensures false;\n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:7: warning: Associated declaration",36
                );
    }
    
    @Test
    public void testPublic4() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  //@ also public normal_behavior ensures false;\n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:7: warning: Associated declaration",35
                );
    }
    
    @Test
    public void testProtected4() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  //@ also protected normal_behavior ensures false;\n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:7: warning: Associated declaration",38
                );
    }
    
    @Test
    public void testPackage4() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  //@ also normal_behavior ensures false;\n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:7: warning: Associated declaration",28
                );
    }
    
    // Inherited method specs from a different package
    
    @Test
    public void testPrivate5() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX2("tt.TestJava","package tt; \n"
                +"public class TestJava extends tx.Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}",
                
                "tx.Parent","package tx; public class Parent {\n"
                        +"  //@ private normal_behavior ensures false;\n"
                        +"  public void m1() {\n"
                        +"  }\n"
                        +"}"
                        
                );
    }
    
    @Test
    public void testPublic5() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX2("tt.TestJava","package tt; \n"
                +"public class TestJava extends tx.Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}",
                
                "tx.Parent","package tx; public class Parent {\n"
                        +"  //@ public normal_behavior ensures false;\n"
                        +"  public void m1() {\n"
                        +"  }\n"
                        +"}"
                        
                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tx/Parent.java:2: warning: Associated declaration",30
                );
    }
    
    @Test
    public void testProtected5() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX2("tt.TestJava","package tt; \n"
                +"public class TestJava extends tx.Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}",
                
                "tx.Parent","package tx; public class Parent {\n"
                        +"  //@ protected normal_behavior ensures false;\n"
                        +"  public void m1() {\n"
                        +"  }\n"
                        +"}"
                        
                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tx/Parent.java:2: warning: Associated declaration",33
                );
    }
    
    @Test
    public void testPackage5() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX2("tt.TestJava","package tt; \n"
                +"public class TestJava extends tx.Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}",
                
                "tx.Parent","package tx; public class Parent {\n"
                        +"  //@ normal_behavior ensures false;\n"
                        +"  public void m1() {\n"
                        +"  }\n"
                        +"}"
                        
                );
    }
    

    // Inherited lightweight method specs from a different package
    
    @Test
    public void testPrivate6() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX2("tt.TestJava","package tt; \n"
                +"public class TestJava extends tx.Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}",
                
                "tx.Parent","package tx; public class Parent {\n"
                        +"  //@  ensures false;\n"
                        +"  private void m1() {\n"
                        +"  }\n"
                        +"}"
                        
                );
    }
    
    @Test
    public void testPublic6() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX2("tt.TestJava","package tt; \n"
                +"public class TestJava extends tx.Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}",
                
                "tx.Parent","package tx; public class Parent {\n"
                        +"  //@  ensures false;\n"
                        +"  public void m1() {\n"
                        +"  }\n"
                        +"}"
                        
                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tx/Parent.java:2: warning: Associated declaration",8
                );
    }
    
    @Test
    public void testProtected6() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX2("tt.TestJava","package tt; \n"
                +"public class TestJava extends tx.Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}",
                
                "tx.Parent","package tx; public class Parent {\n"
                        +"  //@  ensures false;\n"
                        +"  protected void m1() {\n"
                        +"  }\n"
                        +"}"
                        
                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tx/Parent.java:2: warning: Associated declaration",8
                );
    }
    
    @Test
    public void testPackage6() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX2("tt.TestJava","package tt; \n"
                +"public class TestJava extends tx.Parent { \n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}",
                
                "tx.Parent","package tx; public class Parent {\n"
                        +"  //@  ensures false;\n"
                        +"  void m1() {\n"
                        +"  }\n"
                        +"}"
                        
                );
    }
    

    // Not-inherited method spec
    
    
    @Test
    public void testPublic7() {
        addOptions("-method", "tt.TestJava.m1");
        String s2 = "package tx; public class B {\n"
                +"  //@  requires false;\n"
                +"  static public void m1() {\n"
                +"  }\n"
                +"}"
                ;
                        
        helpTCX2("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1() {\n"
                +"     tx.B.m1();"
                +"  }\n"
                
                +"}"
                , "tx.B", s2
                
                        
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method m1",13
                ,"/tx/B.java:3: warning: Associated declaration",22
                ,"/tx/B.java:2: warning: Precondition conjunct is false: false",17
                );
    }
    
    
    @Test
    public void testPrivate8() {
    	expectedExit = 1;
        addOptions("-method", "tt.TestJava.m1");
        String s2 = "package tx; public class B {\n"
                +"  //@ private normal_behavior\n"
                +"  //@  requires false;\n"
                +"  static public void m1() {\n"
                +"  }\n"
                +"}"
                ;
                        
        helpTCX2("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1() {\n"
                +"     tx.B.m1();"
                +"  }\n"
                +"}"
                ,"tx.B",s2
                ,"/tt/TestJava.java:4: warning: No visible specifications for this call site: tx.B.m1() called from tt.TestJava.m1()",13
                );
    }
    
    @Test
    public void testPublic8() {
        addOptions("-method", "tt.TestJava.m1");
        String s2 = "package tx; public class B {\n"
                +"  //@ public normal_behavior\n"
                +"  //@  requires false;\n"
                +"  static public void m1() {\n"
                +"  }\n"
                +"}"
                ;
                        
        helpTCX2("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1() {\n"
                +"     tx.B.m1();"
                +"  }\n"
                +"}"
                ,"tx.B,s2"
                        
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method m1",13
                ,"/tx/B.java:4: warning: Associated declaration",22
                ,"/tx/B.java:3: warning: Precondition conjunct is false: false",17
                );
    }
    
    
    @Test
    public void testProtected8() {
    	expectedExit = 0;
        addOptions("-method", "tt.TestJava.m1");
        String s2 = "package tx; public class B {\n"
                +"  //@ protected normal_behavior\n"
                +"  //@  requires false;\n"
                +"  static public void m1() {\n"
                +"  }\n"
                +"}"
                ;
                        
        helpTCX2("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1() {\n"
                +"     tx.B.m1();"
                +"  }\n"
                +"}"
                ,"tx.B",s2
                ,"/tt/TestJava.java:4: warning: No visible specifications for this call site: tx.B.m1() called from tt.TestJava.m1()",13
                );
    }
        
    @Test
    public void testPackage8() {
    	expectedExit = 0;
        addOptions("-method", "tt.TestJava.m1");
        String s2 = "package tx; public class B {\n"
                +"  //@ normal_behavior\n"
                +"  //@  requires false;\n"
                +"  static public void m1() {\n"
                +"  }\n"
                +"}"
                ;

        helpTCX2("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1() {\n"
                +"     tx.B.m1();"
                +"  }\n"
                +"}"
                ,"tx.B", s2
                ,"/tt/TestJava.java:4: warning: No visible specifications for this call site: tx.B.m1() called from tt.TestJava.m1()",13
                );
    }


    @Test
    public void testPrivate9() {
    	expectedExit = 0;
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  //@ private normal_behavior\n"
                +"  //@  requires false;\n"
                +"  static public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava { \n"
                +"  public void m1() {\n"
                +"      B.m1();"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: No visible specifications for this call site: tt.B.m1() called from tt.TestJava.m1()",11
                );
    }
    
    @Test
    public void testPublic9() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  //@ public normal_behavior\n"
                +"  //@  requires false;\n"
                +"  static public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava { \n"
                +"  public void m1() {\n"
                +"      B.m1();"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Precondition) in method m1",11
                ,"/tt/TestJava.java:5: warning: Associated declaration",22
                ,"/tt/TestJava.java:4: warning: Precondition conjunct is false: false",17
                );
    }
    
    @Test
    public void testProtected9() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  //@ protected normal_behavior\n"
                +"  //@  requires false;\n"
                +"  static public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava { \n"
                +"  public void m1() {\n"
                +"      B.m1();"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Precondition) in method m1",11
                ,"/tt/TestJava.java:5: warning: Associated declaration",22
                ,"/tt/TestJava.java:4: warning: Precondition conjunct is false: false",17
                );
    }
    
    @Test
    public void testPackage9() {
        addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  //@ normal_behavior\n"
                +"  //@  requires false;\n"
                +"  static public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava { \n"
                +"  public void m1() {\n"
                +"      B.m1();"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Precondition) in method m1",11
                ,"/tt/TestJava.java:5: warning: Associated declaration",22
                ,"/tt/TestJava.java:4: warning: Precondition conjunct is false: false",17
                );
    }

}
