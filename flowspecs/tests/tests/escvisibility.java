package tests;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

// Tests the rules about which specification cases are enforced by a method's implementation

@RunWith(Parameterized.class)
public class escvisibility extends EscBase {

    public escvisibility(String option, String solver) {
        super(option, solver);
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        main.addOptions("-no-purityCheck");
        String z = java.io.File.pathSeparator;
        String testspecpath = "$A"+z+"$B";
        main.addOptions("-classpath",   testspecpath);
        main.addOptions("-sourcepath",   testspecpath);
        main.addOptions("-specspath",   testspecpath);
        main.addOptions("-quiet");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
        main.addOptions("-jmltesting");
    }

    // Invariant inherited from same package
    
    @Test
    public void testPrivate() {
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  //@ private normal_behavior ensures false;\n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:7: warning: Associated declaration",31
                );
    }
    
    @Test
    public void testPublic4() {
        main.addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  //@ public normal_behavior ensures false;\n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:7: warning: Associated declaration",30
                );
    }
    
    @Test
    public void testProtected4() {
        main.addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  //@ protected normal_behavior ensures false;\n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:7: warning: Associated declaration",33
                );
    }
    
    @Test
    public void testPackage4() {
        main.addOptions("-method", "tt.TestJava.m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"class Parent { \n"
                
                +"  public void m1() {\n"
                +"  }\n"
                +"}\n"
                
                +"public class TestJava extends Parent { \n"
                +"  //@ normal_behavior ensures false;\n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:7: warning: Associated declaration",23
                );
    }
    
    // Inherited method specs from a different package
    
    @Test
    public void testPrivate5() {
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
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
        main.addOptions("-method", "tt.TestJava.m1");
        addMockJavaFile("tx/B.java","package tx; public class B {\n"
                +"  //@  requires false;\n"
                +"  static public void m1() {\n"
                +"  }\n"
                +"}"
                );
                        
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1() {\n"
                +"     tx.B.m1();"
                +"  }\n"
                
                +"}"
                
                        
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method m1",13
                ,"/tx/B.java:2: warning: Associated declaration",8
                );
    }
    
    
    @Test
    public void testPrivate8() {
        main.addOptions("-method", "tt.TestJava.m1");
        addMockJavaFile("tx/B.java","package tx; public class B {\n"
                +"  //@ private normal_behavior\n"
                +"  //@  requires false;\n"
                +"  static public void m1() {\n"
                +"  }\n"
                +"}"
                );
                        
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1() {\n"
                +"     tx.B.m1();"
                +"  }\n"
                
                +"}"
                
                );
    }
    
    @Test
    public void testPublic8() {
        main.addOptions("-method", "tt.TestJava.m1");
        addMockJavaFile("tx/B.java","package tx; public class B {\n"
                +"  //@ public normal_behavior\n"
                +"  //@  requires false;\n"
                +"  static public void m1() {\n"
                +"  }\n"
                +"}"
                );
                        
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1() {\n"
                +"     tx.B.m1();"
                +"  }\n"
                
                +"}"
                
                        
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method m1",13
                ,"/tx/B.java:3: warning: Associated declaration",8
                );
    }
    
    
    @Test
    public void testProtected8() {
        main.addOptions("-method", "tt.TestJava.m1");
        addMockJavaFile("tx/B.java","package tx; public class B {\n"
                +"  //@ protected normal_behavior\n"
                +"  //@  requires false;\n"
                +"  static public void m1() {\n"
                +"  }\n"
                +"}"
                );
                        
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1() {\n"
                +"     tx.B.m1();"
                +"  }\n"
                
                +"}"
                
                );
    }
        
    @Test
    public void testPackage8() {
        main.addOptions("-method", "tt.TestJava.m1");
        addMockJavaFile("tx/B.java","package tx; public class B {\n"
                +"  //@ normal_behavior\n"
                +"  //@  requires false;\n"
                +"  static public void m1() {\n"
                +"  }\n"
                +"}"
                );

        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1() {\n"
                +"     tx.B.m1();"
                +"  }\n"

                    +"}"

                );
    }


    @Test
    public void testPrivate9() {
        main.addOptions("-method", "tt.TestJava.m1");
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
                );
    }
    
    @Test
    public void testPublic9() {
        main.addOptions("-method", "tt.TestJava.m1");
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
                ,"/tt/TestJava.java:4: warning: Associated declaration",8
                );
    }
    
    @Test
    public void testProtected9() {
        main.addOptions("-method", "tt.TestJava.m1");
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
                ,"/tt/TestJava.java:4: warning: Associated declaration",8
                );
    }
    
    @Test
    public void testPackage9() {
        main.addOptions("-method", "tt.TestJava.m1");
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
                ,"/tt/TestJava.java:4: warning: Associated declaration",8
                );
    }

}
