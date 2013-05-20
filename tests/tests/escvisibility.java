package tests;

import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class escvisibility extends EscBase {

    public escvisibility(String option, String solver) {
        super(option, solver);
    }
    
    @Parameters
    static public  Collection<String[]> datax() {
        return noOldData();
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        main.addOptions("-noPurityCheck");
        String z = java.io.File.pathSeparator;
        String testspecpath = "$A"+z+"$B";
        main.addOptions("-classpath",   testspecpath);
        main.addOptions("-sourcepath",   testspecpath);
        main.addOptions("-specspath",   testspecpath);
        main.addOptions("-quiet");
        //main.addOptions("-jmldebug");
        //main.addOptions("-noInternalSpecs");
        //main.addOptions("-trace");
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
    
    @Test
    public void testInvariant() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  public int pb;\n"
                +"  protected int pt;\n"
                +"   int pa;\n"
                +"  private int pv;\n"
                
                +"  //@ invariant 0 == pb;\n"  // Line 7
                +"  //@ invariant 0 == pt;\n"
                +"  //@ invariant 0 == pa;\n"
                +"  //@ invariant 0 == pv;\n"
                
                +"  //@ public invariant 0 == pb;\n"
                +"  //@ public invariant 0 == pt;\n"
                +"  //@ public invariant 0 == pa;\n"
                +"  //@ public invariant 0 == pv;\n"
                
                +"  //@ protected invariant 0 == pb;\n"  // Line 15
                +"  //@ protected invariant 0 == pt;\n"
                +"  //@ protected invariant 0 == pa;\n"
                +"  //@ protected invariant 0 == pv;\n"
                
                +"  //@ private invariant 0 == pb;\n"
                +"  //@ private invariant 0 == pt;\n"
                +"  //@ private invariant 0 == pa;\n"
                +"  //@ private invariant 0 == pv;\n"
                +"}"
                ,"/tt/TestJava.java:7: An identifier with public visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:8: An identifier with protected visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:10: An identifier with private visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:12: An identifier with protected visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:13: An identifier with package visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:15: An identifier with public visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:17: An identifier with package visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:18: An identifier with private visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:19: An identifier with public visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:21: An identifier with package visibility may not be used in a invariant clause with private visibility",30
                );
    }
    
    @Test
    public void testInvariantM() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  /*@ pure */public int pb(){return 0; };\n"
                +"  /*@ pure */protected int pt(){return 0; };\n"
                +"  /*@ pure */ int pa(){return 0; };\n"
                +"  /*@ pure */private int pv(){return 0; };\n"
                
                +"  //@ invariant 0 == pb();\n"  // Line 7
                +"  //@ invariant 0 == pt();\n"
                +"  //@ invariant 0 == pa();\n"
                +"  //@ invariant 0 == pv();\n"
                
                +"  //@ public invariant 0 == pb();\n"
                +"  //@ public invariant 0 == pt();\n"
                +"  //@ public invariant 0 == pa();\n"
                +"  //@ public invariant 0 == pv();\n"
                
                +"  //@ protected invariant 0 == pb();\n"  // Line 15
                +"  //@ protected invariant 0 == pt();\n"
                +"  //@ protected invariant 0 == pa();\n"
                +"  //@ protected invariant 0 == pv();\n"
                
                +"  //@ private invariant 0 == pb();\n"
                +"  //@ private invariant 0 == pt();\n"
                +"  //@ private invariant 0 == pa();\n"
                +"  //@ private invariant 0 == pv();\n"
                +"}"
                ,"/tt/TestJava.java:7: An identifier with public visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:8: An identifier with protected visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:10: An identifier with private visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:12: An identifier with protected visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:13: An identifier with package visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:15: An identifier with public visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:17: An identifier with package visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:18: An identifier with private visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:19: An identifier with public visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:21: An identifier with package visibility may not be used in a invariant clause with private visibility",30
                );
    }
    
    @Test
    public void testInvariant2() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  /*@ spec_public */ protected int pt;\n"
                +"  /*@ spec_public */  int pa;\n"
                +"  /*@ spec_public */ private int pv;\n"
                
                +"  //@ invariant 0 == pt;\n"  // Line 6
                +"  //@ invariant 0 == pa;\n"
                +"  //@ invariant 0 == pv;\n"
                
                +"  //@ public invariant 0 == pt;\n"
                +"  //@ public invariant 0 == pa;\n"
                +"  //@ public invariant 0 == pv;\n"
                
                +"  //@ protected invariant 0 == pt;\n"
                +"  //@ protected invariant 0 == pa;\n"
                +"  //@ protected invariant 0 == pv;\n"
                
                +"  //@ private invariant 0 == pt;\n"
                +"  //@ private invariant 0 == pa;\n"
                +"  //@ private invariant 0 == pv;\n"

                +"  /*@ spec_protected */  int pat;\n"
                +"  /*@ spec_protected */ private int pvt;\n"
                
                +"  //@ invariant 0 == pat;\n"
                +"  //@ invariant 0 == pvt;\n"
                
                +"  //@ public invariant 0 == pat;\n"
                +"  //@ public invariant 0 == pvt;\n"
                
                +"  //@ protected invariant 0 == pat;\n"
                +"  //@ protected invariant 0 == pvt;\n"
                
                +"  //@ private invariant 0 == pat;\n"
                +"  //@ private invariant 0 == pvt;\n"
                +"}"
                ,"/tt/TestJava.java:6: An identifier with public visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:7: An identifier with public visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:8: An identifier with public visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:12: An identifier with public visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:13: An identifier with public visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:14: An identifier with public visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:15: An identifier with public visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:16: An identifier with public visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:17: An identifier with public visibility may not be used in a invariant clause with private visibility",30
 
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:21: An identifier with protected visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:22: An identifier with protected visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:23: An identifier with protected visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:26: An identifier with protected visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:27: An identifier with protected visibility may not be used in a invariant clause with private visibility",30
                );
    }
    
    @Test
    public void testInClause() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  //@ model public int pb;\n"
                +"  //@ model protected int pt;\n"
                +"  //@ model  int pa;\n"
                +"  //@ model private int pv;\n"
                
                +"  public int x1; //@ in pb;\n"  // Line 7
                +"  public int x2; //@ in pt;\n"
                +"  public int x3; //@ in pa;\n"
                +"  public int x4; //@ in pv;\n"
                
                +"  protected int y1; //@ in pb;\n"
                +"  protected int y2; //@ in pt;\n"
                +"  protected int y3; //@ in pa;\n"
                +"  protected int y4; //@ in pv;\n"
                
                +"   int z1; //@ in pb;\n"
                +"   int z2; //@ in pt;\n"
                +"   int z3; //@ in pa;\n"
                +"   int z4; //@ in pv;\n"
                
                +"  private int t1; //@ in pb;\n"
                +"  private int t2; //@ in pt;\n"
                +"  private int t3; //@ in pa;\n"
                +"  private int t4; //@ in pv;\n"
                
                +"}"
                ,"/tt/TestJava.java:8: An identifier with protected visibility may not be used in a in clause with public visibility",25
                ,"/tt/TestJava.java:9: An identifier with package visibility may not be used in a in clause with public visibility",25
                ,"/tt/TestJava.java:10: An identifier with private visibility may not be used in a in clause with public visibility",25
                ,"/tt/TestJava.java:13: An identifier with package visibility may not be used in a in clause with protected visibility",28
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a in clause with protected visibility",28
                ,"/tt/TestJava.java:18: An identifier with private visibility may not be used in a in clause with package visibility",19
                );
    }
    
    @Test
    public void testRequires1() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  public boolean pb;\n"
                +"  protected boolean pt;\n"
                +"   boolean pa;\n"
                +"  private boolean pv;\n"
                
                +"  /*@ spec_public */ protected boolean ptb;\n"
                +"  /*@ spec_public */  boolean pab;\n"
                +"  /*@ spec_public */ private boolean pvb;\n"
                
                +"  /*@ spec_protected */  boolean pat;\n"
                +"  /*@ spec_protected */ private boolean pvt;\n"
                
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also private normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also protected normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also public normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  public void m(){}\n"
                +"}"
                ,"/tt/TestJava.java:12: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:12: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:12: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:12: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:12: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:18: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:18: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:20: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:20: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                );
    }
    
    @Test
    public void testRequires2() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  public boolean pb;\n"
                +"  protected boolean pt;\n"
                +"   boolean pa;\n"
                +"  private boolean pv;\n"
                
                +"  /*@ spec_public */ protected boolean ptb;\n"
                +"  /*@ spec_public */  boolean pab;\n"
                +"  /*@ spec_public */ private boolean pvb;\n"
                
                +"  /*@ spec_protected */  boolean pat;\n"
                +"  /*@ spec_protected */ private boolean pvt;\n"
                
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also private normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also protected normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also public normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  protected void m(){}\n"
                +"}"
                ,"/tt/TestJava.java:12: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:12: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:18: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:18: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:19: warning: There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:20: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:20: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                );
    }
    
    @Test
    public void testRequires3() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  public boolean pb;\n"
                +"  protected boolean pt;\n"
                +"   boolean pa;\n"
                +"  private boolean pv;\n"
                
                +"  /*@ spec_public */ protected boolean ptb;\n"
                +"  /*@ spec_public */  boolean pab;\n"
                +"  /*@ spec_public */ private boolean pvb;\n"
                
                +"  /*@ spec_protected */  boolean pat;\n"
                +"  /*@ spec_protected */ private boolean pvt;\n"
                
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also private normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also protected normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also public normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"   void m(){}\n"
                +"}"
                ,"/tt/TestJava.java:12: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:17: warning: There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:18: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:18: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:19: warning: There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:20: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:20: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                );
    }
    
    @Test
    public void testRequires4() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  public boolean pb;\n"
                +"  protected boolean pt;\n"
                +"   boolean pa;\n"
                +"  private boolean pv;\n"
                
                +"  /*@ spec_public */ protected boolean ptb;\n"
                +"  /*@ spec_public */  boolean pab;\n"
                +"  /*@ spec_public */ private boolean pvb;\n"
                
                +"  /*@ spec_protected */  boolean pat;\n"
                +"  /*@ spec_protected */ private boolean pvt;\n"
                
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also private normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also protected normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also public normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  private void m(){}\n"
                +"}"
                ,"/tt/TestJava.java:12: warning: There is no point to a specification case having more visibility than its method",7
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:17: warning: There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:18: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:18: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:19: warning: There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:20: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:20: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                );
    }
    

}
