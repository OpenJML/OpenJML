package tests;

import org.jmlspecs.openjml.esc.JmlEsc;

import com.sun.tools.javac.util.Options;

/** This class of JUnit tests checks that nowarn works for esc tests.
 * @author David R. Cok
 *
 */
public class escnowarn extends EscBase {

    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        options.put("-noPurityCheck","");
        options.put("-nullableByDefault",""); // Because the tests were written this wasy
        //options.put("-jmlverbose",   "");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //JmlEsc.escdebug = true;
    }
    
    public void testNowarnRequires() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@   requires false;\n"  
                +"  public void mm() {}\n"
                
                +"  public void m() {\n"
                +"    mm(); \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: Invariants+Preconditions appear to be contradictory in method mm()",15
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Precondition) in method m",7
                ,"/tt/TestJava.java:3: warning: Associated declaration",9
                );
    }
    
    public void testNowarnRequiresNW() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@   requires false;\n"  
                +"  public void mm() {}\n"
                
                +"  public void m() {\n"
                +"    mm();  //@ nowarn Precondition; \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: Invariants+Preconditions appear to be contradictory in method mm()",15
                );
    }
    
    public void testNowarnEnsures() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@   ensures false;\n"
                +"  public void mm() {}   \n"
                
                +"  public void m() {\n" 
                +"      mm(); \n "
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Postcondition) in method mm",15
                ,"/tt/TestJava.java:3: warning: Associated declaration",9
                );
    }
    
    public void testNowarnEnsuresNW() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@   ensures false;\n"
                +"  public void mm() {}   //@ nowarn Postcondition; \n"
                
                +"  public void m() {\n" 
                +"      mm(); \n"
                +"  }\n"
                +"}"
                );
    }
    
//    public void testLocationEnsures2() {
//        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
//                +"  //@   ensures false;\n"
//                +"  public void m();\n"
//                +"}"
//                );
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m() {\n"
//                +"    return;\n"
//                +"  }\n"
//                +"}"
//                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Postcondition) in method m",5
//                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",9
//                );
//    }
//    
//    public void testLocationSignals() {
////        options.put("-progress","");
////        options.put("-jmlverbose","");
//        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
//                +"  //@   signals (Exception) false;\n"
//                +"  public void m();\n"
//                +"}"
//                );
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m() {\n"
//                +"    throw new RuntimeException();\n"
//                +"  }\n"
//                +"}"
//                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m",5
//                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",9
//                );
//    }
//    
//    public void testLocationInvariant() {
//        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
//                +"  //@ invariant i>=0;\n"
//                +"}"
//                );
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                +"  static int i;\n"
//                
//                +"  public void m() {\n"
//                +"    i = -1; return; \n"
//                +"  }\n"
//                +"}"
//                ,"/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Invariant) in method <init>",8
//                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",17
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Invariant) in method m",13
//                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",17
//                );
//    }
//    
//    public void testLocationInitially() {
//        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
//                +"  //@ initially i>=0;\n"
//                +"}"
//                );
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                +"  static int i;\n"
//                
//                +"  public TestJava() {\n"
//                +"    i = -1; return; \n"
//                +"  }\n"
//                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Initially) in method <init>",13
//                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",17
//                );
//    }
//    
//    
//    public void testLocationConstraint() {
//        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
//                +"  //@ constraint i>=\\old(i);\n"
//                +"}"
//                );
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                +"  static int i;\n"
//                
//                +"  public void m() {\n"
//                +"    i = -1; return; \n"
//                +"  }\n"
//                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Constraint) in method m",13
//                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",18
//                );
//    }
//    
//    // TODO: represents, non_null field, non_null parameter, non_null method
//    // TODO: non_null local, any local
//    // TODO: signals_only, diverges, assignable
//    // TODO: called preconditions
//    // TODO: called undefined: div by 0, array index neg, array index too big
//    // TODO: code undefined
}
    
