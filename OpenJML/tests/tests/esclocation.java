package tests;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;


/** This class of JUnit tests checks that assertion violations for assertions
 * declared in other files are printed with source code from the other file.
 * @author David R. Cok
 *
 */
@RunWith(Parameterized.class)
public class esclocation extends EscBase {

    public esclocation(String option, String solver) {
        super(option,solver);
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        main.addOptions("-noPurityCheck");
        main.addOptions("-nullableByDefault"); // Because the tests were written this way
        //options.put("-jmlverbose",   "");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //JmlEsc.escdebug = true;
    }
    
    @Test
    public void testLocationRequires() {
        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
                +"  //@   requires false;\n"
                +"  public void mm();\n"
                +"}"
                );
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m() {\n"
                +"    mm();\n"
                +"  }\n"
                +"  public void mm() {}\n"
                +"}"  // FIXME - are the following the best error messages we can make?
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method m",7
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",9
                // FIXME - test for infeasible preconditions
                ,!option.equals("-custom") ? null : "/tt/TestJava.java:6: warning: Invariants+Preconditions appear to be contradictory in method mm()",15
                );
    }
    
    @Test
    public void testLocationEnsures() {
        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
                +"  //@   ensures false;\n"
                +"  public void m();\n"
                +"}"
                );
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m() {\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (Postcondition) in method m",15
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",9
                );
    }
    
    @Test
    public void testLocationEnsures2() {
        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
                +"  //@   ensures false;\n"
                +"  public void m();\n"
                +"}"
                );
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m() {\n"
                +"    return;\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Postcondition) in method m",5
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",9
                );
    }
    
    @Test
    public void testLocationSignals() {
//        options.put("-progress","");
//        options.put("-jmlverbose","");
        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
                +"  //@   signals (Exception) false;\n"
                +"  public void m();\n"
                +"}"
                );
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m() {\n"
                +"    throw new RuntimeException();\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m",5
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",9
                );
    }
    
    @Test
    public void testLocationInvariant() {
        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
                +"  //@ invariant i>=0;\n"
                +"}"
                );
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                
                +"  public void m() {\n"
                +"    i = -1; return; \n"
                +"  }\n"
                +"}"
                // FIXME - check constructor
                ,!option.equals("-custom") ? null : "/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Invariant) in method <init>",8
                ,!option.equals("-custom") ? null : "/$A/tt/TestJava.jml:2: warning: Associated declaration",17
                ,!option.equals("-custom") ? "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (InvariantExit) in method m"
                                           : "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Invariant) in method m"
                                               ,13
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",!option.equals("-custom") ? 7:17
                );
    }
    
    @Test
    public void testLocationInitially() {
        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
                +"  //@ initially i>=0;\n"
                +"}"
                );
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                
                +"  public TestJava() {\n"
                +"    i = -1; return; \n"
                +"  }\n"
                +"}"
                // FIXME - check constructor
                ,!option.equals("-custom") ? null : "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Initially) in method <init>",13
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",17
                );
    }
    
    
    @Test
    public void testLocationConstraint() {
        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
                +"  //@ constraint i>=\\old(i);\n"
                +"}"
                );
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                
                +"  public void m() {\n"
                +"    i = -1; return; \n"
                +"  }\n"
                +"}"
                // FIXME - normalize column
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Constraint) in method m",13
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",!option.equals("-custom") ? 7: 18
                );
    }
    
    // TODO: represents, non_null field, non_null parameter, non_null method
    // TODO: non_null local, any local
    // TODO: signals_only, diverges, assignable
    // TODO: called preconditions
    // TODO: called undefined: div by 0, array index neg, array index too big
    // TODO: code undefined
}
    
