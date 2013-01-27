package tests;

import java.util.ArrayList;
import java.util.Collection;

import org.jmlspecs.openjml.esc.JmlEsc;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import com.sun.tools.javac.util.Options;

/** This class of JUnit tests checks that nowarn works for esc tests.
 * @author David R. Cok
 *
 */
@RunWith(Parameterized.class)
public class escnowarn extends EscBase {

    String option;
    
    public escnowarn(String option) {
        this.option = option;
    }
    
    @Parameters
    static public  Collection<String[]> datax() {
        Collection<String[]> data = new ArrayList<String[]>(10);
        data.add(new String[]{"-boogie"}); 
        data.add(new String[]{"-newesc"}); 
        data.add(new String[]{null}); 
        //data.add(new String[]{"-rac"}); 
        return data;
    }
    
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        setOption(option);
        main.addOptions("-noPurityCheck");
        main.addOptions("-nullableByDefault"); // Because the tests were written this wasy
        //options.put("-jmlverbose",   "");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //JmlEsc.escdebug = true;
    }
    
    @Test
    public void testNowarnRequires() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { boolean b; \n"
                +"  //@   requires b;\n"  
                +"  public void mm() {}\n"
                
                +"  public void m() {\n"
                +"    mm(); \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Precondition) in method m",7
                ,"/tt/TestJava.java:3: warning: Associated declaration",9
                );
    }
    
    @Test
    public void testNowarnRequiresNW() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { boolean b;  \n"
                +"  //@   requires b;\n"  
                +"  public void mm() {}\n"
                
                +"  public void m() {\n"
                +"    mm();  //@ nowarn Precondition; \n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test
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
    
    @Test
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

    //  FIXME - disabled tests
    @Test @Ignore
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
    
    @Test @Ignore
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
    
    @Test @Ignore
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
                ,"/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Invariant) in method <init>",8
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",17
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Invariant) in method m",13
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",17
                );
    }
    
    @Test @Ignore
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
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Initially) in method <init>",13
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",17
                );
    }
    
    
    @Test @Ignore
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
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Constraint) in method m",13
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",18
                );
    }
    
    // TODO: represents, non_null field, non_null parameter, non_null method
    // TODO: non_null local, any local
    // TODO: signals_only, diverges, assignable
    // TODO: called preconditions
    // TODO: called undefined: div by 0, array index neg, array index too big
    // TODO: code undefined
}
    
