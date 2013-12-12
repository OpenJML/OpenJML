package tests;

import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;


@RunWith(Parameterized.class)
public class escinclause extends EscBase {

    public escinclause(String option, String solver) {
        super(option,solver);
    }
        
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        main.addOptions("-no-purityCheck");
        //main.addOptions("-jmlverbose");
        //main.addOptions("-method",   "m2bad");
        //main.addOptions("-jmldebug");
        //main.addOptions("-trace");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }

    @Test
    public void testInClause1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ model public int mx;\n"
                +"  int x; //@ in mx; \n"
                +"  int y;\n"

                +"  //@ assignable mx; \n"
                +"  public void m1bad(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"  //@ assignable mx; \n"
                +"  public void m1good(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assignable) in method m1bad",7
                ,"/tt/TestJava.java:6: warning: Associated declaration: /tt/TestJava.java:8: ",7
                );
    }

}
