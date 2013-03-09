package tests;

import org.junit.Test;


public class escinclause extends EscBase {

    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        options.put("-newesc","");
        options.put("-noPurityCheck","");
        //options.put("-jmlverbose",   "");
        //options.put("-method",   "m2bad");
        //options.put("-showbb",   "");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //options.put("-showce",   "");
        //options.put("-trace",   "");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }

    @Test
    public void testInClause1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ model int mx;\n"
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
                ,"/tt/TestJava.java:6: warning: Associated declaration",7
                );
    }

}
