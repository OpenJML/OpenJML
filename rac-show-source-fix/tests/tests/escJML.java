package tests;

import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(Parameterized.class)
public class escJML extends EscBase {

    @Override
    public void setUp() throws Exception {
        testspecpath1 = "$A"+z+"$B"+ z + "$SY";
        super.setUp();
    }
    
    @Override
    public void tearDown() throws Exception {
        testspecpath1 = "$A"+z+"$B";
        super.tearDown();
    }
    
    public escJML(String option, String solver) {
        super(option,solver);
    }
    
    @Test
    public void testLBLObject() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m(String i) { \n"
                +"     //@ assert JML.lbl(\"AL\",i) == null; \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test
    public void testLBLint() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m(int i) { \n"
                +"     //@ assert JML.lbl(\"AL\",i) == 0; \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test
    public void testLBLshort() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m(short i) { \n"
                +"     //@ assert JML.lbl(\"AL\",i) == 0; \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test @Ignore // FIXME - this creates a huge VC
    public void testLBLboolean() { 
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m(boolean i) { \n"
                +"     //@ assert JML.lbl(\"AL\",i); \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test
    public void testLBLdouble() {
        if ("cvc4".equals(solver)) return;
        main.addOptions("-logic=AUFNIRA");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m(double i) { \n"
                +"     //@ assert JML.lbl(\"AL\",i) == 0; \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test
    public void testLBLfloat() {
        if ("cvc4".equals(solver)) return;
        main.addOptions("-logic=AUFNIRA");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m(float i) { \n"
                +"     //@ assert JML.lbl(\"AL\",i) == 0; \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

}
