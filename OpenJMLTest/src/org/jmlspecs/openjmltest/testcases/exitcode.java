package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;
import com.sun.tools.javac.main.Option;
import com.sun.tools.javac.util.Options;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class exitcode extends EscBase {


    public exitcode(String options, String solver) {
        super(options, solver);
    }

    @Parameters
    static public Collection<String[]> parameters() {
        return EscBase.parameters();
    }

    @Override
    public void setUp() throws Exception {
        super.setUp();
        main.addOptions("-no-jmltesting");
        jmltesting = false;
    }
    
    @Test
    public void testNoWerror() {
        expectedExit = 0;
        helpTCX("tt.TestJava","package tt;  \n"
                +"class X { public void m() {} } public class TestJava extends X { \n"
                                // Need something that causes a warning -- here a missing also
                +"  //@ requires true;\n"
                +"  public void m() {  }\n"
                +"}"
                ,"/tt/TestJava.java:3: warning: Method m overrides parent class methods and so its specification should begin with 'also' (tt.TestJava.m() overrides tt.X.m())",7
        );

    }
    
    @Test
    public void testWerror() {
        main.addOptions("-Werror");
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class X { public void m() {} } public class TestJava extends X { \n"
                                // Need something that causes a warning -- here a missing also
                +"  //@ requires true;\n"
                +"  public void m() {  }\n"
                +"}"
                ,"/tt/TestJava.java:3: warning: Method m overrides parent class methods and so its specification should begin with 'also' (tt.TestJava.m() overrides tt.X.m())",7
                ,"/tt/TestJava.java: error: warnings found and -Werror specified",-1
        );

    }

    @Test
    public void testWerrorVerify() {
        main.addOptions("-Werror");
        expectedExit = 6;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava  { \n"
                +"  public void m() { /*@ assert false; */} \n"
                +"}"
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (Assert) in method m",25
        );

    }
    
    @Test
    public void testWerrorVerify2() {
        main.addOptions("-Werror","--verify-exit=0");
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava  { \n"
                +"  public void m() { /*@ assert false; */} \n"
                +"}"
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (Assert) in method m",25
        );
    }
    
    @Test
    public void testVerifyExit() {
        main.addOptions("--verify-exit=0");
        expectedExit = 0;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava  { \n"
                +"  public void m() { /*@ assert false; */} \n"
                +"}"
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (Assert) in method m",25
        );
    }
    
    @Test
    public void testVerifyExit2() {
        main.addOptions("--verify-exit=1");
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava  { \n"
                +"  public void m() { /*@ assert false; */} \n"
                +"}"
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (Assert) in method m",25
        );
    }
    

}
