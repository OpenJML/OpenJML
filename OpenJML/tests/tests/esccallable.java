package tests;

import java.util.Collection;

import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class esccallable extends EscBase {

    public esccallable(String option, String solver) {
        super(option,solver);
    }
    
    @Test
    public void testBasicCallable() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable \\nothing;\n"
                +"  public void m() {}\n"
                +"}"
                );
    }

    @Test
    public void testBasicCallable2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n;\n"
                +"  void m() { n(); }\n"
                +"  void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testBasicCallable3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable \\nothing;\n"
                +"  public void m() { n(); }\n"
                +"  void n() {}\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Callable) in method m",22
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

    @Test
    public void testBasicCallable4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n;\n"
                +"  void m() { p(); }\n"
                +"  void n() {}\n"
                +"  void p() {}\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Callable) in method m",15
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

}
