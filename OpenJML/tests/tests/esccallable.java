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
                +"  public TestJava() {}\n"
                +"}"
                );
    }

}
