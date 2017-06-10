package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.ParameterizedWithNames;
import org.junit.runners.Parameterized.Parameters;

@RunWith(ParameterizedWithNames.class)
public class escenums extends EscBase {

    public escenums(String options, String solver) {
        super(options,solver);
    }
    
    @Test
    public void testBasicEnum() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public enum TestJava { AA, BB, CC \n"
                +"}"
                );
    }
    
    @Test
    public void testUseEnum() {
        helpTCX("tt.TestJava","package tt; \n"
                +" enum Z { AA, BB, CC } \n"
                +" public class TestJava {\n"
                +"    public void m() {\n"
                +"       //@ assert Z.AA != Z.BB; \n"
                +"    }\n"
                +"}"
                );
    }
    
    @Test
    public void testUseEnum2() {
        helpTCX("tt.TestJava","package tt; \n"
                +" enum Z { AA, BB, CC } \n"
                +" public class TestJava {\n"
                +"    public void m() {\n"
                +"       //@ assert Z.AA == Z.AA; \n"
                +"    }\n"
                +"}"
                );
    }
    
    @Test
    public void testUseEnum3() {
        helpTCX("tt.TestJava","package tt; \n"
                +" enum Z { AA, BB, CC } \n"
                +" public class TestJava {\n"
                +"    public void m() {\n"
                +"       Object o = new Object();\n"
                +"       //@ assert Z.AA != o; \n"
                +"    }\n"
                +"}"
                );
    }
    
    @Test
    public void testUseEnum4() {
        helpTCX("tt.TestJava","package tt; \n"
                +" enum Z { AA, BB, CC } \n"
                +" public class TestJava {\n"
                +"    public void m(Object o) {\n"
                +"       //@ assume !(o instanceof Z) ;\n"
                +"       //@ assert Z.AA != o; \n"
                +"    }\n"
                +"}"
                );
    }
    
    @Test
    public void testUseEnum4a() {
        helpTCX("tt.TestJava","package tt; \n"
                +" enum Z { AA, BB, CC } \n"
                +" public class TestJava {\n"
                +"    public void m(Object o) {\n"
                +"       //@ assume (o instanceof Z) ;\n"
                +"       //@ assert o == Z.AA || o == Z.CC || o == Z.BB; \n"
                +"    }\n"
                +"}"
                );
    }
    
    @Test
    public void testUseEnum5() {
        helpTCX("tt.TestJava","package tt; \n"
                +" enum Z { AA, BB, CC } \n"
                +" public class TestJava {\n"
                +"    public void m(Object o) {\n"
                +"       //@ assert Z.AA != o; \n"
                +"    }\n"
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }
    
    @Test
    public void enumSwitch() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava {\n"
                +"    //@ ensures \\result > 0;\n"
                +"    //@ ensures the_value == MyEnum.ONE ==> \\result == 2;\n"
                +"    //@ ensures the_value == MyEnum.TWO ==> \\result == 4;\n"
                +"    //@ ensures the_value == MyEnum.THREE ==> \\result == 8;\n"
                +"    public int switchStatement(final MyEnum the_value) {\n"
                +"      int result = 0;\n"
                +"      switch (the_value) {\n"
                +"        case ONE:    \n"
                +"          result = 2;\n"
                +"          break;    \n"
                +"              \n"
                +"        case TWO:    \n"
                +"          result = 4;    \n"
                +"          break;    \n"
                +"              \n"
                +"        case THREE:    \n"
                +"          result = 8;    \n"
                +"          break;    \n"
                +"              \n"
                +"        default:    \n"
                +"          result = 1;    \n"
                +"      }    \n"
                +"      return result;    \n"
                +"   }    \n"
                +"        \n"
                +"   static public enum MyEnum {    \n"
                +"      ONE, TWO, THREE;    \n"
                +"   }    \n"
                +"}    \n"
                );
        }
        

}
