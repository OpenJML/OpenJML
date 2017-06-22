package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;

//FIXME _ need to test when inline body is in separate file
//FIXME _ need to test when inline body is in separate file that is not parsed on the command-line
// FIXME - need to test when inline is in .jml
// FIXME - need to test when inline is in .jml for a binary class

@RunWith(ParameterizedWithNames.class)
public class escbitvector extends EscBase {

    public escbitvector(String options, String solver) {
        super(options,solver);
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
    
    @Test 
    //@ code_java_math spec_java_math
    public void testBV1() {
    	main.addOptions("-show","-method=m1","-escBV");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires n <= 0x7ffffff0;\n"
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure;\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n"
                +"  }\n"
                                
                +"}"
                );
    }
    

}
