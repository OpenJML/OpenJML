package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Ignore;
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
    public void testBV2() {
        main.addOptions("-escBV=auto","-logic=ALL");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires n <= 0x7ffffff0;\n"
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure;\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    @Test 
    public void testBV2a() {
        main.addOptions("-escBV=true","-logic=ALL");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires n <= 0x7ffffff0;\n"
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure;\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    @Test 
    public void testBV1() {
        main.addOptions("-logic=ALL");  // Should use BV
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure;\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n"
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method m1",5
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                );
    }
    
    @Test 
    public void testBV1a() {
        main.addOptions("-logic=ALL");  // Default is auto BV
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure;\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n"
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method m1",5
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                );
    }
    
    @Test 
    public void testBV1b() {
        expectedExit = 1;
        main.addOptions("-escBV=false","-logic=ALL");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure;\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n" // ERROR - forcing no BV when there are BV ops
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:9: NOT IMPLEMENTED: Not yet supported feature in converting BasicPrograms to SMTLIB: Bit-operation BITAND",22
                ,"/tt/TestJava.java:5: NOT IMPLEMENTED: Not yet supported feature in converting BasicPrograms to SMTLIB: Bit-operation BITAND",23
                );
    }
    
    // FIXME - should the following emit a command-line error exit code and stop?
    @Test @Ignore
    public void testBVe1() {
        main.addOptions("-escBV","-logic=ALL");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires n <= 0x7ffffff0;\n"
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure;\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n" // ERROR - forcing no BV when there are BV ops
                +"  }\n"
                                
                +"}"
 //               ,"Command-line argument error: Expected 'auto', 'true' or 'false' for -escBV: -logic=ALL",0
          );
    }
    
    @Test @Ignore
    public void testBVe2() {
        main.addOptions("-escBV=xx","-logic=ALL");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires n <= 0x7ffffff0;\n"
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure;\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n" // ERROR - forcing no BV when there are BV ops
                +"  }\n"
                                
                +"}"
//                ,"Command-line argument error: Expected 'auto', 'true' or 'false' for -escBV: xx",0
         );
    }
    
    @Test @Ignore
    public void testBVe3() {
        main.addOptions("-escBV=","-logic=ALL");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires n <= 0x7ffffff0;\n"
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure;\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n" // ERROR - forcing no BV when there are BV ops
                +"  }\n"
                                
                +"}"
//                ,"Command-line argument error: Expected 'auto', 'true' or 'false' for -escBV: "
          );
    }
    
    @Test @Ignore
    public void testBVe4() {
        expectedExit = 1;
        main.addOptions("-escBV");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires n <= 0x7ffffff0;\n"
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure;\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n" // ERROR - forcing no BV when there are BV ops
                +"  }\n"
                                
                +"}"
                ,"warning: The last command-line option expects a parameter: -escBV",-1
//                ,"Command-line argument error: Expected 'auto', 'true' or 'false' for -escBV: "
          );
    }
    

}
