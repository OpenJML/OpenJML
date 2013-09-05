package tests;

import java.io.IOException;

import org.junit.Before;
import org.junit.Test;

public class Levels extends TCBase {

    String eol = "\n";  
    
    @Before
    public void setUp() throws Exception {
        super.setUp();        
//        main.addOptions("-noPurityCheck");
//        main.addOptions("-jmltesting");
//        main.addOptions("-noInternalRuntime");
//        main.addOptions("-esc");
        jmldebug = true;
//    
        }

    @Test
    public void testOnMethod() throws IOException{
        helpTCF("A.java", caseFromStub("testOnMethod"));
    }
    
    @Test
    public void testOnFormalParameters() throws IOException{
        helpTCF("A.java", caseFromStub("testOnFormalParameters"));
    }
    
    @Test
    public void testOnField() throws IOException{
        helpTCF("A.java", caseFromStub("testOnField"));
    }
    
    @Test
    public void testOnLocalVariable() throws IOException{        
        helpTCF("A.java", caseFromStub("testOnLocalVariable"));
    }
    
    
}