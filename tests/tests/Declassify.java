package tests;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.junit.Test;


public class Declassify extends TCBase {

    String eol = "\n";  
    
    @Override
    public void setUp() throws Exception {
        super.setUp();        
        main.addOptions("-noPurityCheck");
        main.addOptions("-jmltesting");
        main.addOptions("-noInternalRuntime");
        main.addOptions("-esc");
    }

    @Test
    public void testNormalCaseSingleLine() throws IOException{
        helpTCF("A.java", caseFromStub("testNormalCaseSingleLine"));
    }
    
    @Test
    public void testNormalCaseMultiline() throws IOException{
        helpTCF("A.java", caseFromStub("testNormalCaseMultiline"));
    }
    
    
    @Test
    public void testMissingPolicyClause() throws IOException{
        helpTCF("A.java", caseFromStub("testMissingPolicyClause"), "/A.java:2: Each declassify clause must have a policy that justifies the declassification (hint: use keyword \"usingPolicy\")", 60);
    }
    
    @Test
    public void testMissingPolicyName() throws IOException{
        helpTCF("A.java", caseFromStub("testMissingPolicyName"),
                "/A.java:2: The type or expression near here is invalid (or not implemented): ( token <JMLEND> in JmlParser.term3())",
                70,
                "/A.java:2: Missing a policy expression within a declassification clause (hint: myPolicy(arg1, arg2))",
                69);
    }
    
    @Test
    public void testMissingWhat() throws IOException{
        helpTCF("A.java", caseFromStub("testMissingWhat"), "/A.java:2: Missing an expression to declassify", 19);
    }
    
    @Test
    public void testMissingSemi() throws IOException{
        helpTCF("A.java", caseFromStub("testMissingSemi"), expectedFromStub("testMissingSemi"));
    }
    
    
}
