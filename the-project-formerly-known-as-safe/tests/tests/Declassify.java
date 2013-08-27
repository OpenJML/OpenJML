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
    }

    @Test
    public void testNormalCaseMultiline() throws IOException{
        helpTC(fromStub("testNormalCaseMultiline"));
    }
    
    
}
