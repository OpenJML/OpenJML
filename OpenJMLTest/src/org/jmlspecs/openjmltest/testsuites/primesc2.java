package org.jmlspecs.openjmltest.testsuites;

//import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBaseFiles;

import static org.junit.Assert.fail;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** This file contains ESC tests of the JML value types. The files referenced are also used for RAC tests in primrac. */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class primesc2 extends EscBaseFiles {


    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }
    
    public void helpEscSimple(String ... opts) {
        super.helpEscSimple(opts);
    }

    
    @Test
    public void jmlreal() {
        helpEscSimple();
    }
    
    @Test
    public void jmlstring() {
        helpEscSimple();
    }
    
    @Test
    public void jmlstring2() {
        helpEscSimple();
    }
    
    @Test
    public void jmlseq() {
        helpEscSimple();
    }
    

    @Test
    public void jmlset() {
        helpEscSimple();
    }
    
}
