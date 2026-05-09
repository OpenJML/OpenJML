package org.jmlspecs.openjmltest.testsuites;

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
public class primesc1 extends EscBaseFiles {


    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }
    
    public void helpEscSimple(String ... opts) {
        super.helpEscSimple(opts);
    }

    @Test
    public void jmlbigint() {
        helpEscSimple();
    }
    
    @Test
    public void jmlbigintCasts() {
        helpEscSimple("--spec-math=java");
    }
    
    @Test
    public void jmldatagroup() {
        helpEscSimple();
    }
    
    @Test
    public void jmlarray() {
        helpEscSimple();
    }
    

    @Test
    public void jmlrange() {
        helpEscSimple();
    }
    
    @Test
    public void jmlmap() {
        helpEscSimple();
    }
    
    @Test
    public void jmlinit() {
        helpEscSimple();
    }
    
    @Test
    public void jmlTYPE() {
        helpEscSimple();
    }
}
