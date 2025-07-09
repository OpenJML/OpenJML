package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.Assume;
import org.junit.FixMethodOrder;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** This file contains ESC tests of the JML value types. The files referenced are also used for RAC tests in primrac. */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class primesc extends EscBaseFiles {


    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }

    @Test
    public void jmlbigint() {
        helpTG();
    }
    
    @Test
    public void jmlbigintBad() {
        expectedExit = 1;
        helpTG(); // FIXME try compiling with -Xdiags:verbose (but does not seem to work)
    }
    
    @Test
    public void jmlTYPE() {
        helpTG();
    }
    
    @Test
    public void jmlreal() {
        helpTG();
    }
    
    @Test
    public void jmlstring() {
        helpTG();
    }
    
    @Test
    public void jmlseq() {
        helpTG();
    }
    

    @Test
    public void jmlarray() {
        helpTG();
    }
    

    @Test
    public void jmlrange() {
        helpTG();
    }
    
    @Test
    public void jmlset() {
        helpTG();
    }
    
    @Test
    public void jmlmap() {
        helpTG();
    }
    
    // TODO: Review these two and incorporate them with the above, if appropriate.
    
    @Test
    public void valuetypes() {
        helpTG();
    }

    @Test
    public void valuetypes2() {
        helpTG();
    }

}
