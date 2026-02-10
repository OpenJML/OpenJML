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
public class primesc1 extends EscBaseFiles {


    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }
    
    public void helpTG(String ... opts) {
        super.helpTG(opts);
    }

    @Test
    public void jmlbigint() {
        helpTG("--method=shift","--show");
    }
    
    @Test
    public void jmlbigintCasts() {
        helpTG("--spec-math=java");
    }
    
    @Test
    public void jmldatagroup() {
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
    public void jmlmap() {
        helpTG();
    }
    
    @Test
    public void jmlinit() {
        helpTG();
    }
    
    @Test
    public void jmlTYPE() {
        helpTG();
    }
    
    
    // TODO: Review the following and incorporate them with the above, as appropriate.
    
    @Test
    public void locsetTests2() {
        helpTG();
    }

}
