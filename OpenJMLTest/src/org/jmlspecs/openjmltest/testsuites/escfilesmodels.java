package org.jmlspecs.openjmltest.testsuites;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjmltest.EscBase;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escfilesmodels extends EscBaseFiles {
    
    String cpathAddition = "";

    public void helpEscFile(String sourceDirname, String outDir, String ... opts) {
        //Assert.fail(); // FIXME - Java8 - long running
        ArrayList<String> list = new ArrayList<String>();
        list.add("-code-math=safe");
        list.add("-spec-math=bigint");
        list.add("--check-feasibility=precondition,reachable,exit,spec");
        list.add("--progress");
        list.addAll(Arrays.asList(opts));
        escOnFiles(sourceDirname,outDir,list.toArray(opts));
    }

    public void helpTCG(String ... opts) {
        String dir = "test/" + getTestName();
        List<String> a = new LinkedList<>();
        a.add(0,"-cp"); 
        a.add(1,dir + cpathAddition);
        a.add("--code-math=safe");
        a.add("--spec-math=bigint");
        a.add("--check-feasibility=precondition,reachable,exit,spec");
        a.add("--source-path=$SY");
        a.add("--progress");
        a.addAll(Arrays.asList(opts));
        escOnFiles(dir, dir, a.toArray(new String[a.size()]));
    }

    public void helpTCGNoOptions(String ... opts) {
        String dir = "test/" + getTestName();
        List<String> a = new LinkedList<>();
        a.add(0,"-cp"); 
        a.add(1,dir + cpathAddition);
        a.addAll(Arrays.asList(opts));
        escOnFiles(dir, dir, a.toArray(new String[a.size()]));
    }



    @Test public void gitbug431() {
        expectedExit = 0;
        helpEscFile("test/gitbug431","test/gitbug431", "-cp", "test/gitbug431", "--esc", "--progress");
    }
        
    @Test public void gitbug461() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug498() {
        expectedExit = 0;
        helpTCG();
    }

    @Ignore // FIXME - times out
    @Test public void gitbug500a() {
        helpTCG("--solver-seed=242");
    }

    @Ignore // FIXME - times out
    @Test public void gitbug500b() {
        helpTCG("--solver-seed=242");
    }

    @Ignore // times out
    @Test public void gitbug584() {
        expectedExit = 0;
    }
    
    @Test @Ignore  // Needs specs about double
    public void gitbug633() {
        Assume.assumeTrue(runLongTests); // FIXME - And not yet working either
        cpathAddition = ":../OpenJML/runtime";
        expectedExit = 0;
        helpTCG();
    }
    
    
    @Test
    public void gitbug673() {
        expectedExit = 0;
        helpTCG();
    }
}

