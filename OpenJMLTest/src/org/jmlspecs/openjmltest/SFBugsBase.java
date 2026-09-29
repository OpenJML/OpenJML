package org.jmlspecs.openjmltest;

import org.jmlspecs.openjml.Main;

import java.util.*;

import org.junit.*;

/** The shared setup and helper methods of the escsf1, escsf2 and escsf3 test suites */
public abstract class SFBugsBase extends EscBaseFiles {
    
    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        ignoreNotes = true;
        super.setUp();
    }
    
    public void helpEscSimple(String... opts) {
        super.helpEscSimple(opts);
    }

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

    public void helpTGNoOptions(String ... opts) {
        String dir = "test/" + getTestName();
        List<String> a = new LinkedList<>();
        a.add(0,"-cp"); 
        a.add(1,dir);
        a.addAll(Arrays.asList(opts));
        escOnFiles(dir, dir, a.toArray(new String[a.size()]));
    }
}
