package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.SFBugsBase;
import org.jmlspecs.openjml.Main;

import java.util.*;

import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** Part 2 of the escsf tests (formerly SFBugs) (split in three so that no one suite dominates a parallel run); the
 * shared setup and helper methods are in SFBugsBase. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escsf2 extends SFBugsBase {

    @Ignore // FIXME - needs work
    @Test public void gitbug482() {
        helpEscFile("test/gitbug482/checkers/src/main/java/checkers","test/gitbug482", "-cp", "test/gitbug482/checkers/src/main","--check"); // check only, not esc
    }

    @Test public void gitbug556() {
        helpEscSimple();
    }
    
    @Test public void gitbug557() {
        helpEscSimple();
    }
    
    @Test public void gitbug558() {
        helpEscSimple();
    }
    
    @Test public void gitbug558a() {
        helpEscSimple();
    }
    
    @Test public void gitbug558b() {
        helpEscSimple();
    }
    
    @Test public void gitbug559() {
        helpEscSimple();
    }
    
    @Test public void gitbug559a() {
        helpEscSimple();
    }
    
    @Test public void gitbug560() {
        helpEscSimple("--check-feasibility=none");
    }
    
    @Test public void gitbug567() {
        helpEscSimple();
    }
    
    @Test public void gitbug567a() {
        helpEscSimple("--code-math=java");
    }
    
    @Test public void gitbug567b() {
        helpEscSimple("--code-math=safe");
    }
    
    @Test public void gitbug567c() {
        helpEscSimple("--code-math=bigint");
    }
    
    @Test public void gitbug572() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    // The .jml file is on the command-line, which caused a crash, now fixed
    @Test public void gitbug573() {
        expectedExit = 2;
        helpEscFile("test/gitbug573/pckg/A.jml","test/gitbug573","-sourcepath","test/gitbug573");
    }
    
    @Test public void gitbug573a() {
        helpEscSimple();
    }
    
    // Here .jml is on the command-line, but the .java does not exist
    @Test public void gitbug573b() {
        expectedExit = 2;
        helpEscFile("test/gitbug573b/pckg/A.jml","test/gitbug573b","-sourcepath","test/gitbug573b");
    }
    
    @Test public void gitbug573c() {
        expectedExit = 2;
        helpEscFile("test/gitbug573c/java/lang/Integer.jml","test/gitbug573c","-sourcepath","test/gitbug573c");
    }
    
    @Test public void gitbug574() {
        helpEscSimple();
    }
    
    @Test public void gitbug575() {
        helpEscSimple();
    }
    
    @Test public void gitbug578() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug589() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
    public void gitbug591() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug593() {
        helpEscSimple("-check");
    }
    
    @Test
    public void gitbug594() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug596a() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug596b() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug596c() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug596d() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug597() {
        helpEscSimple("--esc-max-warnings=1");
    }
    
    @Test
    public void gitbug598() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug598a() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug602() {
        helpEscSimple("-Xlint:unchecked");
    }
    
    @Test
    public void gitbug603() {
        expectedExit = Main.Result.CMDERR.exitCode;
        helpEscSimple("-Xmaxwarns=100"); // Arguments are part of the test
    }
    
    @Ignore   // FIXME requires implementation of \not_assigned
    @Test
    public void gitbug604() {
        helpEscSimple("--code-math=safe","--method=AbsInterval.add");
    }
    
    @Test
    public void gitbug605() {
        helpEscSimple("--code-math=safe");
    }
    
    @Test
    public void gitbug606() {
        helpEscSimple("--code-math=safe");
    }
    
    @Test
    public void gitbug607() {
        helpEscSimple("--show","--method=x"); // Arguments are part of the test
    }
    
    @Test
    public void gitbug608() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug610() {
        helpEscSimple("--code-math=safe");
    }
    
    @Test
    public void gitbug611() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug613() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug615() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug618() {
        helpEscSimple("--check-feasibility=precondition,reachable,exit,spec,assume,assert");
    }
    
    @Test
    public void gitbug621() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug621a() { // Original bug
        helpEscSimple("--method=testMethod"); // Limited to this one method
    }
    
    @Test
    public void gitbug622() { // Problem with implicit assertion about string literal
        helpEscSimple("-staticInitWarning");
    }
    
    @Test
    public void gitbug623() {
        helpEscSimple("--check-feasibility=precondition,reachable,exit,spec,assume,assert");
    }
    
    @Ignore // Varying test output in trace
    @Test
    public void gitbug626() {
        helpEscSimple("--subexpressions");
    }
    
    @Ignore // FIXME - Problem with fresh in loop bodies
    @Test
    public void gitbug627() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug629() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug629a() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug630() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug630a() { // FIXME - SMT encpoding problem
        helpEscSimple();
    }
    
    @Test
    public void gitbug631() {
        helpEscSimple("--check-feasibility=precondition,reachable,exit,spec,assume,assert");
    }
    
    @Test  // Z3 non-deterministically crashes; trying to fix that by specifying the seed
    public void gitbug633a() {
        helpEscSimple("--solver-seed=42");
    }
    
    @Test
    public void gitbug634() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug635() {
        expectedExit = 6;
        helpEscSimple();
    }
    
    @Test
    public void gitbug636() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
    public void gitbug637() {
        helpEscSimple();
    }

    @Test
    public void gitbug638() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
   public void gitbug639() {
       helpEscSimple();
   }
   
    @Test
   public void gitbug639a() {
       helpEscSimple();
   }
   
    @Test
    public void gitbug640() {
        helpEscSimple();
    }

}
