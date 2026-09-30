package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.SFBugsBase;
import org.jmlspecs.openjml.Main;

import java.util.*;

import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** Part 3 of the escsf tests (formerly SFBugs) (split in three so that no one suite dominates a parallel run); the
 * shared setup and helper methods are in SFBugsBase. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escsf3 extends SFBugsBase {

    @Test
    public void gitbug643() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
    public void gitbug644() {
        helpEscSimple();
    }
        
    @Test
    public void gitbug647() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug648() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug648a() {
        expectedExit = 6;
        helpEscSimple("-cp","test/gitbug648");
    }
    
    @Test
    public void gitbug650() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug650a() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug650b() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug650c() {
        helpEscSimple();
    }

    @Test
    public void gitbug651() {
        helpEscSimple();
    }

    @Test
    public void gitbug651a() {
        expectedExit = 1;
        helpEscSimple(); 
    }   
        
    @Test
    public void gitbug651b() {
        helpEscSimple();
    }

    @Test
    public void gitbug653() {
        helpEscSimple("--specs-path=test/gitbug653");
    }
    
    @Test
    public void gitbug654() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug659() {
        helpEscSimple();
    }
    
    
    @Test
    public void gitbug667() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug669() {
    }
    
    @Test
    public void gitbug666() {
    }
    
    @Test
    public void gitbug670() {
        helpEscSimple();
    }
    
    @Test // FIXME -- Crash in speculative attribution
    public void gitbug671() {
        helpEscFile("test/gitbug672/commons-collections4-4.3-sources/org/apache/commons/collections4/set/ListOrderedSet.java","test/gitbug671","--timeout=1800","-no-staticInitWarning","-cp","test/gitbug672/commons-collections4-4.3-sources","--esc-max-warnings=1");
    }
    
    @Test @Ignore // FIXME -- nullpointer exception, time out //  // Complained of infinite run time
    public void gitbug672() {
        helpEscFile("test/gitbug672/commons-collections4-4.3-sources/org/apache/commons/collections4/bidimap/TreeBidiMap.java","test/gitbug672","--timeout=1800","-no-staticInitWarning","-cp","test/gitbug672/commons-collections4-4.3-sources","--esc-max-warnings=1");
    }
    
    @Test
    public void gitbug676() {
        helpEscSimple();
    }
    
    @Test @Ignore // FIXME - this seems to be an incompleteness or bug in Z3 non-linear computations
    public void gitbug677() {
        helpEscSimple("--code-math=safe");//,"-show","-method=calculateArea","-subexpressions","-ce"); // The problem manifests with safe math
    }
    
    @Test
    public void gitbug678() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug681() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug682() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug683() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug684() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug685() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug686() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug687() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug688() {
        helpEscSimple("--subexpressions");
    }
    
    @Test
    public void gitbug688err() {
        expectedExit = 1;
        helpEscSimple("--subexpressions");
    }
    
    @Test
    public void gitbug695() {
        helpEscSimple("--check-feasibility=precondition,reachable,exit,spec,assume,assert");
    }
    
    @Test
    public void gitbug696() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug698() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug698A() {
        helpEscSimple();
    }
    
    @Test @Ignore // Will erroneously succeed until measured_by is implemented
    public void gitbug705() {
        helpEscSimple();
    }

    @Test @Ignore // FIXME: Bug fixed, but the specs are not complete
    public void gitbug710() {
        helpEscFile("test/gitbug710/java/util/IdentityHashMap.java", "test/gitbug710","-cp","test/gitbug710","-no-staticInitWarning","--timeout=300");
    }
    
    @Test
    public void gitbug711() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug712() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug716() {
        helpEscSimple();
    }
    
    @Test @Ignore // FIXME: EXAMPLE SPECS NOT YET COMPLETE
    public void gitbug717() {
        helpEscSimple();
    }
    
    @Test @Ignore // FIXME: Specs not yet finished
    public void gitbug718() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug718a() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug718x1() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug718x2() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug718x4() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug719() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug719a() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug722() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug733() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug733a() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug734() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug736() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug737() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug738() {
        helpEscSimple("--warn=missing-measured-by","--check-feasibility=none");
    }
    
    @Test
    public void gitbug738a() {
        helpEscSimple("--check-feasibility=none");
    }
    
    @Test
    public void gitbug740() {
        helpEscSimple("--check-feasibility=none");
    }
    
    @Test
    public void gitbug741() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
    public void gitbug888() {
        helpEscSimple("--check-feasibility=all");
    }
    
    @Test
    public void gitbug888a() {
        helpEscSimple("--check-feasibility=basic");
    }
    
    @Test
    public void gitbug998() {
        helpEscSimple();
    }
    
    @Test
    public void gitbug999() {
        helpEscSimple();
    }
    
    @Test
    public void rise4fun() {
        helpTGNoOptions("--check-feasibility=precondition,exit");
    }

}
