<<<<<<< HEAD
package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.fail;

import java.io.File;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjmltest.EscBase;
import org.jmlspecs.openjmltest.TCBase;
import org.junit.Assert;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;
import org.junit.runners.Parameterized.Parameters;

@RunWith(ParameterizedWithNames.class)
public class SFBugs extends EscBase {

//    @Override
//    public void setUp() throws Exception {
////        noCollectDiagnostics = true;
////        jmldebug = true;
//        super.setUp();
//    }

	public SFBugs(String options, String solver) {
		super(options, solver);
	}
	
    @Parameters
    static public Collection<String[]> parameters() {
        return minQuantAndSolvers(solvers);
    }
    
	public void helpTCF(String sourceDirname, String outDir, String ... opts) {
    	Assert.fail(); // FIXME - Java8 - long running
		escOnFiles(sourceDirname,outDir,opts);
	}



    @Test public void test() {
    	expectedExit = 1;
        helpTCF("test/tcWithJml/TCWithJml.java","test/tcWithJml", "-cp", "test/tcWithJml", "-check");
    }
    
    @Test public void sfpatch25() {
    	expectedExit = 0;
        helpTCF("test/sfpatch25/A.java","test/sfpatch25", "-cp", "test/sfpatch25", "-esc","-quiet");
    }
    
    @Test public void sfbug407() {
    	expectedExit = 0;
        helpTCF("test/sfbug407","test/sfbug407", "-cp", "test/sfbug407", "-esc", "-progress");
    }
    
    @Test public void sfbug398() {
    	expectedExit = 0;
        helpTCF("test/sfbug398","test/sfbug398", "-cp", "test/sfbug398", "-esc", "-progress");
    }
    
    @Test public void sfbug399() {
    	expectedExit = 0;
        helpTCF("test/sfbug399","test/sfbug399", "-cp", "test/sfbug399", "-esc","-progress");
    }
    
    @Ignore // very long running
    @Test public void sfbug404() {
    	expectedExit = 0;
        helpTCF("test/sfbug404","test/sfbug404", "-cp", "test/sfbug404", "-esc","-progress","-logic=AUFNIRA");
    }
    
    @Test public void sfbug408() {
    	expectedExit = 0;
        helpTCF("test/sfbug408","test/sfbug408", "-cp", "test/sfbug408", "-esc","-progress");
    }
    
    @Test public void sfbug409() {
    	expectedExit = 0;
        helpTCF("test/sfbug409","test/sfbug409", "-cp", "test/sfbug409", "-esc","-progress");
    }
    
    @Test public void sfbug410() {
    	expectedExit = 0;
        helpTCF("test/sfbug410","test/sfbug410", "-cp", "test/sfbug410", "-esc","-progress");
    }
    
    @Ignore // Can be very long running
    @Test public void sfbug414() {
    	expectedExit = 0;
        helpTCF("test/sfbug414","test/sfbug414", "-cp", "test/sfbug414", "-esc","-progress","-logic=AUFNIRA","-escMaxWarnings=5","-show","-method=Sqrt.sqrt","-subexpressions");
    }
    
    
}
=======
package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.fail;

import java.io.File;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjmltest.EscBase;
import org.jmlspecs.openjmltest.TCBase;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;
import org.junit.runners.Parameterized.Parameters;

@RunWith(ParameterizedWithNames.class)
public class SFBugs extends EscBase {

//    @Override
//    public void setUp() throws Exception {
////        noCollectDiagnostics = true;
////        jmldebug = true;
//        super.setUp();
//    }

	public SFBugs(String options, String solver) {
		super(options, solver);
	}
	
    @Parameters
    static public Collection<String[]> parameters() {
        return minQuantAndSolvers(solvers);
    }
    
	public void helpTCF(String sourceDirname, String outDir, String ... opts) {
		escOnFiles(sourceDirname,outDir,opts);
	}



    @Test public void test() {
    	expectedExit = 1;
        helpTCF("test/tcWithJml/TCWithJml.java","test/tcWithJml", "-cp", "test/tcWithJml", "-check");
    }
    
    @Test public void sfpatch25() {
    	expectedExit = 0;
        helpTCF("test/sfpatch25/A.java","test/sfpatch25", "-cp", "test/sfpatch25", "-esc","-quiet");
    }
    
    @Test public void sfbug407() {
    	expectedExit = 0;
        helpTCF("test/sfbug407","test/sfbug407", "-cp", "test/sfbug407", "-esc", "-progress");
    }
    
    @Test public void sfbug398() {
    	expectedExit = 0;
        helpTCF("test/sfbug398","test/sfbug398", "-cp", "test/sfbug398", "-esc", "-progress");
    }
    
    @Test public void sfbug399() {
    	expectedExit = 0;
        helpTCF("test/sfbug399","test/sfbug399", "-cp", "test/sfbug399", "-esc","-progress");
    }
    
    @Ignore // very long running
    @Test public void sfbug404() {
    	expectedExit = 0;
        helpTCF("test/sfbug404","test/sfbug404", "-cp", "test/sfbug404", "-esc","-progress","-logic=AUFNIRA");
    }
    
    @Test public void sfbug408() {
    	expectedExit = 0;
        helpTCF("test/sfbug408","test/sfbug408", "-cp", "test/sfbug408", "-esc","-progress");
    }
    
    @Test public void sfbug409() {
    	expectedExit = 0;
        helpTCF("test/sfbug409","test/sfbug409", "-cp", "test/sfbug409", "-esc","-progress");
    }
    
    @Test public void sfbug410() {
    	expectedExit = 0;
        helpTCF("test/sfbug410","test/sfbug410", "-cp", "test/sfbug410", "-esc","-progress");
    }
    
    @Ignore // Can be very long running
    @Test public void sfbug414() {
    	expectedExit = 0;
        helpTCF("test/sfbug414","test/sfbug414", "-cp", "test/sfbug414", "-esc","-progress","-logic=AUFNIRA","-escMaxWarnings=5","-show","-method=Sqrt.sqrt","-subexpressions");
    }
    
    @Test public void gitbug257() {
    	expectedExit = 0;
        helpTCF("test/gitbug257","test/gitbug257", "-cp", "test/gitbug257", "-esc", "-progress", "-logic=AUFNIRA");
    }
    
    @Test public void gitbug260() {
    	expectedExit = 0;
        helpTCF("test/gitbug260","test/gitbug260", "-cp", "test/gitbug260", "-esc", "-progress");
    }
    
    @Test public void gitbug431() {
    	expectedExit = 0;
        helpTCF("test/gitbug431","test/gitbug431", "-cp", "test/gitbug431", "-esc", "-progress");
    }
    
    @Test public void gitbug450() {
    	expectedExit = 0;
        helpTCF("test/gitbug450","test/gitbug450", "-cp", "test/gitbug450", "-esc", "-progress");
    }
    
    @Test public void gitbug450b() {
    	expectedExit = 0;
        helpTCF("test/gitbug450b","test/gitbug450b", "-cp", "test/gitbug450b", "-esc", "-progress");
    }
    
    @Test public void gitbug454() {
    	expectedExit = 0;
        helpTCF("test/gitbug454","test/gitbug454", "-cp", "test/gitbug454", "-esc");
    }
    
    @Test public void gitbug458() {
    	expectedExit = 0;
        helpTCF("test/gitbug458","test/gitbug458", "-cp", "test/gitbug458", "-esc");
    }
    
    @Test public void gitbug458a() {
    	expectedExit = 0;
        helpTCF("test/gitbug458a","test/gitbug458a", "-cp", "test/gitbug458a", "-esc");
    }
    
    @Test public void gitbug458b() {
    	expectedExit = 0;
        helpTCF("test/gitbug458b","test/gitbug458b", "-cp", "test/gitbug458b", "-esc");
    }
    
    @Test public void gitbug459() {
    	expectedExit = 0;
        helpTCF("test/gitbug459","test/gitbug459", "-cp", "test/gitbug459", "-esc");
    }
    
    
}
>>>>>>> refs/heads/master
