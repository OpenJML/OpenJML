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
		ignoreNotes = true;
	}
	
    @Parameters
    static public Collection<String[]> parameters() {
        return minQuantAndSolvers(solvers);
    }
    
	public void helpTCF(String sourceDirname, String outDir, String ... opts) {
    	//Assert.fail(); // FIXME - Java8 - long running
		escOnFiles(sourceDirname,outDir,opts);
	}

	public void helpTCG(String ... opts) {
		String dir = "test/" + getMethodName(1);
		List<String> a = new LinkedList<>();
		a.add(0,"-cp"); a.add(1,dir);
		a.addAll(Arrays.asList(opts));
		escOnFiles(dir, dir, a.toArray(new String[a.size()]));
	}



    @Test public void typecheckWithJML() {
    	expectedExit = 1;
        helpTCF("test/tcWithJml/TCWithJml.java","test/tcWithJml", "-cp", "test/tcWithJml", "-check");
    }
    
    @Test public void sfpatch25() {
        helpTCF("test/sfpatch25/A.java","test/sfpatch25", "-cp", "test/sfpatch25", "-esc","-quiet");
    }
    
    @Test public void sfbug407() {
        helpTCF("test/sfbug407","test/sfbug407", "-cp", "test/sfbug407", "-esc", "-progress");
    }
    
    @Test public void sfbug398() {
        helpTCF("test/sfbug398","test/sfbug398", "-cp", "test/sfbug398", "-esc", "-progress");
    }
    
    @Test public void sfbug399() {
        helpTCF("test/sfbug399","test/sfbug399", "-cp", "test/sfbug399", "-esc","-progress");
    }
    
    @Ignore // very long running
    @Test public void sfbug404() {
        helpTCF("test/sfbug404","test/sfbug404", "-cp", "test/sfbug404", "-esc","-progress","-logic=AUFNIRA");
    }
    
    @Test public void sfbug408() {
        helpTCF("test/sfbug408","test/sfbug408", "-cp", "test/sfbug408", "-esc","-progress");
    }
    
    @Test public void sfbug409() {
        helpTCF("test/sfbug409","test/sfbug409", "-cp", "test/sfbug409", "-esc","-progress");
    }
    
    @Test public void sfbug410() {
        helpTCF("test/sfbug410","test/sfbug410", "-cp", "test/sfbug410", "-esc","-progress");
    }
    
    @Ignore // Can be very long running
    @Test public void sfbug414() {
    	expectedExit = 0;
        helpTCF("test/sfbug414","test/sfbug414", "-cp", "test/sfbug414", "-esc","-progress","-logic=AUFNIRA","-escMaxWarnings=5");
    }
    @Ignore // Can be very long running
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
    	expectedExit = 1;
    	ignoreNotes = true;
        helpTCF("test/gitbug450","test/gitbug450", "-cp", "test/gitbug450", "-esc", "-progress");
    }
    
    @Test public void gitbug450c() {
    	expectedExit = 0;
        helpTCF("test/gitbug450c","test/gitbug450c", "-cp", "test/gitbug450c", "-esc", "-progress");
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
    
    @Test public void gitbug462() {
    	expectedExit = 0;
        helpTCF("test/gitbug462","test/gitbug462", "-cp", "test/gitbug462", "-esc");
    }
    
    @Test public void gitbug462a() {
    	expectedExit = 0;
        helpTCF("test/gitbug462a","test/gitbug462a", "-cp", "test/gitbug462a", "-esc");
    }
    
    @Test public void gitbug462b() {
    	expectedExit = 0;
        helpTCF("test/gitbug462b","test/gitbug462b", "-cp", "test/gitbug462b", "-esc" );//, "-show", "-method=Container.ContainerUser.allocate","-subexpressions");
    }
    
    @Test public void gitbug462c() {
    	expectedExit = 0;
        helpTCF("test/gitbug462c","test/gitbug462c", "-cp", "test/gitbug462c", "-esc");
    }
    
    @Test public void gitbug456() {
    	expectedExit = 0;
        helpTCF("test/gitbug456","test/gitbug456", "-cp", "test/gitbug456", "-esc", "-exclude", "bytebuf.ByteBuf.*");
    }
    
    @Test public void gitbug456a() {
    	expectedExit = 0;
        helpTCF("test/gitbug456a","test/gitbug456a", "-cp", "test/gitbug456a", "-esc", "-exclude", "bytebuf.ByteBuf.*");
    }
    
    @Test public void gitbug455() {
    	expectedExit = 0;
        helpTCF("test/gitbug455","test/gitbug455", "-cp", "test/gitbug455", "-esc");
    }
    
    @Ignore // Cannot reproduce the issue until the error's reporter gets back to us
    @Test public void gitbug446() {
    	expectedExit = 0;
        helpTCF("test/gitbug446","test/gitbug446", "-cp", "test/gitbug446", "-esc");
    }
    
    // FIXME - generics
    @Test public void gitbug445() {
    	expectedExit = 1;
        helpTCF("test/gitbug445","test/gitbug445", "-cp", "test/gitbug445");
    }
    
    @Test public void gitbug463() {
    	expectedExit = 0;
        helpTCF("test/gitbug463","test/gitbug463", "-cp", "test/gitbug463","-purityCheck");
    }
    
    @Test public void gitbug463a() {
    	expectedExit = 0;
        helpTCF("test/gitbug463a","test/gitbug463a", "-cp", "test/gitbug463a");
    }
    
    @Test public void gitbug444() {
    	expectedExit = 0;
        helpTCF("test/gitbug444","test/gitbug444", "-cp", "test/gitbug444"); //,"-show","-method=isRelaxedPrefix");
    }
    
    @Test public void gitbug444a() {
    	expectedExit = 0;
        helpTCF("test/gitbug444a","test/gitbug444a", "-cp", "test/gitbug444a");
    }

    @Test public void gitbug466() {
    	expectedExit = 0;
        helpTCF("test/gitbug466","test/gitbug466", "-cp", "test/gitbug466","-method=Test.run");
    }

    @Test public void gitbug467() {
    	expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug470() {
    	expectedExit = 0;
        helpTCF("test/gitbug470/ACD.java","test/gitbug470", "-cp", "test/gitbug470","-code-math=java");
    }

    @Test public void gitbug471() {
    	expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug469() {
    	expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug476() {
    	expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug477() {
    	expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug478() {
    	expectedExit = 0;
        helpTCG();
    }

    // Check everything in apache commons library!
    @Test @Ignore public void gitbug481() {
    	expectedExit = 0;
        helpTCF("test/gitbug481b","test/gitbug481", "-cp", "test/gitbug481b","-progress");
    }

    // Just one method, but parse and typecheck all files first
    @Test @Ignore public void gitbug481c() {
    	expectedExit = 0;
        helpTCF("test/gitbug481b","test/gitbug481c", "-cp", "test/gitbug481b","-method=org.apache.commons.math3.linear.ArrayFieldVector.getEntry");
    }

    // Just one method in one file
    @Test public void gitbug481b() {
    	expectedExit = 0;
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481b", "-cp", "test/gitbug481b","-method=org.apache.commons.math3.linear.ArrayFieldVector.getEntry");
    }

    // Just one file
    @Test public void gitbug481a() {
    	expectedExit = 1;
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a", "-cp", "test/gitbug481b");
    }

    @Test public void gitbug482() {
    	expectedExit = 0;
        helpTCF("test/gitbug482/checkers/src/main","test/gitbug482", "-cp", "test/gitbug482/checkers/src/main","-check"); // check only, not esc
    }

    public void gitbug999() {
    	expectedExit = 0;
        helpTCG();
    }
}

