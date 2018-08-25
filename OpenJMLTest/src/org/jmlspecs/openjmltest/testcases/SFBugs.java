package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.fail;

import java.io.File;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.Main;
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

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
		ignoreNotes = true;
    }

	public SFBugs(String options, String solver) {
		super(options, solver);
	}
	
    @Parameters
    static public Collection<String[]> parameters() {
        return minQuantAndSolvers(solvers);
    }
    
	public void helpTCF(String sourceDirname, String outDir, String ... opts) {
    	//Assert.fail(); // FIXME - Java8 - long running
	    ArrayList<String> list = new ArrayList<String>();
	    list.add("-code-math=bigint");
	    list.add("-spec-math=bigint");
        list.addAll(Arrays.asList(opts));
		escOnFiles(sourceDirname,outDir,list.toArray(opts));
	}

    public void helpTCG(String ... opts) {
        String dir = "test/" + getMethodName(1);
        List<String> a = new LinkedList<>();
        a.add(0,"-cp"); 
        a.add(1,dir);
        a.add("-code-math=bigint");
        a.add("-spec-math=bigint");
        a.addAll(Arrays.asList(opts));
        escOnFiles(dir, dir, a.toArray(new String[a.size()]));
    }

    public void helpTCGNoOptions(String ... opts) {
        String dir = "test/" + getMethodName(1);
        List<String> a = new LinkedList<>();
        a.add(0,"-cp"); 
        a.add(1,dir);
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
    @Ignore // Can be very long running because it uses floating point
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
    
    @Test public void gitbug457() {
    	expectedExit = 0;
        helpTCG("-nullableByDefault");
    }
    
    @Test public void gitbug457a() {
    	expectedExit = 0;
        helpTCG("-nonnullByDefault");
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
    
    @Ignore // FIXME - needs all the model classes - and they need cleaning up
    @Test public void gitbug461() {
    	expectedExit = 0;
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
        helpTCF("test/gitbug462b","test/gitbug462b", "-cp", "test/gitbug462b", "-esc");
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
    
    @Test public void gitbug445() {
    	expectedExit = 1;
        helpTCG();
    }
    
    @Ignore // FIXME - model specs
    @Test public void gitbug445a() {
        helpTCG();
    }
    
    @Test public void gitbug463() {
    	expectedExit = 0;
        helpTCF("test/gitbug463","test/gitbug463", "-cp", "test/gitbug463");
    }
    
    @Test public void gitbug463a() {
    	expectedExit = 0;
        helpTCF("test/gitbug463a","test/gitbug463a", "-cp", "test/gitbug463a");
    }
    
    @Test public void gitbug444() {
    	expectedExit = 0;
        helpTCF("test/gitbug444","test/gitbug444", "-cp", "test/gitbug444");
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

    @Test public void gitbug474() {
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
        helpTCG();  // NOTE: Uses a custom instance of ByteBuffer.jml, which made the original bug
    }

    @Test public void gitbug480() {
    	expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug497() {
    	expectedExit = 1;
        helpTCG();
    }

    @Test public void gitbug498() {
    	expectedExit = 0;
        helpTCG();
    }

    @Test public void gitbug499() {
    	expectedExit = 1;
        helpTCG();
    }

    @Ignore
    @Test public void gitbug500a() {
        helpTCG();
    }

    @Ignore
    @Test public void gitbug500b() {
        helpTCG();
    }

    @Test public void gitbug500c() {
        helpTCG("-rac");  // Just RAC compilation - RAC compile crash
    }

    @Test public void gitbug502() {
        helpTCG();
    }

    @Test public void gitbug503() {
        helpTCG();
    }

    @Test public void gitbug535() {
        helpTCG();
    }

    @Test public void gitbug538() {
        helpTCG();
    }

    @Test public void gitbug539() {
        helpTCG();
    }

    @Test public void gitbug540() {
        helpTCG();
    }

    @Test public void gitbug543() {
        helpTCG();  // FIXME - problems with quantification over arrays
    }

    @Test public void gitbug545() {
        helpTCG();
    }

    @Test public void gitbug548() {
        helpTCG("-nullableByDefault");
    }
    
    @Test public void gitbug550() {
        helpTCG();
    }
    
    @Test public void gitbug554() {
        helpTCG();
    }
    
    @Test public void gitbug555() {
        helpTCG("-nullableByDefault");
    }
    


    @Test public void gitbug518() {
    	expectedExit = 1;
        helpTCG("-check");  // Just checking
    }

    @Test public void gitbug528() {
        helpTCG("-strictJML","-check");  // Just checking
    }

    @Test public void gitbug529() {
        helpTCG("-rac");  // Just RAC compilation  // FIXME - try running also
    }

    // Check everything in apache commons library!
    @Test @Ignore public void gitbug481() {
    	expectedExit = 0;
        helpTCF("test/gitbug481b","test/gitbug481", "-cp", "test/gitbug481b","-progress");
    }

    // Just one method, but parse and typecheck all files first
    @Ignore 
    @Test public void gitbug481c() {
    	expectedExit = 0;
        helpTCF("test/gitbug481b","test/gitbug481c", "-cp", "test/gitbug481b","-method=org.apache.commons.math3.linear.ArrayFieldVector.getEntry");
    }

    // Just one method in one file
    @Ignore // FIXME - timeout
    @Test public void gitbug481b() {
    	expectedExit = 0;
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481b", "-cp", "test/gitbug481b","-method=org.apache.commons.math3.linear.ArrayFieldVector.getEntry","-no-staticInitWarning");
    }

    static String p = "org.apache.commons.math3.linear.ArrayFieldVector.";
    static String m1 = p + "ArrayFieldVector(org.apache.commons.math3.Field<T>)";
    static String m2 = p + "ArrayFieldVector(org.apache.commons.math3.Field<T>,int)";
    static String m3 = p + "ArrayFieldVector(int,T)";
    static String m4 = p + "ArrayFieldVector(org.apache.commons.math3.linear.ArrayFieldVector<T>,boolean)";
    static String m5 = p + "ArrayFieldVector(org.apache.commons.math3.linear.ArrayFieldVector<T>,org.apache.commons.math3.linear.ArrayFieldVector<T>)";
    static String m6 = p + "ArrayFieldVector(org.apache.commons.math3.linear.FieldVector<T>,org.apache.commons.math3.linear.FieldVector<T>)";
    static String m7 = p + "ArrayFieldVector(org.apache.commons.math3.linear.FieldVector<T>,T[])";
    static String m8 = p + "ArrayFieldVector(T[],org.apache.commons.math3.linear.ArrayFieldVector<T>)";
    static String m9 = p + "ArrayFieldVector(T[],org.apache.commons.math3.linear.FieldVector<T>)";
    static String m10 = p + "ArrayFieldVector(T[],T[])";
    
    static String all = m1+";"+m2+";"+m3+";"+m4+";"+m5+";"+m6+";"+m7+";"+m8+";"+m9+";"+m10;
    
    @Test public void gitbug481a1() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a1", "-cp", "test/gitbug481b","-method="+m1,"-no-staticInitWarning");
    }

    @Test public void gitbug481a2() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a2", "-cp", "test/gitbug481b","-method="+m2,"-no-staticInitWarning");
    }

    @Test public void gitbug481a3() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a3", "-cp", "test/gitbug481b","-method="+m3,"-no-staticInitWarning");
    }

    @Ignore // FIXME - timeout
    @Test public void gitbug481a4() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a4", "-cp", "test/gitbug481b","-method="+m4,"-no-staticInitWarning");
    }

    @Ignore // FIXME - timeout
    @Test public void gitbug481a5() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a5", "-cp", "test/gitbug481b","-method="+m5,"-no-staticInitWarning");
    }

    @Ignore // FIXME - timeout
    @Test public void gitbug481a6() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a6", "-cp", "test/gitbug481b","-method="+m6,"-no-staticInitWarning");
    }

    @Ignore // FIXME - timeout
    @Test public void gitbug481a7() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a7", "-cp", "test/gitbug481b","-method="+m7,"-no-staticInitWarning");
    }

    @Test public void gitbug481a8() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a8", "-cp", "test/gitbug481b","-method="+m8,"-no-staticInitWarning");
    }

    @Ignore // FIXME - timeout
    @Test public void gitbug481a9() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a9", "-cp", "test/gitbug481b","-method="+m9,"-no-staticInitWarning");
    }

    @Ignore // FIXME - timeout
    @Test public void gitbug481a10() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a10", "-cp", "test/gitbug481b","-method="+m10,"-no-staticInitWarning");
    }

    @Ignore // FIXME - timeout
    @Test public void gitbug481arest() {
    	expectedExit = 1;
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a", "-cp", "test/gitbug481b","-exclude="+all,"-no-staticInitWarning");
    }

    @Test public void gitbug482() {
    	expectedExit = 0;
        helpTCF("test/gitbug482/checkers/src/main/java/checkers/*.java","test/gitbug482", "-cp", "test/gitbug482/checkers/src/main","-check"); // check only, not esc
    }

    @Test public void gitbug556() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug557() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug558() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug558a() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug558b() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug559() {
        expectedExit = 0;
        helpTCG("-escExitInfo");
    }
    
    @Test public void gitbug559a() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug560() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug567() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug567a() {
        expectedExit = 0;
        helpTCF("test/gitbug567","test/gitbug567a","-code-math=java");
    }
    
    @Test public void gitbug567b() {
        expectedExit = 0;
        helpTCF("test/gitbug567","test/gitbug567b","-code-math=safe");
    }
    
    @Test public void gitbug567c() {
        expectedExit = 0;
        helpTCF("test/gitbug567","test/gitbug567c","-code-math=bigint");
    }
    
    @Test public void gitbug572() {
        expectedExit = 1;
        helpTCG();
    }
    
    // The .jml file is on the command-line, which caused a crash, now fixed
    @Test public void gitbug573() {
        expectedExit = 0;
        helpTCF("test/gitbug573/pckg/A.jml","test/gitbug573","-sourcepath","test/gitbug573");
    }
    
    @Test public void gitbug573a() {
        expectedExit = 0;
        helpTCG();
    }
    
    // Here .jml is on the command-line, but the .java does not exist
    @Test public void gitbug573b() {
        expectedExit = 1;
        helpTCF("test/gitbug573b/pckg/A.jml","test/gitbug573b","-sourcepath","test/gitbug573b");
    }
    
    @Test public void gitbug573c() {
        expectedExit = 1;
        helpTCF("test/gitbug573c/java/lang/Integer.jml","test/gitbug573c","-sourcepath","test/gitbug573c","-no-internalSpecs");
    }
    
    @Test public void gitbug574() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug575() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug578() {
        expectedExit = 0;
        helpTCG();
    }
    
    // Double operations (sqrt) not yet implemented
    @Ignore
    @Test public void gitbug580() {
        expectedExit = 0;
        helpTCG();
    }
    
    @Test public void gitbug582() {
        expectedExit = 0;
        helpTCG("-purityCheck");
    }
    
    @Test
    public void gitbug589() {
    	expectedExit = 1;
        helpTCG();
    }
    
    @Test
    public void gitbug591() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug593() {
    	expectedExit = 0;
        helpTCG("-check");
    }
    
    @Test
    public void gitbug594() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug596a() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug596b() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug596c() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug596d() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug597() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug598() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug598a() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug600() {
    	expectedExit = 0;
        helpTCG("-rac","-racCheckAssumptions","-racPreconditionEntry"); // RAC compile crash
    }
    
    @Test
    public void gitbug601() {
    	expectedExit = 0;
        helpTCG();  // FIXME Unimplemented floating point 
    }
    
    @Test
    public void gitbug602() {
    	expectedExit = 0;
        helpTCG("-Xlint:unchecked","-Xlint:sunapi");
    }
    
    @Test
    public void gitbug603() {
    	expectedExit = Main.Result.CMDERR.exitCode;
        helpTCG("-Xmaxwarns=100","-quiet"); // Arguments are part of the test
    }
    
    @Test
    public void gitbug604() {  // FIXME requires implementatino of \not_assigned
    	expectedExit = 0;
        helpTCG("-code-math=safe","-method=AbsInterval.add");
    }
    
    @Test
    public void gitbug605() {
    	expectedExit = 0;
        helpTCG("-code-math=safe");
    }
    
    @Test
    public void gitbug606() {
    	expectedExit = 0;
        helpTCG("-code-math=safe");
    }
    
    @Test
    public void gitbug607() {
    	expectedExit = 0;
        helpTCG("-show","-method=x"); // Arguments are part of the test
    }
    
    @Test
    public void gitbug608() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug610() {
    	expectedExit = 0;
        helpTCG("-code-math=safe");
    }
    
    @Test
    public void gitbug611() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug613() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug615() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug618() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug621() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug621a() { // Original bug
    	expectedExit = 0;
        helpTCG("-method=testMethod"); // Limited to this one method
    }
    
    @Test
    public void gitbug622() {
    	expectedExit = 0;
        helpTCG("-staticInitWarning");
    }
    
    @Test
    public void gitbug622a() {
    	expectedExit = 0;
        helpTCG("-no-staticInitWarning");
    }
    
    @Test
    public void gitbug623() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug626() {
    	expectedExit = 0;
        helpTCG("-subexpressions");//,"-show","-method=findFirstSetLoop"); // -subexpressions is part of the test
    }
    
    @Test
    public void gitbug627() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug630() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug630a() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug634() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug635() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug636() {
    	expectedExit = 1;
        helpTCG();
    }
    
    @Test
    public void gitbug666() {
    	expectedExit = 0;
        helpTCG("-show=all","-method=pow");
    }
    
    public void gitbug888() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void gitbug999() {
    	expectedExit = 0;
        helpTCG();
    }
    
    @Test
    public void rise4fun() {
        expectedExit = 0;
        helpTCGNoOptions();
    }

}

