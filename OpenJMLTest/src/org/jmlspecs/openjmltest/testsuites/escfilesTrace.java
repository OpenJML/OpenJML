package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.fail;

import java.io.*;
import java.util.*;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBase;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

/** These tests check running ESC on files in the file system, comparing the
 * output against expected files. These tests are a bit easier to create, since 
 * the file and output do not have to be converted into Strings; however, they
 * are not as easily read, since the content is tucked away in files, rather 
 * than immediately there in the test class.
 * <P>
 * To add a new test:
 * <UL>
 * <LI> create a directory containing the test files as a subdirectory of 
 * 'test'
 * <LI> add a test to this class - typically named similarly to the folder
 * containing the source data
 * </UL>
 */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
@Ignore // FIXME - improve and stabilize trace output
public class escfilesTrace extends EscBaseFiles {

    boolean enableSubexpressions = false;
    
    @Override
    public void setUp() throws Exception {
        super.setUp();
    }

    // FIXME _ just use EscBaseFiles.setupForFiles ?
    public java.util.List<String> setupForFiles(String sourceDirname, String outDir, String ... opts) {
    	ignoreNotes = true;
        new File(outDir).mkdirs();
        java.util.List<String> args = new LinkedList<String>();
        args.add("--esc");
        args.add("-jmltesting");
        if (new File(sourceDirname).isDirectory()) args.add("--dir");
        args.add(sourceDirname);
        if (solver != null) args.add("--prover="+solver);
        //addOptionsToArgs(options,args);        
        args.addAll(Arrays.asList(opts));
        return args;
    }

    String OpenJMLDemoNonPublicPath = "../OpenJMLDemo"; // FIXME - get rid of this - wrong anyway

    @Test 
    public void escDMZCashTrace() {
        expectedExit = 0;
        helpEscFile(OpenJMLDemoNonPublicPath + "/src/dmz2","test/escDMZCashTrace","--subexpressions","--method=dmz2.Cash.Cash","-escMaxWarnings=1","-jmltesting");
    }



    @Test // @Ignore // Ignoring for now because the output is too volatile, even if correct - lots of paths that can be found in various orders
    public void escDemoPaths() {
        expectedExit = 0;
        helpEscFile(OpenJMLDemoPath + "/src/openjml/demo/Paths.java","test/escDemoPaths","--subexpressions","--progress");
    }

    @Test 
    public void escDemoChangeCase() {
        expectedExit = 0;
        helpEscFile(OpenJMLDemoPath + "/src/openjml/demo/ChangeCase.java","test/escDemoChangeCase","--progress","--method=changeCase","-escMaxWarnings=1","--subexpressions","-jmltesting");
    }

    @Test
    public void escTrace() {
        expectedExit = 0;
        helpEscFile("test/escTrace","test/escTrace",
                "--method=m","-escMaxWarnings=1",enableSubexpressions ? "--subexpressions" : "");
    }

    @Test
    public void escTrace2() {
        expectedExit = 0;
        helpEscFile("test/escTrace2","test/escTrace2","--method=m", enableSubexpressions ? "--subexpressions" : "");
    }

    @Test
    public void escTrace3() {
        expectedExit = 0;
        helpEscFile("test/escTrace3","test/escTrace3","--progress", enableSubexpressions ? "--subexpressions" : "", "-jmltesting");
    }

    @Test
    public void escTrace4() {
        expectedExit = 0;
        helpEscFile("test/escTrace4","test/escTrace4","--method=m","--subexpressions","--progress");
    }

    @Test
    public void escTrace5() {
        expectedExit = 0;
        helpEscFile("test/escTrace5","test/escTrace5","--method=m","--progress", enableSubexpressions ? "--subexpressions" : "","-jmltesting");
    }

    @Test
    public void escTrace6() {
        expectedExit = 0;
        helpEscFile("test/escTrace6","test/escTrace6","--progress", "--subexpressions","-jmltesting");
    }

    @Test
    public void escTraceLoops() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceLoops","--method=mgood","--progress", "--subexpressions","-jmltesting");
    }

    @Test
    public void escTraceLoops1() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceLoops1","--method=m1","--subexpressions","--progress","-jmltesting");
    }

    @Test
    public void escTraceLoops2() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceLoops2","--method=m2","--subexpressions","--progress");
    }

    @Test
    public void escTraceLoops3() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceLoops3","--method=m3","--progress", enableSubexpressions ? "--subexpressions" : "");
    }

    @Test
    public void escTraceLoops4() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceLoops4","--method=m4","--progress", enableSubexpressions ? "--subexpressions" : "");
    }

    @Test
    public void escTraceLoops5() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceLoops5","--method=m5","--subexpressions","--progress","-jmltesting");
    }

    @Test
    public void escTraceLoops6() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceLoops6","--method=m6","--subexpressions","--progress");
    }

    @Test
    public void escTraceWhile() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceWhile","--method=mwhile","--subexpressions","--progress","-jmltesting");
    }

    @Test
    public void escTraceWhile1() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceWhile1","--method=mwhile1","--subexpressions","--progress");
    }

    @Test
    public void escTraceWhile2() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceWhile2","--method=mwhile2","--subexpressions","--progress");
    }

    @Test
    public void escTraceDo() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceDo","--method=mdo","--subexpressions","--progress","-jmltesting");
    }

    @Test
    public void escTraceDo1() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceDo1","--method=mdo1","--subexpressions","--progress","-jmltesting");
    }

    @Test
    public void escTraceDo2() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceDo2","--method=mdo2","--subexpressions","--progress");
    }

    @Test
    public void escTraceForeach() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceForeach","--method=mforeach","--subexpressions","--progress");
    }

    @Test
    public void escTraceForeach1() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceForeach1","--method=mforeach1","--subexpressions","--progress");
    }

    @Test
    public void escTraceForeach2() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceForeach2","--method=mforeach2","--subexpressions","--progress");
    }

    @Test
    public void escTraceForeach3() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceForeach3","--method=mforeach3","--subexpressions","--progress","-jmltesting");
    }

    @Test
    public void escTraceForeach4() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceForeach4","--method=mforeach4","--subexpressions","--progress");
    }

    @Test
    public void escTraceForeach5() {
        expectedExit = 0;
        helpEscFile("test/escTraceLoops","test/escTraceForeach5","--method=mforeach5","--subexpressions","--progress");
    }

    @Test
    public void escTraceBS() {
        expectedExit = 0;
        helpEscFile("test/escTraceBS","test/escTraceBS","--subexpressions","--progress");
    }
}
