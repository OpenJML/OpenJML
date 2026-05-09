package org.jmlspecs.openjmltest;

import static org.junit.Assert.*;

import java.io.File;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Collection;
import java.util.concurrent.TimeUnit;
import java.util.stream.Stream;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjmltest.OutputCompare.*;
import org.junit.Rule;
import org.junit.rules.TestName;
import org.junit.rules.Timeout;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.MockJavaFileObject;

import com.sun.tools.javac.util.List;


public abstract class EscBase extends JmlTestSuite {
    
    // FIXME - either rewrite to use Parameters, or delete all this stuff
    // Might well use Parameters for testing more than one solver; not as likely for different option sets

    // FIXME - this only applies when running a standard Runner, not with the custom OpenJMLTestRunner
    /** This JUnit rule sets a timeout on the whole test */
    @Rule public Timeout timeout = new Timeout(10, TimeUnit.MINUTES); // limit on entire test, not on each proof attempt

    protected static boolean runLongTests = System.getProperty("SKIPLONGTESTS") == null;

    static {
        if (!runLongTests) System.out.println("Skipping long-running tests");
    }

    static public java.util.List<String> solvers = java.util.Arrays.asList(new String[]{ 
            "z3_4_3",
//            "z3-4.8",
//            "cvc4-1.8",
//            "cvc5-0.0"
//            "z3_4_7", 
 //           "z3_4_5", 
 //           "z3_4_6", 
 //           "z3_4_3_1", 
//          "z3_4_4", 
//            "cvc4",
            //"yices2",
 //             "yices", 
 //            "simplify" 
            });
    
    static public java.util.List<String> solversWithNull;
    {
        solversWithNull = new LinkedList<String>();
        solversWithNull.add(null);
        solversWithNull.addAll(solvers);
    }

    static public Collection<String[]> parameters() {
        return solversOnly();
    }

    static public Collection<String[]> solversOnly() {
        return makeParameters(solvers);
    }
    
    static public Collection<String[]> solvers(java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) {
            data.add(new String[]{s});
        }
        return data;
    }

    static public Collection<String[]> optionsAndSolvers(String[] options, java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) {
            for (String opts: options) {
                data.add(new String[]{opts,s});
            }
        }
        return data;
    }

    static public Collection<String[]> makeParameters(java.util.List<String> options, java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) {
            for (String option: options) {
                data.add(new String[]{option,s});
            }
        }
        return data;
    }

    static public Collection<String[]> makeParameters(java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) data.add(new String[]{null,s});
        return data;
    }

    static public Collection<String[]> makeParameters(String... solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) data.add(new String[]{null,s});
        return data;
    }
    
    /** options is a comma- or space-separated list of options to be added -- used in the parameterized JUnit tests*/
    protected String options;  // FIXME - remove?run
    /** The name of the solver to be used */
    protected String solver;
    
    // Currently, we are running EscBase tests for a single solver and no options parameter.
    // Any custom options for a test are added using addOptions after setup and before calling helpEsc
    
    public EscBase() {
        this.options = null;
        this.solver = "z3_4_3";
    }
    
    /** options is a comma-separated list of options to be added */
    public EscBase(String options, String solver) {
        this.options = options;
        this.solver = solver;
    }
    
    /** the default specification path used in the tests */
    protected static String testspecpath1 = "$A"+z+"$B";
    /** variable that holds the specification path for each test -- may be set per test (after setUp is called) */
    protected static String testspecpath;
    
    /** Set this field to the expected exit value; -1 means use a default based on the conttent of the expected output
    **/
    protected int expectedExit = 0;

    protected boolean captureOutput = false; // FIXME - why isn't true the default -- explain
    protected boolean checkOutput = true;

    @Override
    public void setUp() throws Exception {
        if (captureOutput) collectSystemOutput(true);
        testspecpath = testspecpath1;
        ignoreNotes = true;
        super.setUp(); // Uses ignoreNotes
        addOptions("--specs-path", testspecpath,
                   "--command","esc",
                   "--keys","NOARITH",
                   "--timeout=300", // seconds
                   "-jmltesting", // filters time-related or user-environment-related material out of test output
                   "--no-warn=implicit-everything"); // Because too many tests would issue warnings if enabled
        addOptions(options);
        if (solver != null) addOptions(JmlOption.PROVER.optionName(),solver);
        expectedExit = 0;
        print = false;
    }
    
    @Override
    public void tearDown() throws Exception {
        super.tearDown();
        captureOutput = false;
        //MethodProverSMT.benchmarkName = null;
    }

    /** Applies ESC to the case where there are two input .java mock files, each consisting of a class name and the input source text;
     * the expectedResults array is a line-by-line list of the expected output.
     */
    protected void helpEsc(String classname, String inputSource, String classname2, String inputSource2, Object... expectedResults) {
        try {
            String filename = classname.replace(".","/")+".java";
            JavaFileObject f = new MockJavaFileObject(filename,inputSource);
            String filename2 = classname2.replace(".","/")+".java";
            JavaFileObject f2 = new MockJavaFileObject(filename2,inputSource2);
            helpEsc(List.<JavaFileObject>of(f,f2),expectedResults);
        } catch (Exception e) {
            e.printStackTrace(out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    /** Applies ESC to a mock file, with the given classname and input contents;
     * the expected results array is a line by line list of the expected output.
     */
    protected void helpEsc(String classname, String inputSource, Object... expectedResults) {
        try {
            String filename = classname.replace(".","/") +".java"; 
            JavaFileObject f = new MockJavaFileObject(filename,inputSource);
            helpEsc(List.<JavaFileObject>of(f), expectedResults);
        } catch (Exception e) {
            e.printStackTrace(out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    /** Applies ESC (with any options already added using addOptions) to the list of files (JavaFileObjects),
     * comparing any diagnostics to the give list of expected results.
     */
    protected void helpEsc(List<JavaFileObject> files, Object... expectedResults) {

        try {
            // Register each file by URI in the existing mockFiles (same object as main.mockFiles),
            // preserving any .jml spec mocks already added via addMockFile().
            for (JavaFileObject jfo : files) mockFiles.addMockByUri(jfo.toUri().normalize(), jfo);
            String[] fileArgs = files.stream().map(javax.tools.JavaFileObject::getName).toArray(String[]::new);
            int ex = main.compile(fileArgs, mockFiles).exitCode;
            int verifyExit = JmlOption.EXITVERIFY.getInt(main.context());
            if (captureOutput) collectSystemOutput(false);
            { 
                if (print) printDiagnostics();
                outputCompare.compareResults(expectedResults,collector,true);
                if (expectedExit == 0) for (Object er: expectedResults) if (er.toString().contains(": verify:")) expectedExit = verifyExit;
                if (ex != expectedExit) fail("Compile ended with exit code " + ex + " but expected " + expectedExit);
            }
            if (captureOutput) {
                var o = output();
                if (print && !o.isEmpty()) out.println("STDOUT:\n" + o);
                var e = errorOutput();
                if (print && !e.isEmpty()) out.println("STDERR:\n" + e);
                if (checkOutput) assertTrue("Did not expect any non-diagnostic output", o.isEmpty() && e.isEmpty());
            }
        } catch (Exception e) {
            { 
                printDiagnostics();
                e.printStackTrace(out);
                fail("Exception thrown while processing test: " + e);
            }
        } catch (AssertionError e) {
            { 
                if (!print && !noExtraPrinting) printDiagnostics();
                throw e;
            }
        }
    }
}
