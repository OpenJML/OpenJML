package org.jmlspecs.openjmltest;

import static org.junit.Assert.fail;

import java.io.File;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.concurrent.TimeUnit;
import java.util.stream.Stream;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.esc.MethodProverSMT;
import org.jmlspecs.openjmltest.OutputCompare.*;
import org.junit.Rule;
import org.junit.rules.TestName;
import org.junit.rules.Timeout;
import org.junit.runners.Parameterized.Parameters;

import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;


public abstract class EscBase extends JmlTestSuite {

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

    static public  Collection<String[]> makeParameters(java.util.List<String> options, java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) {
            for (String option: options) {
                data.add(new String[]{option,s});
            }
        }
        return data;
    }

    static public  Collection<String[]> makeParameters(java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) data.add(new String[]{null,s});
        return data;
    }

    static public  Collection<String[]> makeParameters(String... solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) data.add(new String[]{null,s});
        return data;
    }
    
    public void addOptions(String options) {
        if (options != null) {
            if (options.indexOf(',')>= 0) {
            	addOptions(options.split(","));
            } else {
            	addOptions(options.split(","));
            }
        }
    }

    /** options is a comma- or space-separated list of options to be added -- used in the parameterized JUnit tests*/
    protected String options;
    /** The name of the solver to be used */
    protected String solver;
    
    /** options is a comma- or space-separated list of options to be added -- used in the parameterized JUnit tests*/
    public EscBase() {
        this.options = null;
        this.solver = "z3_4_3";
    }
    
    /** options is a comma- or space-separated list of options to be added */
    public EscBase(String options, String solver) {
        this.options = options;
        this.solver = solver;
    }
    
    /** a typical sepcificatino path used in the tests */
    protected static String testspecpath1 = "$A"+z+"$B";
    /** variable that holds the specification path for each test -- may be set per test */
    protected static String testspecpath;
    
    /** Set this field to the expected exit value. 
    <U><LI> 0: only warnings and static checking errors, not parsing or type errors
    <LI> 1: parsing or type errors
    <LI> -1: don't check the exit value
    </UL> **/
    protected int expectedExit = 0;
    /** Suppresses printing of associated declaration information (to reduce output size) */ // FIXME - perhaps contains user information?
    protected boolean noAssociatedDeclaration;
    protected String[] args; // FIXME - where is this actually used
    protected boolean captureOutput = false; // FIXME - why isn't true the default -- explain

    @Override
    public void setUp() throws Exception {
        if (captureOutput) collectOutput(true);
        testspecpath = testspecpath1;
        ignoreNotes = true;
        super.setUp(); // Uses ignoreNotes
        addOptions("--specs-path", testspecpath);
        addOptions("--command","esc");
        addOptions("--keys","NOARITH");
        addOptions("--no-purity-check");
        addOptions("--timeout=300"); // seconds
        addOptions("-jmltesting"); // filters time-related or user-envirnment-related material out of test output
        addOptions("--no-warn=implicit-everything"); // Because too many tests would issue warnings if enabled
        main.addUncheckedOption("openjml.defaultProver=z3_4");
        addOptions(options);
        if (solver != null) addOptions(JmlOption.PROVER.optionName(),solver);
 //       specs = JmlSpecs.instance(context);
        expectedExit = 0;
        noAssociatedDeclaration = false;
        ignoreNotes = false;
        print = false;
        args = new String[]{};
    }
    
    @Override
    public void tearDown() throws Exception {
        super.tearDown();
        captureOutput = false;
        //MethodProverSMT.benchmarkName = null;
    }

    /** Applies ESC to the case where there are two input .java synthesized files, each consisting of a class name and the input source text;
     * the expecgtedResults array is a line-by-line list of the expected output.
     */
    protected void helpTCX2(String classname, String inputSource, String classname2, String inputSource2, Object... expectedResults) {
        try {
            String filename = classname.replace(".","/")+".java";
            JavaFileObject f = new TestJavaFileObject(filename,inputSource);
            String filename2 = classname2.replace(".","/")+".java";
            JavaFileObject f2 = new TestJavaFileObject(filename2,inputSource2);
            Log.instance(context).useSource(f);
//            helpTCXB(List.of(f,f2),list);
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    /** Applies ESC to a synthesized file, with the given classname and input contents;
     * the expected results array is a line by line list of the expected output.
     */
    protected void helpTCX(String classname, String inputSource, Object... expectedResults) {
        try {
            String filename = classname.replace(".","/") +".java"; 
            JavaFileObject f = new TestJavaFileObject(filename,inputSource);
            Log.instance(context).useSource(f);
            helpTCXB(args,f, expectedResults);
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    protected void helpTCXB(String[] allargs, JavaFileObject f, Object... expectedResults) {
        try {
            int ex = main.compile(allargs, List.<JavaFileObject>of(f)).exitCode;
            if (captureOutput) collectOutput(false);

            synchronized (System.out) { 
                if (print) printDiagnostics();
                outputCompare.compareResults(expectedResults,collector);
                if (expectedExit == 0) for (Object er: expectedResults) if (er.toString().contains(": verify:")) expectedExit = 6;
                if (ex != expectedExit) fail("Compile ended with exit code " + ex);
            }
        } catch (Exception e) {
            synchronized (System.out) { 
                printDiagnostics();
                e.printStackTrace(System.out);
                fail("Exception thrown while processing test: " + e);
            }
        } catch (AssertionError e) {
            synchronized (System.out) { 
                if (!print && !noExtraPrinting) printDiagnostics();
                throw e;
            }
        }
    }

}
