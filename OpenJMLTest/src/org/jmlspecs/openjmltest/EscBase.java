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


public abstract class EscBase extends JmlTestCase {

    public static final String OpenJMLDemoPath = "../../OpenJMLDemo";

    @Rule public TestName testname = new TestName();
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

    /** The parameters must be a String[] and a String */
    static public Collection<String[]> parameters() {
        return solversOnly();
    }
    
    static public Collection<String[]> solversOnly() {
        return makeParameters(solvers);
    }
    
//    public static final String[] minQuantOptions = new String[]{"-no-minQuant","-minQuant"};
    
    static public  Collection<String[]> solvers(java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) {
            data.add(new String[]{s});
        }
        return data;
    }

    static public  Collection<String[]> optionsAndSolvers(String[] options, java.util.List<String> solvers) {
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
    
//    static public void addOptionsToArgs(String options, java.util.List<String> args) {
//        if (options != null) {
//            if (options.indexOf(',')>= 0) {
//            	for (String o: options.split(",")) if (!o.isEmpty()) args.add(o);
//            } else {
//            	for (String o: options.split(" ")) if (!o.isEmpty()) args.add(o);
//            }
//        }
//    }
    
    public void addOptions(String options) {
        if (options != null) {
            if (options.indexOf(',')>= 0) {
            	addOptions(options.split(","));
            } else {
            	addOptions(options.split(","));
            }
        }
    }
    

    /** options is a comma- or space-separated list of options to be added */
    protected String options;
    protected String solver;
    protected boolean captureOutput = false; // FIXME - why isn't true the default 
    
    /** options is a comma- or space-separated list of options to be added */
    public EscBase() {
        this.options = null;
        this.solver = "z3_4_3";
    }
    
    /** options is a comma- or space-separated list of options to be added */
    public EscBase(String options, String solver) {
        this.options = options;
        this.solver = solver;
    }
    
//    public void printDiagnostics() {
//        System.out.println("SOLVER: " + solver + " " + options);
//        super.printDiagnostics();
//    }

    protected static String z = java.io.File.pathSeparator;
    protected static String testspecpath1 = "$A"+z+"$B";
    protected static String testspecpath;
    
    // Set this field to the expected exit value. 
    // 0: only warnings and static checking errors, not parsing or type errors
    // 1: parsing or type errors
    // -1: don't check the exit value
    protected int expectedExit = 0;
    protected boolean noAssociatedDeclaration;
    protected String[] args;

    @Override
    public void setUp() throws Exception {
        if (captureOutput) collectOutput(true);
        testspecpath = testspecpath1;
        ignoreNotes = true;
        super.setUp(); // Uses ignoreNotes
        addOptions("--specs-path",   testspecpath);
        addOptions("--command","esc");
        addOptions("-keys","NOARITH");
        addOptions("--no-purity-check");
        addOptions("--timeout=300"); // seconds
        addOptions("-jmltesting");
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

    /** Runs an --esc test on the file named in 'sourceDirOrFileName' (ofr if it is a folder, all the files in it), 
     * putting the actual output in folder 'outDir' and comparing with expected files also in 'outDir'.
     * Default options are setup in EscBase.setupForFiles().  The options in 'opts' are appended to them. 
     * **/
    public void escOnFiles(String sourceDirname, String outDir, String ... opts) {
        boolean print = false;
        try {
            java.util.List<String> args = setupForFiles(sourceDirname, outDir, opts);
            String actCompile = outDir + "/actual";
            new File(actCompile).delete();
            PrintWriter pw = new PrintWriter(actCompile);
            int ex = -1;
            try {
                //System.out.println("ARGS " + args);
                ex = org.jmlspecs.openjml.Main.execute(pw,null,null,args.toArray(new String[args.size()]));
            } finally {
                pw.close();
            }

            String diffs = outputCompare.compareFiles(outDir + "/expected", actCompile);
            int n = 0;
            while (diffs != null) {
                n++;
                String name = outDir + "/expected" + n;
                if (!new File(name).exists()) break;
                diffs = outputCompare.compareFiles(name, actCompile);
            }
            if (diffs != null) {
                System.out.println("TEST DIFFERENCES: " + testname.getMethodName());
                System.out.println(diffs);
                fail("Files differ: " + diffs);
            }
            
            if (expectedExit != -1 && ex != expectedExit) fail("Compile ended with exit code " + ex);
            new File(actCompile).delete();

        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            throw e;
        } finally {
            // Should close open objects
        }
    }

    public java.util.List<String> setupForFiles(String sourceDirOrFilename, String outDir, String ... opts) {
        new File(outDir).mkdirs();
        java.util.List<String> args = new LinkedList<String>();
        args.add("-g");
        args.add("--esc");
        args.add("--no-purity-check");
        args.add("-jmltesting");
        args.add("--progress");
        args.add("--timeout=300");
        args.add("--code-math=java");
        args.add("--no-warn=implicit-everything"); // Because too many tests would issue warnings if enabled
        if (!new File(sourceDirOrFilename).isFile()) args.add("--dir");
        args.add(sourceDirOrFilename);
        if (solver != null) args.add("--prover="+solver);
        args.addAll(Arrays.asList(opts));
        return args;
    }
    
    @Override
    public void tearDown() throws Exception {
        super.tearDown();
        captureOutput = false;
        //MethodProverSMT.benchmarkName = null;
    }

    protected void helpTCX2(String classname, String s, String classname2, String s2, Object... list) {
        try {
            String filename = classname.replace(".","/")+".java";
            JavaFileObject f = new TestJavaFileObject(filename,s);
            String filename2 = classname2.replace(".","/")+".java";
            JavaFileObject f2 = new TestJavaFileObject(filename2,s2);
            Log.instance(context).useSource(f);
//            helpTCXB(List.of(f,f2),list);
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    protected void helpTCX(String classname, String s, Object... expectedResults) {
        try {
            String filename = classname.replace(".","/") +".java"; 
            JavaFileObject f = new TestJavaFileObject(filename,s);
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
    
    protected OneOf oneof(Object ... list) { return new OneOf(list); }
    protected AnyOrder anyorder(Object ... list) { return new AnyOrder(list); }
    protected Optional optional(Object ... list) { return new Optional(list); }
    protected Seq seq(Object ... list) { return new Seq(list); }
    

}
