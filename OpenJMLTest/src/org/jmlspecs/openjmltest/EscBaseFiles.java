package org.jmlspecs.openjmltest;

import static org.junit.Assert.*;

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
import org.jmlspecs.openjml.esc.MethodProverSMT;
import org.jmlspecs.openjmltest.OutputCompare.*;
import org.junit.Rule;
import org.junit.rules.TestName;
import org.junit.rules.Timeout;
import org.junit.runners.Parameterized.Parameters;

import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

/** This is a superclass for all testcases whose individual tests consist of running esc on a folder of files,
 *  comparing the test output to expected text in an 'expected' file.
 */
public abstract class EscBaseFiles extends EscBase {

    /** options is a comma- or space-separated list of options to be added */
    public EscBaseFiles() {
        super();
    }
    
    /** options is a comma- or space-separated list of options to be added */
    public EscBaseFiles(String options, String solver) {
        super(options, solver);
    }
    // FIXME - the options set in the above constructor are not used
    

    @Override
    public void setUp() throws Exception {
        super.setUp();
        expectedExit = -1;
    }
    
    /** Sets a common initial set of options for these file-based tests */
    public java.util.List<String> collectArgs(String sourceDirOrFilename, String outDir, String ... opts) {
        new File(outDir).mkdirs();
        java.util.List<String> args = new LinkedList<String>();
        args.add("-g");
        args.add("--esc");
        args.add("-jmltesting");
        args.add("--progress");
        args.add("--timeout=300");
//        args.add("--code-math=java");
        args.add("--no-warn=implicit-everything"); // Because too many tests would issue warnings if enabled
        if (!new File(sourceDirOrFilename).isFile()) args.add("--dir");
        args.add(sourceDirOrFilename);
        if (solver != null) args.add("--prover="+solver);
        args.addAll(Arrays.asList(opts));
        return args;
    }

    
    /** Put here any test-specific additions to the class path */
    protected String cpathAddition = "";


    
    
    /** runs a test in the folder with the given name, with the classpath set to that folder,
     * placing the output in an 'actual' file in that same folder
     * and comparing to one or more 'expected' files in that folder; the additional arguments are test-specific 
     * openjml options, which are appended to those set in 'setupForFiles'
     * @param testDirname
     * @param opts
     */
    public void helpTF(String testDirname, String ... opts) {
        String d = "test/" + testDirname;
        String[] firstopts = new String[]{
                "-classpath", d 
                ,"--check-feasibility=precondition,reachable,exit,spec"
 //               ,"--code-math=bigint" // Just to avoid overflow errors in these tests // FIXME - causes feasibility problem
                ,"--spec-math=bigint"
        };
        String[] newopts = new String[opts.length+firstopts.length];
        System.arraycopy(firstopts,0,newopts,0,firstopts.length);
        System.arraycopy(opts,0,newopts,firstopts.length,opts.length);
        helpTCF(d,d,newopts);
    }
    
    /** Executes a test in which (1) the name of the calling method is the name of the test and
     * also the name of the test directory, (2) the classpath is that same directory, (3) all the
     * .java files in that directory are processed, (4) any base options in collectArgs() and added
     * here in helpTG and supplemented by any arguments to helpTG.
     * @param opts
     */
    public void helpTG(String ... opts) {
        String dir = "test/" + getTestName();
        var a = new LinkedList<String>();
        a.add("-cp"); 
        a.add(dir);
        a.add("--code-math=safe");
        a.add("--spec-math=bigint");
        a.add("--check-feasibility=precondition,reachable,exit,spec");
        a.addAll(Arrays.asList(opts));
        escOnFiles(dir, dir, a.toArray(new String[a.size()]));
    }

    /** runs a test whose source material is in the JMLDemo repo */ 
    public void helpDemoFile(String testFilename, String outdir, String ... opts) {
        int k = testFilename.lastIndexOf('/');
        String file = OpenJMLDemoPath + "/src/openjml/" + testFilename;
        String dir = OpenJMLDemoPath + "/src/openjml/" + testFilename.substring(0,k);
        String[] newopts = new String[opts.length+2];
        newopts[0] = "-classpath";
        newopts[1] = dir;
        System.arraycopy(opts,0,newopts,2,opts.length);
        helpTCF(file,"test/" + outdir,newopts);
    }

    /** runs a test whose source material is in the JMLDemo repo */ 
    public void helpDemo(String testDirname, String outdir, String ... opts) {
        String d = OpenJMLDemoPath + "/src/openjml/" + testDirname;
        String[] newopts = new String[opts.length+2];
        newopts[0] = "-classpath";
        newopts[1] = d;
        System.arraycopy(opts,0,newopts,2,opts.length);
        helpTCF(d,"test/" + outdir,newopts);
    }

    /** Runs an --esc test on the files in folder 'sourceDirName', putting the actual output
     * in folder 'outDir' and comparing with expected files also in 'outDir'.
     * Default options are setup in setupForFiles().  The options in 'opts' are appended to them. 
     * @param sourceDirname
     * @param outDir
     * @param opts
     */
    public void helpTCF(String sourceDirname, String outDir, String ... opts) {
        escOnFiles(sourceDirname,outDir,opts);
    }

    /** Runs an --esc test on the file named in 'sourceDirOrFileName' (or if it is a folder, all the files in that folder), 
     * putting the actual output in folder 'outDir' and comparing with expected files also in 'outDir'.
     * Default options are setup in EscBase.setupForFiles().  The options in 'opts' are appended to them. 
     * **/
    public void escOnFiles(String sourceDirname, String outDir, String ... opts) {
        boolean print = false;
        String actCompile = outDir + "/actual";
        new File(actCompile).delete();
        try (PrintWriter pw = new PrintWriter(actCompile)) {
            java.util.List<String> args = collectArgs(sourceDirname, outDir, opts);

            //this.out.println("ARGS " + args);
            int ex = org.jmlspecs.openjml.Main.execute(pw,null,null,args.toArray(new String[args.size()]));

            String diffs = null;
            var files = new File(outDir).list((f,s)->s.startsWith("expected") && !s.endsWith("-compile") && !s.endsWith(("-run")));
            assertTrue("There are no expected output files in " + outDir, 0 != files.length);
            for (String name: files) {
                String expectedFile = outDir + "/" + name;
                diffs = outputCompare.compareFiles(expectedFile, actCompile);
                if (diffs == null) {
                    if (files.length != 1) this.out.println("Matched: " + name);
                    new File(actCompile).delete();
                    if (expectedExit == -1) {
                        String[] command = {"/bin/bash", "-c", "grep -q -E '^[0-9]* error[s]?$'  " + expectedFile };
                        ProcessBuilder processBuilder = new ProcessBuilder(command);
                        Process process = processBuilder.start();
                        int exitCode = process.waitFor();
                        if (exitCode == 0) {
                            //System.out.println("Found errors " + expectedFile);
                            expectedExit = 1;
                        }
                    }
                    if (expectedExit == -1) {
                        String[] command = {"/bin/bash", "-c", "grep -q -E '^[0-9]* verification failure[s]?$' " + expectedFile };
                        ProcessBuilder processBuilder = new ProcessBuilder(command);
                        Process process = processBuilder.start();
                        int exitCode = process.waitFor();
                        if (exitCode == 0) {
                            //System.out.println("Found verification failures " + expectedFile);
                            expectedExit = 6;
                        }
                    }
                    if (expectedExit == -1) {
                        String[] command = {"/bin/bash", "-c", "grep -q -E '^[0-9]* warning[s]?$'  " + expectedFile };
                        ProcessBuilder processBuilder = new ProcessBuilder(command);
                        Process process = processBuilder.start();
                        int exitCode = process.waitFor();
                        if (exitCode == 0) {
                            //System.out.println("Found warnings " + expectedFile);
                            expectedExit = 0;
                        }
                    }
                    if (expectedExit == -1) {
                        expectedExit = 0;
                    }
                    break;
                }
            }
            if (diffs != null) {
                this.out.println("TEST DIFFERENCES: " + actCompile);
                // The output can be voluminous, partly because the comparison algorithm is not smart, so we just truncate it
                // at an arbitrary length
                this.out.println(diffs.substring(0, Math.min(300, diffs.length())));
                fail("Files differ"); // Does not return, so appears to be not covered by Jacoco
            }
            
            if (expectedExit != -1) {
                assertEquals("Compile ended with unexpected exit code:", expectedExit, ex);
            }

        } catch (Exception e) {
            e.printStackTrace(this.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            throw e; // These exceptions come from test failures and signal the JUnit infrastructure of the failure
        }
    }

}
