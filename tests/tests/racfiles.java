package tests;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.junit.Test;

/** These tests check running RAC on files in the file system, comparing the
 * output against expected files. These tests are a bit easier to create, since 
 * the file and output do not have to be converted into Strings; however, they
 * are not as easily read, since the content is tucked away in files, rather 
 * than immediately there in the test class.
 * <P>
 * To add a new test:
 * <UL>
 * <LI> create a directory containing the test files as a subdirectory of 
 * 'testfiles'
 * <LI> add a test to this class - typically named similarly to the folder
 * containing the source data
 * </UL>
 */

public class racfiles extends RacBase {


    
    /** The command-line to use to run RACed programs - note the inclusion of the
     * RAC-compiled JDK library classes ahead of the regular Java libaray classes
     * in the boot class path. (This may not work on all platforms)
     */
    String[] sysrac = new String[]{jdk, "-classpath","bin"+z+"bin-runtime"+z+"testdata",null};

    @Override
    public void setUp() throws Exception {
        rac = sysrac;
        jdkrac = true;
        super.setUp();
    }

    /** This method does the running of a RAC test.  No output is
     * expected from running openjml to produce the RACed program;
     * the number of expected diagnostics is set by 'expectedErrors'.
     * @param dirname The directory containing the test sources, a relative path
     * from the project folder
     * @param classname The fully-qualified classname for the test class (where main is)
     * @param list any expected diagnostics from openjml, followed by the error messages from the RACed program, line by line
     */
    public void helpTCF(String dirname, String classname, String ... opts) {
        boolean print = false;
        StreamGobbler out=null,err=null;
        try {
            String actCompile = dirname + "/actual-compile";
            String actRun = dirname + "/actual-run";
            new File(actCompile).delete();
            new File(actRun).delete();
            List<String> args = new LinkedList<String>();
            args.add("-rac");
            args.add("-d");
            args.add("testdata");
            args.add("-noPurityCheck");
            args.add("-dir");
            args.add(dirname);
            args.addAll(Arrays.asList(opts));
            
            PrintWriter pw = new PrintWriter(actCompile);
            int ex = org.jmlspecs.openjml.Main.execute(pw,null,null,args.toArray(new String[args.size()]));
            pw.close();
            
            String diffs = compareFiles(dirname + "/expected-compile", actCompile);
            if (diffs != null) {
                System.out.println(diffs);
                fail("Files differ: " + diffs);
            } else {
                new File(actCompile).delete();
            }
            if (ex != expectedExit) fail("Compile ended with exit code " + ex);

            if (rac == null) rac = defrac;
            rac[rac.length-1] = classname;
            Process p = Runtime.getRuntime().exec(rac);
            
            out = new StreamGobbler(p.getInputStream());
            err = new StreamGobbler(p.getErrorStream());
            out.start();
            err.start();
            if (timeout(p,10000)) { // 10 second timeout
                fail("Process did not complete within the timeout period");
            }
            ex = p.exitValue();
            String output = "OUT:" + eol + out.input() + eol + "ERR:" + eol + err.input();
            if (print) System.out.println(output);
            diffs = compareText(dirname + "/expected-run",output);
            if (diffs != null) {
                BufferedWriter b = new BufferedWriter(new FileWriter(actRun));
                b.write(output);
                b.close();
                System.out.println(diffs);
                fail("Unexpected output: " + diffs);
            }
            if (ex != expectedRACExit) fail("Execution ended with exit code " + ex);

        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            throw e;
        } finally {
            // Should close open objects
        }
    }


    /** Testing using system specs */
    @Test
    public void test1() {
        expectedExit = 0;
        expectedRACExit = 0;
        helpTCF("testfiles/rac1","Bug1","-noInternalSpecs");
    }

    /** Testing using system specs */
    @Test  // FIXME - problems with library specs
    public void test1a() {
        expectedExit = 0;
        expectedRACExit = 0;
        helpTCF("testfiles/rac1a","Bug1");
    }


}
