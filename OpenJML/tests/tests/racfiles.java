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

    boolean runrac = true;
    
    /** The command-line to use to run RACed programs - note the inclusion of the
     * RAC-compiled JDK library classes ahead of the regular Java libaray classes
     * in the boot class path. (This may not work on all platforms)
     */
    String[] sysrac = new String[]{jdk, "-classpath","bin"+z+"bin-runtime"+z+"testdata",null};

    @Override
    public void setUp() throws Exception {
        rac = sysrac;
        jdkrac = true;
        runrac = true;
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
    public void helpTCF(String dirname, String outputdir, String classname, String ... opts) {
        boolean print = false;
        StreamGobbler out=null,err=null;
        try {
            String actCompile = outputdir + "/actual-compile";
            String actRun = outputdir + "/actual-run";
            new File(outputdir).mkdirs();
            new File(actCompile).delete();
            new File(actRun).delete();
            List<String> args = new LinkedList<String>();
            args.add("-rac");
            args.add("-d");
            args.add("testdata");
            args.add("-no-purityCheck");
            args.add("-dir");
            args.add(dirname);
            args.addAll(Arrays.asList(opts));
            
            PrintWriter pw = new PrintWriter(actCompile);
            int ex = org.jmlspecs.openjml.Main.execute(pw,null,null,args.toArray(new String[args.size()]));
            pw.close();
            
            String compdiffs = compareFiles(outputdir + "/expected-compile", actCompile);
            if (compdiffs != null) {
                System.out.println(compdiffs);
//                fail("Files differ: " + compdiffs);
            } else {
                new File(actCompile).delete();
            }
            if (ex != expectedExit) fail("Compile ended with exit code " + ex);

            if (runrac) {
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
                String diffs = compareText(outputdir + "/expected-run",output);
                if (diffs != null) {
                    BufferedWriter b = new BufferedWriter(new FileWriter(actRun));
                    b.write(output);
                    b.close();
                    System.out.println(diffs);
                    fail("Unexpected output: " + diffs);
                }
                if (ex != expectedRACExit) fail("Execution ended with exit code " + ex);
            }
            if (compdiffs != null) fail("Files differ: " + compdiffs);

        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            throw e;
        } finally {
            // Should close open objects
        }
    }


    /** Testing without using system specs */
    @Test
    public void test1() {
        expectedExit = 0;
        expectedRACExit = 0;
        helpTCF("testfiles/rac1","testfiles/rac1","Bug1","-noInternalSpecs");
    }

    /** Testing using system specs */
    @Test  // FIXME - problems with library specs - RAC cannot handle ghost variables when it does not compile the class file
    public void test1a() {
        expectedExit = 0;
        expectedRACExit = 0;
        helpTCF("testfiles/rac1a","testfiles/rac1a","Bug1");
    }

    @Test // Originally a Stack overflow because of recursive check of invariant
    public void testBug1() {
        expectedExit = 0;
        expectedRACExit = 1;
        helpTCF("testfiles/racbug1","testfiles/racbug1","Add");
    }

    @Test // Originally a Stack overflow because of recursive check of invariant
    public void testBugStackTrace() {
        expectedExit = 0;
        helpTCF("testfiles/racStackTrace","testfiles/racStackTrace","CantCompileRAC");
    }

    @Test // Originally crashed because of a model method in a library class
    public void testPoint() {
        expectedExit = 0;
        helpTCF("testfiles/racPoint","testfiles/racPoint","Point","-quiet");
    }

    @Test // Originally crashed because of a model method in a library class
    public void testPoint2() {
        expectedExit = 0;
        helpTCF("testfiles/racPoint2","testfiles/racPoint2","Point");
    }

    @Test
    public void testFirstTest() {
        expectedExit = 0;
        helpTCF("testfiles/firstTest","testfiles/firstTest","FirstTest","-racJavaChecks","-racCheckAssumptions");
    }

    @Test
    public void testUniqueList() {
        expectedExit = 0;
        helpTCF("testfiles/uniqueList","testfiles/uniqueList","UniqueList","-racJavaChecks","-racCheckAssumptions");
    }

    @Test 
    public void testUniqueList1() {
        expectedExit = 0;
        helpTCF("testfiles/uniqueListBug1","testfiles/uniqueListBug1","UniqueListBug1","-racJavaChecks","-racCheckAssumptions");
    }

    @Test 
    public void testUniqueList2() {
        expectedExit = 0;
        helpTCF("testfiles/uniqueListBug2","testfiles/uniqueListBug2","UniqueListBug2");
    }

    @Test
    public void testDecimal() {
        expectedExit = 0;
        helpTCF("testfiles/sv_rac","testfiles/sv_rac","sv_rac/Decimal");
    }

    @Test
    public void testDecimal2() {
        expectedExit = 0;
        helpTCF("testfiles/sv_rac_mod","testfiles/sv_rac_mod","sv_rac/Decimal");
    }

    @Test
    public void testbigint() {
        expectedExit = 0;
        helpTCF("testfiles/racbigint","testfiles/racbigint","bigint");
    }

    @Test
    public void testreal() {
        expectedExit = 0;
        helpTCF("testfiles/racreal","testfiles/racreal","real");
    }

    @Test
    public void demoStudent() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/student","testfiles/demoStudent","ExecuteCStudent2","-racJavaChecks","-racCheckAssumptions");
    }

    @Test
    public void testECU() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/ecudemo","testfiles/ecurac","Test","-racJavaChecks","-racCheckAssumptions");
    }

    @Test
    public void purseCardTest() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/purse","testfiles/purse","CardTest");
    }

    @Test
    public void purseModTest() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/purseMod","testfiles/purseMod","CardTest");
    }

    @Test
    public void racTime() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/Time.java","testfiles/racTime","Time");
    }

    @Test
    public void racQueue() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/Queue.java","testfiles/racQueue","Queue");
    }

    @Test
    public void racAddng() {
        rac = new String[]{jdk, "-classpath","bin"+z+"bin-runtime"+z+"testdata"+z+"testfiles/racaddng/jmlunitng.jar",null};
        expectedExit = 0;
        helpTCF("testfiles/racaddng/Add_InstanceStrategy.java","testfiles/racaddng","Add_JML_Test","-cp","bin-runtime;testfiles/racaddng;testfiles/racaddng/jmlunitng.jar");
    }

    @Test
    public void racAddngall() {
        rac = new String[]{jdk, "-classpath","bin"+z+"bin-runtime"+z+"testdata"+z+"testfiles/racaddng/jmlunitng.jar",null};
        expectedExit = 0;
        helpTCF("testfiles/racaddng","testfiles/racaddngall","Add_JML_Test","-cp","bin-runtime;testfiles/racaddngall;testfiles/racaddng;testfiles/racaddng/jmlunitng.jar");
    }

    @Test
    public void racNoModel() {
        rac = new String[]{jdk, "-classpath","bin"+z+"bin-runtime"+z+"testdata"+z+"testfiles/racaddng/jmlunitng.jar",null};
        expectedExit = 0;
        helpTCF("testfiles/racNoModel","testfiles/racNoModel","NoModelTest");
    }

    @Test
    public void racMainActivity() {
        runrac = false; // FIXME: Don't try running executable until we supply some input
        //rac = new String[]{jdk, "-classpath","bin"+z+"bin-runtime"+z+"testdata"+z+"testfiles/racaddng/jmlunitng.jar",null};
        expectedExit = 0;
        helpTCF("testfiles/racMainActivity","testfiles/racMainActivity","MainActivity");
    }


    @Test
    public void racMainActivityMicro() {
        expectedExit = 0;
        helpTCF("testfiles/racMainActivityMicro","testfiles/racMainActivityMicro","CharAt");
    }


}
