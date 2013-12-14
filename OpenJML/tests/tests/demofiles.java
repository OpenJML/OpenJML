package tests;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

/** These tests check running ESC on files in the file system, comparing the
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

@RunWith(Parameterized.class)
public class demofiles extends EscBase {

    boolean enableSubexpressions = false;
    
    public demofiles(String option, String solver) {
        super(option,solver);
    }
    
    String[] rac = null;
    
    /** The command-line to use to run ESC on a program */
    String[] sysrac = new String[]{jdk, "-classpath","bin"+z+"bin-runtime",null};

    @Override
    public void setUp() throws Exception {
        rac = sysrac;
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
    public void helpTCF(String sourceDirname, String outDir, String ... opts) {
        boolean print = false;
        try {
            new File(outDir).mkdirs();
            String actCompile = outDir + "/actual";
            new File(actCompile).delete();
            List<String> args = new LinkedList<String>();
            args.add("-esc");
            args.add("-noPurityCheck");
            args.add("-dir");
            args.add(sourceDirname);
            args.addAll(Arrays.asList(opts));
            
            PrintWriter pw = new PrintWriter(actCompile);
            int ex = org.jmlspecs.openjml.Main.execute(pw,null,null,args.toArray(new String[args.size()]));
            pw.close();
            
            String diffs = compareFiles(outDir + "/expected", actCompile);
            int n = 0;
            while (diffs != null) {
                n++;
                String name = outDir + "/expected" + n;
                if (!new File(name).exists()) break;
                diffs = compareFiles(name, actCompile);
            }
            if (diffs != null) {
                System.out.println(diffs);
                fail("Files differ: " + diffs);
            }  
            new File(actCompile).delete();
            if (ex != expectedExit) fail("Compile ended with exit code " + ex);

        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            throw e;
        } finally {
            // Should close open objects
        }
    }


    @Test
    public void testInvertInjection() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/verifythis/InvertInjection.java","testfiles/demoInvertInjection","-progress","-noInternalSpecs");
    }

    @Test
    public void testBinarySearch() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/verifythis/BinarySearch.java","testfiles/demoBinarySearch","-progress","-noInternalSpecs");
    }

    @Test // FIXME: Fails because of inadequate specs and use of \created
    public void testCustomer() {
        expectedExit = 1;
        helpTCF("../OpenJMLDemo/src/openjml/verifythis/Customer.java","testfiles/demoCustomer","-progress","-noInternalSpecs");
    }

    @Test // FIXME: Failure to reason about quantifiers
    public void testMaxByElimination() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/verifythis/MaxByElimination.java","testfiles/demoMaxByElimination","-progress");
    }

    @Test // FIXME: Cannot reason about \sum
    public void testSumAndMax() {
        expectedExit = 1;
        helpTCF("../OpenJMLDemo/src/openjml/verifythis/SumAndMax.java","testfiles/demoSumAndMax","-progress");
    }

    @Test // FIXME: Fails to reason about quantifiers
    public void testEscTest() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/misc1/EscTest.java","testfiles/demoEscTest","-progress","-jmltesting");//,"-subexpressions","-method=zero_matrix","-show");
    }


}
