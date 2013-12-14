package tests;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.Utils;
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
public class escnonpublic extends EscBase {

    boolean enableSubexpressions = false;
    
    public escnonpublic(String option, String solver) {
        super(option,solver);
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
            args.add("-jmltesting");
            args.add("-no-purityCheck");
            if (new File(sourceDirname).isDirectory()) args.add("-dir");
            args.add(sourceDirname);
            if (solver != null) args.add("-prover="+solver);
            if (option != null) {
                for (String o: option.split(" ")) if (!o.isEmpty()) args.add(o);
            }
            
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
    public void testEscStaticModel() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/nonpublic/escStaticModel","testfiles/escStaticModel","-progress");
    }

    @Test
    public void testDMZ() {
        expectedExit = 1;
        helpTCF("../OpenJMLDemo/src/nonpublic/dmz","testfiles/dmz","-progress");
    }

    @Test
    public void testDMZ2() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/nonpublic/dmz2","testfiles/dmz2","-progress");
    }

    @Test
    public void testDMZ3() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/nonpublic/dmz3","testfiles/dmz3","-progress");
    }
}
