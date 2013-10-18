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
public class escfiles extends EscBase {

    boolean enableSubexpressions = false;
    
    public escfiles(String option, String solver) {
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
    public void testDemo() {
        expectedExit = 1;
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClock.java","testfiles/escDemo","-subexpressions","-progress");
    }

    @Test
    public void testDemo1() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClock1.java","testfiles/escDemo1","-progress","-escMaxWarnings=1","-jmltesting");
    }

    @Test
    public void testDemoA() {
        expectedExit = 1;
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClockA.java","testfiles/escDemoA","-subexpressions","-progress","-method=tick");
    }

    @Test
    public void testDemoA1() {
        expectedExit = 1;
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClockA1.java","testfiles/escDemoA1","-subexpressions","-progress","-method=tick");
    }

    @Test
    public void testDemoB() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClockB.java","testfiles/escDemoB","-subexpressions","-progress","-jmltesting");//,"-show","-method=tick");
    }

    @Test
    public void testDemoB1() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClockB1.java","testfiles/escDemoB1",
                "-progress",enableSubexpressions ? "-subexpressions" : "","-jmltesting");
    }

    @Test
    public void testDemoB2() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClockB2.java","testfiles/escDemoB2","-progress","-jmltesting");
    }

    @Test
    public void testDemoB3() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClockB3.java","testfiles/escDemoB3",enableSubexpressions ? "-subexpressions" : "","-progress","-jmltesting");
    }

    @Test
    public void testDemoC() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClockC.java","testfiles/escDemoC","-subexpressions","-progress","-jmltesting");
    }

    @Test
    public void testDemoTypes() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/Types.java","testfiles/escDemoTypes","-noInternalSpecs",enableSubexpressions ? "-subexpressions" : "","-progress","-jmltesting");
    }

    @Test
    public void testDemoTime() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/Time.java","testfiles/escDemoTime","-progress","-jmltesting","-logic=AUFNIA");
    }


    @Test @Ignore // FIXME - order of errors is too non-deterministic
    public void testBag() {
        expectedExit = 0;
        helpTCF("testfiles/bag","testfiles/bag");
    }

    @Test
    public void testBagModified() {
        expectedExit = 0;
        helpTCF("testfiles/bagModified","testfiles/bagModified","-progress","-jmltesting");
    }

    @Test // FIXME - hangs up sometimes with some solvers
    public void testLoopExercises() {
        expectedExit = 0;
        helpTCF("testfiles/loopExercises","testfiles/loopExercises","-progress","-logic=AUFNIA","-timeout=30");
    }

    @Test @Ignore
    public void testPurseCard() {
        if (solver.equals("cvc4")) fail(); // FIXME - CVC4 crashes
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/purse","testfiles/purse","-progress","-logic=AUFNIA","-timeout=15");
    }

    @Test @Ignore
    public void testPurseCardMod() {
        if (solver.equals("cvc4")) fail(); // FIXME - CVC4 crashes
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/purseMod","testfiles/purseMod","-classpath","../OpenJMLDemo/src/openjml/purseMod","-progress","-logic=AUFNIA","-timeout=15");
    }

    @Test
    public void testTaxpayer() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/TaxPayer.java","testfiles/demoTaxpayer","-classpath","../OpenJMLDemo/src/openjml/demo","-progress","-jmltesting");
    }

    @Test
    public void testBeanCan() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/BeanCan.java","testfiles/demoBeancan","-classpath","../OpenJMLDemo/src/openjml/demo","-progress","-jmltesting");
    }

    @Test
    public void testECU() {
        expectedExit = 1;
        helpTCF("../OpenJMLDemo/src/openjml/ecudemo","testfiles/ecuesc","-classpath","../OpenJMLDemo/src/openjml/ecudemo","-progress","-jmltesting","-logic=AUFNIA","-timeout=30");
    }

    @Test
    public void testAdd() {
        expectedExit = 0;
        helpTCF("testfiles/escAdd/Add.java","testfiles/escAdd","-classpath","testfiles/escAdd","-progress","-jmltesting","-timeout=30");
    }

    @Test
    public void testAdd2() {
        expectedExit = 0;
        helpTCF("testfiles/escAdd2/Add.java","testfiles/escAdd2","-classpath","testfiles/escAdd2","-progress","-jmltesting","-timeout=30");
    }

    @Test
    public void testCashAmount() {
        expectedExit = 1;
        helpTCF("../OpenJMLDemo/src/openjml/demo/CashAmount.java","testfiles/escCashAmount","-classpath","../OpenJMLDemo/src/openjml/demo","-progress","-jmltesting","-show","-method=negate","-trace","-subexpressions");
    }

    @Test
    public void testCashAmount2() {
        expectedExit = 1;
        helpTCF("../OpenJMLDemo/src/openjml/demo/CashAmountOnlyPrivate.java","testfiles/escCashAmountonlyPrivate","-classpath","../OpenJMLDemo/src/openjml/demo","-progress","-jmltesting");
    }


}
