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
    
    public void helpTF(String testFilesDirname, String ... opts) {
        String d = "testfiles/" + testFilesDirname;
        String[] newopts = new String[opts.length+2];
        newopts[0] = "-classpath";
        newopts[1] = d;
        System.arraycopy(opts,0,newopts,2,opts.length);
        helpTCF(d,d,newopts);
    }

    public void helpDemo(String testFilesDirname, String outdir, String ... opts) {
        String d = "../OpenJMLDemo/src/openjml/" + testFilesDirname;
        String[] newopts = new String[opts.length+2];
        newopts[0] = "-classpath";
        newopts[1] = d;
        System.arraycopy(opts,0,newopts,2,opts.length);
        helpTCF(d,"testfiles/" + outdir,newopts);
    }

    public void helpTCF(String sourceDirname, String outDir, String ... opts) {
        boolean print = false;
        try {
            new File(outDir).mkdirs();
            String actCompile = outDir + "/actual";
            new File(actCompile).delete();
            List<String> args = new LinkedList<String>();
            args.add("-esc");
            args.add("-no-purityCheck");
            args.add("-jmltesting");
            args.add("-timeout=30");
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
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClock1.java","testfiles/escDemo1","-progress","-escMaxWarnings=1");
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
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClockB.java","testfiles/escDemoB","-subexpressions","-progress");//,"-show","-method=tick");
    }

    @Test
    public void testDemoB1() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClockB1.java","testfiles/escDemoB1",
                "-progress",enableSubexpressions ? "-subexpressions" : "");
    }

    @Test
    public void testDemoB2() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClockB2.java","testfiles/escDemoB2","-progress");
    }

    @Test
    public void testDemoB3() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClockB3.java","testfiles/escDemoB3",enableSubexpressions ? "-subexpressions" : "","-progress");
    }

    @Test
    public void testDemoC() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/clock/TickTockClockC.java","testfiles/escDemoC","-subexpressions","-progress");
    }

    @Test
    public void testDemoTypes() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/Types.java","testfiles/escDemoTypes","-noInternalSpecs",enableSubexpressions ? "-subexpressions" : "","-progress");
    }

    @Test
    public void testDemoTime() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/Time.java","testfiles/escDemoTime","-progress","-logic=AUFNIA");
    }


    @Test @Ignore // FIXME - order of errors is too non-deterministic
    public void testBag() {
        expectedExit = 0;
        helpTCF("testfiles/bag","testfiles/bag");
    }

    @Test
    public void testBagModified() {
        expectedExit = 0;
        helpTCF("testfiles/bagModified","testfiles/bagModified","-progress");
    }

    @Test // FIXME - hangs up sometimes with some solvers
    public void testLoopExercises() {
        expectedExit = 0;
        helpTCF("testfiles/loopExercises","testfiles/loopExercises","-progress","-logic=AUFNIA");
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
        if (solver.equals("cvc4")) fail(); // FIXME - CVC4 crashes?
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/TaxPayer.java","testfiles/demoTaxpayer","-classpath","../OpenJMLDemo/src/openjml/demo","-progress");
    }

    @Test
    public void testBeanCan() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/BeanCan.java","testfiles/demoBeancan","-classpath","../OpenJMLDemo/src/openjml/demo","-progress");
    }

    @Test // FIXME - times out
    public void testECU() {
        expectedExit = 1;
        helpTCF("../OpenJMLDemo/src/openjml/ecudemo","testfiles/ecuesc","-classpath","../OpenJMLDemo/src/openjml/ecudemo","-progress","-logic=AUFNIA");
    }

    @Test
    public void testAdd() {
        expectedExit = 1;
        helpTF("escAdd","-progress");
    }

    @Test
    public void testAdd2() {
        expectedExit = 0;
        helpTF("escAdd2","-progress");
    }

    @Test @Ignore // CVC4 crashes
    public void testCashAmount() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/CashAmount.java","testfiles/escCashAmount","-classpath","../OpenJMLDemo/src/openjml/demo","-progress","-escMaxWarnings=1");
    }

    @Test
    public void testCashAmount2() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/CashAmountOnlyPrivate.java","testfiles/escCashAmountonlyPrivate","-classpath","../OpenJMLDemo/src/openjml/demo","-progress");
    }

    @Test
    public void testCashAmountMutable() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/CashAmountMutable.java","testfiles/escCashAmountMutable","-classpath","../OpenJMLDemo/src/openjml/demo","-progress");
    }

    @Test
    public void testCashAmountMF() {
        expectedExit = 0;
        helpTCF("../OpenJMLDemo/src/openjml/demo/CashAmountMF.java","testfiles/escCashAmountMF","-classpath","../OpenJMLDemo/src/openjml/demo","-progress","-escMaxWarnings=1");
    }

    @Test
    public void testSettableClock() {
        expectedExit = 0;
        helpDemo("settableClock","escSettableClock","-progress","-logic=AUFNIRA");
    }

    @Test
    public void testVector() {
        expectedExit = 0;
        helpTCF("testfiles/escVector/Vector.java","testfiles/escVector","-classpath","testfiles/escVector","-progress","-escMaxWarnings=1");
    }

    @Test @Ignore // FIXME - make this work by carrying information about variables into the first cycle of a loop
    public void testDMZLoop() {
        expectedExit = 0;
        helpTCF("testfiles/escDMZLoop/ESCTest.java","testfiles/escDMZLoop","-classpath","testfiles/escDMZLoop","-progress","-method=findMax","-show");
    }

    @Test
    public void testDMZLoopA() {
        expectedExit = 0;
        helpTCF("testfiles/escDMZLoopA/ESCTest.java","testfiles/escDMZLoopA","-classpath","testfiles/escDMZLoopA","-progress","-method=findMax");
    }

    @Test
    public void testDMZLoopB() {
        expectedExit = 0;
        helpTCF("testfiles/escDMZLoopB/ESCTest.java","testfiles/escDMZLoopB","-classpath","testfiles/escDMZLoopB","-progress","-method=findMax");
    }

    @Test
    public void testRecursiveInvariant() {
        expectedExit = 1;
        helpTCF("testfiles/escRecursiveInvariant/RecursiveInvariant.java","testfiles/escRecursiveInvariant","-classpath","testfiles/escRecursiveInvariant","-progress");
    }

    @Test // FIXME - needs to handle getClass()
    public void testBadCast() {
        expectedExit = 0;
        helpTCF("testfiles/escBadCast/BadCast.java","testfiles/escBadCast","-classpath","testfiles/escBadCast","-progress");
    }

    @Test
    public void testCashAmountPrivate2() {
        expectedExit = 0;
        helpTCF("testfiles/escCashAmountPrivate2/CashAmountOnlyPrivate.java","testfiles/escCashAmountPrivate2","-classpath","testfiles/escCashAmountPrivate2","-progress","-method=increase");
    }

    @Test // FIXME - fails because of generics
    public void testDoublyLinkedList() {
        helpTCF("testfiles/escDoublyLinkedList/DoublyLinkedList.java","testfiles/escDoublyLinkedList","-classpath","testfiles/escDoublyLinkedList","-progress");
    }

    @Test
    public void testEscModelFields() {
        helpTF("escModelFields","-progress");
    }

    @Test
    public void testEscSimpleString() {
        helpTF("escSimpleString","-nonnullByDefault","-progress");//,"-escMaxWarnings=1","-show","-trace","-subexpressions");
    }

    @Test
    public void testEscSimpleString2() {
        helpTF("escSimpleString2","-nonnullByDefault","-progress");
    }

    @Test
    public void testEscSimpleString3() {
        helpTF("escSimpleString3","-nonnullByDefault","-progress");
    }


    @Test
    public void testEscDiverges() {
        helpTF("escDiverges","-nonnullByDefault","-progress","-logic=AUFNIRA");
    }


    @Test
    public void testEscDiverges2() {
        helpTF("escDiverges2","-nonnullByDefault","-progress","-logic=AUFNIRA");
    }

    @Test
    public void testEscInvariants() {
        helpTF("escInvariants","-progress");
    }

    @Test
    public void testEscInvariants2() {
        helpTF("escInvariants2","-progress");
    }


}
