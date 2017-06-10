package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.ParameterizedWithNames;
import org.junit.runners.Parameterized.Parameters;

/** These tests check running ESC on files in the file system, comparing the
 * output against expected files. These tests are a bit easier to create, since 
 * the file and output do not have to be converted into Strings; however, they
 * are not as easily read, since the content is tucked away in files, rather 
 * than immediately there in the test class.
 * <P>
 * To add a new test:
 * <UL>
 * <LI> create a directory containing the test files as a subdirectory of 
 * 'test'
 * <LI> add a test to this class - typically named similarly to the folder
 * containing the source data
 * </UL>
 */

@RunWith(ParameterizedWithNames.class)
public class escfiles extends EscBase {

    boolean enableSubexpressions = false;
    
    public escfiles(String options, String solver) {
        super(options,solver);
    }
    
    
    String[] rac = null;
    
    /** The command-line to use to run ESC on a program */
    String[] sysrac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime",null};

    @Override
    public void setUp() throws Exception {
        rac = sysrac;
        super.setUp();
    	ignoreNotes = true;
    }
    
    public void helpTF(String testDirname, String ... opts) {
        String d = "test/" + testDirname;
        String[] newopts = new String[opts.length+2];
        newopts[0] = "-classpath";
        newopts[1] = d;
        System.arraycopy(opts,0,newopts,2,opts.length);
        helpTCF(d,d,newopts);
    }

    public void helpDemo(String testDirname, String outdir, String ... opts) {
        String d = OpenJMLDemoPath + "/src/openjml/" + testDirname;
        String[] newopts = new String[opts.length+2];
        newopts[0] = "-classpath";
        newopts[1] = d;
        System.arraycopy(opts,0,newopts,2,opts.length);
        helpTCF(d,"test/" + outdir,newopts);
    }

    public void helpTCF(String sourceDirname, String outDir, String ... opts) {
    	escOnFiles(sourceDirname,outDir,opts);
    }


    @Test
    public void testDemo() {
        expectedExit = 1;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClock.java","test/escDemo");
    }

    @Test
    public void testDemo1() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClock1.java","test/escDemo1","-escMaxWarnings=1");
    }

    @Test
    public void testDemoA() {
        expectedExit = 1;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockA.java","test/escDemoA","-subexpressions","-method=tick");
    }

    @Test
    public void testDemoA1() {
        expectedExit = 1;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockA1.java","test/escDemoA1","-subexpressions","-method=tick");
    }

    @Test
    public void testDemoB() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockB.java","test/escDemoB");//,"-method=tick","-show","-escMaxWarnings=1");
    }

    @Test
    public void testDemoB1() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockB1.java","test/escDemoB1",
                "-progress","-escMaxWarningsPath",enableSubexpressions ? "-subexpressions" : "");
    }

    @Test
    public void testDemoB2() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockB2.java","test/escDemoB2");
    }

    @Test
    public void testDemoB3() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockB3.java","test/escDemoB3",enableSubexpressions ? "-subexpressions" : "");
    }

    @Test
    public void testDemoC() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockC.java","test/escDemoC","-subexpressions");
    }

    @Test
    public void testDemoD() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockD.java","test/escDemoD","-subexpressions");
    }

    @Test
    public void testDemoTypes() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Types.java","test/escDemoTypes","-typeQuants=true","-noInternalSpecs",enableSubexpressions ? "-subexpressions" : "");
    }

    @Test // Problem with reasoning about generic types
    public void testDemoTypesAuto() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Types.java","test/escDemoTypes","-typeQuants=auto","-noInternalSpecs",enableSubexpressions ? "-subexpressions" : "");
    }

    @Test
    public void testDemoTypesDef() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Types.java","test/escDemoTypes","-typeQuants=false","-noInternalSpecs",enableSubexpressions ? "-subexpressions" : "");
    }

    @Test // FIXME - Problem with int / short conversions
    public void testDemoTime() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Time.java","test/escDemoTime","-logic=AUFNIA");
    }


    @Test @Ignore // FIXME - order of errors is too non-deterministic
    public void testBag() {
        expectedExit = 0;
        helpTCF("test/bag","test/bag");
    }

    @Test
    public void testBagModified() {
        expectedExit = 0;
        helpTCF("test/bagModified","test/bagModified");
    }

    @Test @Ignore // FIXME - hangs up sometimes with some solvers; takes a while with others - comment out while we are doing repeated testing
    public void testLoopExercises() {
        expectedExit = 0;
        helpTCF("test/loopExercises","test/loopExercises","-logic=AUFNIA");
    }

    @Test @Ignore  // FIXME - CVC4 crashes
    public void testPurseCard() {
        if ("cvc4".equals(solver)) fail();
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/purse","test/purse","-logic=AUFNIA","-timeout=15");
    }

    @Test @Ignore // FIXME - CVC4 crashes
    public void testPurseCardMod() {
        if ("cvc4".equals(solver)) fail();
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/purseMod","test/purseMod","-classpath",OpenJMLDemoPath + "/src/openjml/purseMod","-logic=AUFNIA","-timeout=15");
    }

    @Test
    public void testTaxpayer() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Taxpayer.java","test/demoTaxpayer","-classpath",OpenJMLDemoPath + "/src/openjml/demo");
    }

    @Test
    public void testBeanCan() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/BeanCan.java","test/demoBeancan","-classpath",OpenJMLDemoPath + "/src/openjml/demo");
    }

    @Test @Ignore // FIXME - stuck or just long?
    public void testECU() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/ecudemo","test/ecuesc","-classpath",OpenJMLDemoPath + "/src/openjml/ecudemo","-logic=AUFNIA");
    }

    @Test
    public void testException() {
        helpTF("escException");
    }

    @Test
    public void testAdd() {
        expectedExit = 1;
        helpTF("escAdd");
    }

    @Test
    public void testAdd2() {
        expectedExit = 0;
        helpTF("escAdd2");
    }

    @Test 
    public void testCashAmount() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/CashAmount.java","test/escCashAmount","-classpath",OpenJMLDemoPath + "/src/openjml/demo","-escMaxWarnings=1","-logic=AUFNIA");
    }

    @Test
    public void testCashAmount2() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/CashAmountOnlyPrivate.java","test/escCashAmountonlyPrivate","-classpath",OpenJMLDemoPath + "/src/openjml/demo");
    }

    @Test
    public void testCashAmountMutable() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/CashAmountMutable.java","test/escCashAmountMutable","-classpath",OpenJMLDemoPath + "/src/openjml/demo");
    }

    @Test
    public void testCashAmountMF() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/CashAmountMF.java","test/escCashAmountMF","-classpath",OpenJMLDemoPath + "/src/openjml/demo","-escMaxWarnings=1");
    }

    @Test
    public void testSettableClock() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpDemo("settableClock","escSettableClock","-logic=AUFNIA");
    }

    @Test
    public void testVector() {
        expectedExit = 0;
        helpTF("escVector","-code-math=java");
    }

    @Test @Ignore // FIXME - make this work by carrying information about variables into the first cycle of a loop
    public void testDMZLoop() {
        expectedExit = 0;
        helpTF("escDMZLoop","-method=findMax","-show");
    }

    @Test
    public void testDMZLoopA() {
        expectedExit = 0;
        helpTF("escDMZLoopA","-method=findMax");
    }

    @Test
    public void testDMZLoopB() {
        expectedExit = 0;
        helpTF("escDMZLoopB","-method=findMax");
    }

    @Test
    public void testRecursiveInvariant() {
        expectedExit = 1;
        helpTF("escRecursiveInvariant","-no-minQuant");
    }

    @Test
    public void testRecursiveInvariantMQ() {
        expectedExit = 1;
        helpTF("escRecursiveInvariantMQ","-minQuant");
    }

    @Test
    public void testRecursiveInvariant2() {
        expectedExit = 1;
        helpTF("escRecursiveInvariant2","-no-minQuant");
    }

    @Test
    public void testRecursiveInvariant2MQ() {
        expectedExit = 1;
        helpTF("escRecursiveInvariant2","-minQuant");
    }

    // FIXME - reasoning about getClass
    @Test
    public void testBadCast() {
        expectedExit = 0;
        helpTF("escBadCast");//,"-show","-method=BadCast.equals");
    }

    @Test
    public void testCashAmountPrivate2() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF("test/escCashAmountPrivate2/CashAmountOnlyPrivate.java","test/escCashAmountPrivate2","-classpath","test/escCashAmountPrivate2","-method=increase","-logic=AUFNIA");
    }

    @Test
    public void testJLS() {
        expectedExit = 0;
        helpTF("escJLS");
    }

    @Test
    public void testDoublyLinkedList() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTF("escDoublyLinkedList");
    }

    @Test
    public void testEscModelFields() {
        helpTF("escModelFields","-progress");
    }

    @Test
    public void testEscSimpleString() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver)); // FIXME - CVC4 crashes or is long
        helpTF("escSimpleString","-nonnullByDefault","-timeout=240");//,"-method=SimpleString","-show","-checkFeasibility=debug");
    }

    @Test
    public void testEscSimpleString2() {
        helpTF("escSimpleString2","-nonnullByDefault");
    }

    @Test
    public void testEscSimpleString3() {
        helpTF("escSimpleString3","-nonnullByDefault");
    }


    @Test @Ignore // FIXME - long running, probably because of the logic
    public void testEscDiverges() {
        helpTF("escDiverges","-nonnullByDefault","-logic=AUFNIRA");
    }


    @Test @Ignore // FIXME - long running, probably because of the logic
    public void testEscDiverges2() {
        helpTF("escDiverges2","-nonnullByDefault","-logic=AUFNIRA");
    }
    
    @Test
    public void testEscDeterministic() {
        helpTF("escDeterministic");
	}

    @Test
    public void testEscDeterministic2() {
        helpTF("escDeterministic2");
	}

    @Test
    public void testEscInvariants() {
        helpTF("escInvariants");
    }

    @Test
    public void testEscInvariants2() {
        helpTF("escInvariants2");
    }

    @Test
    public void testJmlSpecPublic() {
        helpTCF("test/escSeparateJml/BankingExample.java","test/escSeparateJml","-classpath","test/escSeparateJml");//,"-show","-method=credit","-subexpressions","-checkFeasibility=all");
    }

    @Test
    public void escAssignableBug() {
        helpTF("escAssignableBug");
    }

    @Test
    public void escDerivedInvariant() {
        helpTF("escDerivedInvariant");
    }

    @Test
    public void testEscConstructor() {
        helpTF("escConstructor");
    }

    @Test
    public void testEscConstructor2() {
        helpTF("escConstructor2");
    }

    @Test
    public void testEscConstructor3() {
        helpTF("escConstructor3");
    }

    @Test
    public void testEscConstructor4() {
        helpTF("escConstructor4");
    }
    
    @Test
    public void testEscConstructor5() {
        helpTF("escConstructor5");
    }

    @Test
    public void testEscConstructor6() {
        helpTF("escConstructor6");
    }

    @Test
    public void testEscShortCircuit() {
        helpTF("escShortCircuit");
    }

    @Test // FIXME - still has problems with imports in JML files and with checks on field initializers
    public void testEscJml() {
        helpTCF("test/escJml/Test.java","test/escJml","-specspath=test/escJml/specs");
    }

    @Test
    public void testEscJml1() {
        helpTCF("test/escJml1/StorageParameters.java","test/escJml1","-specspath=test/escJml1/specs");//,"-show","-method=main");
    }

    @Test
    public void testEscJml2() {
        helpTCF("test/escJml2/StorageParameters.java","test/escJml2","-specspath=test/escJml2/specs");
    }

    @Test
    public void testEscJml3() {
        helpTCF("test/escJml3/StorageParameters.java","test/escJml3","-specspath=test/escJml2/specs");
    }

    @Test
    public void testEscJmlDup() {
        helpTF("escDup");
    }



}
