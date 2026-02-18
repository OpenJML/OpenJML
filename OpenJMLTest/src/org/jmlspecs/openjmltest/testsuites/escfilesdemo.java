package org.jmlspecs.openjmltest.testsuites;

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
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.Assume;
import org.junit.FixMethodOrder;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

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

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escfilesdemo extends EscBaseFiles {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }
    

    // FIXME - use helpDemo?
    // FIXME - which of the demos should be tested with rac as well

    @Test
    public void escDemo() {
        expectedExit = 1;
        helpDemoFile("clock/TickTockClock.java","escDemo");
    }

    @Test
    public void escDemo1() {
        expectedExit = 6;
        helpDemoFile("clock/TickTockClock1.java","escDemo1","--esc-max-warnings=1","--check-feasibility=basic");
    }

    @Test
    public void escDemoA() {
        expectedExit = 1;
        helpDemoFile("clock/TickTockClockA.java","escDemoA","--subexpressions","--method=tick");
    }

    @Test
    public void escDemoA1() {
        expectedExit = 1;
        helpDemoFile("clock/TickTockClockA1.java","escDemoA1","--subexpressions","--method=tick");
    }

    @Test
    public void escDemoB() {
        expectedExit = 0;
        helpDemoFile("clock/TickTockClockB.java","escDemoB","--check-feasibility=basic");
    }

    @Test
    public void escDemoB1() {
        expectedExit = 6;
        helpDemoFile("clock/TickTockClockB1.java","escDemoB1","--esc-warnings-path");
    }

    @Test
    public void escDemoB2() {
        expectedExit = 6;
        helpDemoFile("clock/TickTockClockB2.java","escDemoB2","--check-feasibility=basic");
    }

    @Test
    public void escDemoB3() {
        expectedExit = 6;
        helpDemoFile("clock/TickTockClockB3.java","escDemoB3","--check-feasibility=basic");
    }

    @Test
    public void escDemoC() {
        expectedExit = 0;
        helpDemoFile("clock/TickTockClockC.java","escDemoC","--subexpressions","--check-feasibility=basic");
    }

    @Test
    public void escDemoD() {
        expectedExit = 0;
        helpDemoFile("clock/TickTockClockD.java","escDemoD","--subexpressions","--check-feasibility=basic");
    }

    @Test
    public void escDemoTypes() {
        expectedExit = 6;
        helpDemoFile("demo/Types.java","escDemoTypes","--typeQuants=true","--check-feasibility=precondition,exit");
    }

    @Test // Problem with reasoning about generic types // FIXME - does this need typeQuants?
    public void escDemoTypesAuto() {
        expectedExit = 6;
        helpDemoFile("demo/Types.java","escDemoTypes","--typeQuants=auto","--check-feasibility=precondition,exit");
    }

    @Test
    public void escDemoTypesNoQuants() { // FIXME - does this need typeQuants?
        expectedExit = 6;
        helpDemoFile("demo/Types.java","escDemoTypesNoQuants","--typeQuants=false","--check-feasibility=precondition,exit");
    }

    @Test // FIXME - Problem with int / short conversions
    public void escDemoTime() {
        expectedExit = 0;
        helpDemoFile("demo/Time.java","escDemoTime","--check-feasibility=precondition,exit");
    }


    @Test @Ignore // FIXME - no expected file yet and long-running
    public void demoPurse() {
        if ("cvc4".equals(solver)) fail();
        expectedExit = 0;
        helpDemo("purse","demoPurse","--timeout=15");
    }

    @Test @Ignore // FIXME - no expected file yet and long-running
    public void demoPurseMod() {
        if ("cvc4".equals(solver)) fail();
        expectedExit = 0;
        helpDemo("purseMod","demoPurseMod","--timeout=15");
    }

    @Test
    public void demoTaxpayer() {
        expectedExit = 0;
        helpDemoFile("demo/Taxpayer.java","demoTaxpayer","--check-feasibility=precondition,exit");
    }

    @Test
    public void demoBeancan() {
        expectedExit = 0;
        helpDemoFile("demo/BeanCan.java","demoBeancan","--code-math=bigint","--spec-math=bigint","--check-feasibility=precondition,exit");
    }

    @Test @Ignore // Non-deterministic output // and lengthy 
    public void demoecu() {
        expectedExit = 0;
        helpDemo("ecu","demoecu","--esc-max-warnings=1","--check-feasibility=precondition,exit");
    }


    // FIXME - use testDemo -- move to Demo testcase file?
    @Test 
    public void demoCashAmount() {
        expectedExit = 0;
        helpDemoFile("demo/CashAmount.java","demoCashAmount","--esc-max-warnings=1","--check-feasibility=none");
    }

    @Test
    public void demoCashAmountonlyPrivate() {
        expectedExit = 6;
        helpDemoFile("demo/CashAmountOnlyPrivate.java","demoCashAmountonlyPrivate","--check-feasibility=none");
    }

    @Test
    public void demoCashAmountMutable() {
        expectedExit = 0;
        helpDemoFile("demo/CashAmountMutable.java","demoCashAmountMutable","--code-math=bigint","--spec-math=bigint","--check-feasibility=none");
    }

    @Test
    public void demoCashAmountMF() {
        expectedExit = 0;
        helpDemoFile("demo/CashAmountMF.java","demoCashAmountMF","--esc-max-warnings=1","--check-feasibility=none");
    }

    @Test
    public void escCashAmountPrivate2() {   // FIXME - should thius be in with demo files?
        expectedExit = 0;
        helpEscFile("test/escCashAmountPrivate2/CashAmountOnlyPrivate.java","test/escCashAmountPrivate2","-classpath","test/escCashAmountPrivate2","-method=increase","-checkFeasibility=none");
    }

    @Test
    public void demoSettableClock() {
        helpDemo("settableClock","demoSettableClock","--check-feasibility=precondition,exit");
    }

    @Test @Ignore // FIXME - needs some fixing
    public void demoStudent() {
        expectedExit = 0;
        helpDemoFile("student","demoStudent","--check-feasibility=basic");
    }
    
    @Test
    public void demoInvertInjection() {
        expectedExit = 0;
        helpDemoFile("verifythis/InvertInjection.java","demoInvertInjection","--code-math=safe","--check-feasibility=basic");
    }

    @Test
    public void demoBinarySearch() {
        expectedExit = 6;
        helpDemoFile("verifythis/BinarySearch.java","demoBinarySearch","--code-math=safe","--check-feasibility=basic");
    }

    @Ignore  // FIXME: Fails because of inadequate specs and use of \created
    @Test
    public void demoCustomer() {
        expectedExit = 0;
        helpDemoFile("verifythis/Customer.java","demoCustomer","--code-math=safe","--check-feasibility=basic");
    }

    @Test
    public void demoMaxByElimination() {
        expectedExit = 0;
        ignoreNotes = true;
        helpDemoFile("verifythis/MaxByElimination.java","demoMaxByElimination","-code-math=bigint","--check-feasibility=basic");
    }

    @Test @Ignore // FIXME: Cannot reason about \sum
    public void demoSumAndMax() {
        expectedExit = 1;
        helpDemoFile("verifythis/SumAndMax.java","demoSumAndMax","--code-math=safe","--check-feasibility=basic");
    }

    @Test
    public void demoEscTest() {
        expectedExit = 0;
        helpDemoFile("misc1/EscTest.java","demoEscTest","--code-math=safe","--check-feasibility=basic");
    }


}

