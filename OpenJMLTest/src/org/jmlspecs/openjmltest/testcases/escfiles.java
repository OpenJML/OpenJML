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
public class escfiles extends EscBaseFiles {


    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }
    

    // FIXME - use helpDemo?

    @Test
    public void testDemo() {
        expectedExit = 1;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClock.java","test/escDemo");
    }

    @Test
    public void testDemo1() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClock1.java","test/escDemo1","--esc-max-warnings=1","--check-feasibility=basic");
    }

    @Test
    public void testDemoA() {
        expectedExit = 1;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockA.java","test/escDemoA","--subexpressions","--method=tick");
    }

    @Test
    public void testDemoA1() {
        expectedExit = 1;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockA1.java","test/escDemoA1","--subexpressions","--method=tick");
    }

    @Test
    public void testDemoB() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockB.java","test/escDemoB","--check-feasibility=basic");
    }

    @Test
    public void testDemoB1() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockB1.java","test/escDemoB1",
                "--progress","--esc-warnings-path");
    }

    @Test
    public void testDemoB2() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockB2.java","test/escDemoB2","--check-feasibility=basic");
    }

    @Test
    public void testDemoB3() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockB3.java","test/escDemoB3","--check-feasibility=basic");
    }

    @Test
    public void testDemoC() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockC.java","test/escDemoC","--subexpressions","--check-feasibility=basic");
    }

    @Test
    public void testDemoD() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/clock/TickTockClockD.java","test/escDemoD","--subexpressions","--check-feasibility=basic");
    }

    @Test
    public void escDemoTypes() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Types.java","test/escDemoTypes","--typeQuants=true","--check-feasibility=precondition,exit");
    }

    @Test // Problem with reasoning about generic types
    public void escDemoTypesAuto() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Types.java","test/escDemoTypes","--typeQuants=auto","--check-feasibility=precondition,exit");
    }

    @Test
    public void escDemoTypesDef() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Types.java","test/escDemoTypesNoQuants","--typeQuants=false","--check-feasibility=precondition,exit");
    }

    @Test // FIXME - Problem with int / short conversions
    public void escDemoTime() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/Time.java","test/escDemoTime","--check-feasibility=precondition,exit");
    }


    @Test // Order of errors is somewhat non-deterministic
    public void bag() {
        expectedExit = 0;
        helpTCF("test/bag","test/bag","--esc-max-warnings=1");
    }

    @Test
    public void bagModified() {
        expectedExit = 0;
        helpTCF("test/bagModified","test/bagModified");
    }

    @Test
    public void loopExercises() {
        expectedExit = 0;
        helpTCF("test/loopExercises","test/loopExercises","--exclude=gauss","--check-feasibility=basic");
    }

    @Test @Ignore // FIXME - nonlinear inference
    public void loopExercises2() {
        expectedExit = 0;
        helpTCF("test/loopExercises","test/loopExercises","--method=gauss");
    }

    @Test
    public void demoPurse() {
        if ("cvc4".equals(solver)) fail();
        expectedExit = 0;
        helpDemo("purse","purse","--timeout=15");
    }

    @Test
    public void demoPurseMod() {
        if ("cvc4".equals(solver)) fail();
        expectedExit = 0;
        helpDemo("purseMod","purseMod","-classpath",OpenJMLDemoPath + "/src/openjml/purseMod","--timeout=15");
    }

    @Test
    public void demoTaxpayer() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpDemo("demo/Taxpayer.java","demoTaxpayer","-classpath",OpenJMLDemoPath + "/src/openjml/demo","--check-feasibility=precondition,exit");
    }

    @Test
    public void demoBeanCan() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpDemo("demo/BeanCan.java","demoBeancan","-classpath",OpenJMLDemoPath + "/src/openjml/demo","--code-math=bigint","--spec-math=bigint","--check-feasibility=precondition,exit");
    }

    @Test @Ignore // Non-deterministic output // and lengthy
    public void ecuesc() {
        expectedExit = 0;
        helpDemo("ecudemo","ecuesc","-classpath",OpenJMLDemoPath + "/src/openjml/ecudemo","--esc-max-warnings=1","--check-feasibility=precondition,exit");
    }

    @Test
    public void valuetypes() {
        helpTF("valuetypes");
    }

    @Test
    public void valuetypes2() {
        helpTF("valuetypes2");
    }

    @Test
    public void valueTypesErr() {
        expectedExit = 1;
        helpTF("valuetypesErr");
    }

    @Test
    public void oldproblem() {
        helpTF("oldproblem");
    }

    @Test
    public void feasible() {
        helpTF("feasible");
    }

    // Just for debugging, not for testing
//    @Test
//    public void testOpt() {
//        helpTF("opt","-show","-method=m");
//    }

    @Test @Ignore // Problem is with mixed BV and bigint operations
    public void buggyCalculator() {
        helpTF("buggyCalculator");
    }

    @Test
    public void buggyRandomNumbers() {
        helpTF("buggyRandomNumbers");
    }

    @Test @Ignore // times out -- see testPrime for fixed version
    public void buggyPrimeNumbers() {
        helpTF("buggyPrimeNumbers");
    }

    @Test @Ignore // FIXME - unclear why fails
    public void buggyPalindrome() {
        helpTF("buggyPalindrome");
    }

    @Test
    public void escException() {
        helpTF("escException");
    }

    @Test
    public void preold() {
        helpTF("preold");
    }
    

    @Test
    public void preold2() {
        expectedExit = 1;
        helpTF("preold2");
    }

    @Test
    public void nullableOld() {
        helpTF("nullableOld");
    }

    @Test
    public void staticOld() {
        expectedExit = 1;
        helpTF("staticOld");
    }

    @Test
    public void escINF() {
        helpTF("escINF");
    }

    @Test
    public void escAdd() {
        expectedExit = 0;
        helpTF("escAdd");
    }

    @Test
    public void escAdd2() {
        expectedExit = 0;
        helpTF("escAdd2");
    }

    @Test
    public void escArrayCopy() {
        expectedExit = 0;
        helpTF("escArrayCopy");
    }

    @Test
    public void escClone() {
        expectedExit = 0;
        helpTF("escClone");
    }
    @Test
    public void esc2DArray() {
        expectedExit = 0;
        helpTF("esc2DArray");
    }

    @Test @Ignore // FIXME - axioms for multi-dimensional arrays
    public void esc2DTranspose() {
        expectedExit = 0;
        helpTF("esc2DTranspose");
    }

    @Test @Ignore // FIXME - Specs need improvement
    public void testVT20191() {
        expectedExit = 0;
        helpTF("verifythis-2019-1","--check-feasibility=none"); // FIXME - feasibility check times out
    }

    @Test
    public void testVT20192() {
        expectedExit = 0;
        helpTF("verifythis-2019-2","--solver-seed=42");
    }

    // FIXME - use testDemo -- move to Demo testcase file?
    @Test 
    public void escCashAmount() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/CashAmount.java","test/escCashAmount","-classpath",OpenJMLDemoPath + "/src/openjml/demo","-escMaxWarnings=1","-checkFeasibility=none");
    }

    @Test
    public void escCashAmountonlyPrivate() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/CashAmountOnlyPrivate.java","test/escCashAmountonlyPrivate","-classpath",OpenJMLDemoPath + "/src/openjml/demo","-checkFeasibility=none");
    }

    @Test
    public void escCashAmountMutable() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/CashAmountMutable.java","test/escCashAmountMutable","-classpath",OpenJMLDemoPath + "/src/openjml/demo","-code-math=bigint","-spec-math=bigint","-checkFeasibility=none");
    }

    @Test
    public void escCashAmountMF() {
        expectedExit = 0;
        helpTCF(OpenJMLDemoPath + "/src/openjml/demo/CashAmountMF.java","test/escCashAmountMF","-classpath",OpenJMLDemoPath + "/src/openjml/demo","-escMaxWarnings=1","-checkFeasibility=none");
    }

    @Test
    public void escCashAmountPrivate2() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpTCF("test/escCashAmountPrivate2/CashAmountOnlyPrivate.java","test/escCashAmountPrivate2","-classpath","test/escCashAmountPrivate2","-method=increase","-checkFeasibility=none");
    }

    @Test
    public void escSettableClock() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        expectedExit = 0;
        helpDemo("settableClock","escSettableClock","--check-feasibility=precondition,exit");
    }

    @Test
    public void escVector() {
        expectedExit = 0;
        helpTF("escVector","--code-math=java");
    }

    @Test
    public void escDMZLoop() {
        expectedExit = 0;
        helpTF("escDMZLoop","--method=findMax");
    }

    @Test
    public void escDMZLoopA() {
        expectedExit = 0;
        helpTF("escDMZLoopA","--method=findMax","--code-math=bigint","--spec-math=bigint");
    }

    @Test
    public void escDMZLoopB() {
        expectedExit = 0;
        helpTF("escDMZLoopB","--method=findMax","--code-math=bigint","--spec-math=bigint");
    }

    @Test
    public void escRecursiveInvariant() {
        expectedExit = -1;
        helpTF("escRecursiveInvariant");
    }

    @Test
    public void escRecursiveInvariant2() {
        expectedExit = -1;
        helpTF("escRecursiveInvariant2");
    }

    @Test
    public void testquant() {
        expectedExit = -1;
        helpTF("testquant");
    }

    @Test
    public void constructorDefaults() {
        expectedExit = 0;
        helpTF("constructorDefaults");
    }

    @Test
    public void escInlineLoop() {
        expectedExit = 0;
        helpTF("escInlineLoop");
    }


    // FIXME - reasoning about getClass
    @Test
    public void escBadCast() {
        expectedExit = 0;
        helpTF("escBadCast");
    }

    @Test
    public void escJLS() {
        expectedExit = 0;
        helpTF("escJLS");
    }

    @Test
    public void escDoublyLinkedList() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTF("escDoublyLinkedList");
    }

    @Test
    public void escModelFields() {
        helpTF("escModelFields","--progress");
    }

    @Test
    public void escSimpleString() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver)); // FIXME - CVC4 crashes or is long
        helpTF("escSimpleString","--nonnull-by-default","-timeout=240");
    }

    @Test
    public void escSimpleString2() {
        helpTF("escSimpleString2","--nonnull-by-default");
    }

    @Test
    public void escSimpleString3() {
        helpTF("escSimpleString3","--nonnull-by-default");
    }

    @Test
    public void escDiverges2() {
        helpTF("escDiverges2","--nonnull-by-default");
    }
    
    @Test @Ignore // FIXME - string comparisons for switch statements
    public void escStrings() {
        helpTF("escStrings");
    }
    
    @Test
    public void escEnum() {
        helpTF("escEnum");
    }
    
    @Test
    public void escLoop() {
        helpTF("escLoop");
    }

    @Test
    public void escLoopModifies() {
        helpTF("escLoopModifies");
    }

    @Test
    public void escLoopAssignable() {
        expectedExit = 1;
        helpTF("escLoopAssignable");
    }

    @Test
    public void escBodySpecs() {
        helpTF("escBodySpecs");
    }

    @Test
    public void escDeterministic() {
        helpTF("escDeterministic");
    }

    @Test
    public void escDeterministic2() {
        helpTF("escDeterministic2");
    }

    @Test
    public void escFunction() {
        helpTF("escFunction");
    }
    
    @Test
    public void escAbstractSpecs() {
        helpTF("escAbstractSpecs");
    }
    
    @Test
    public void escAbstractSpecs2() {
        expectedExit = 1;
        helpTF("escAbstractSpecs2");
    }
    
    @Test
    public void escInvariants() {
        helpTF("escInvariants");
    }

    @Test
    public void escInvariants2() {
        helpTF("escInvariants2");
    }

    @Test
    public void escSeparateJml() {
        helpTCF("test/escSeparateJml/BankingExample.java","test/escSeparateJml","-classpath","test/escSeparateJml");
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
    public void escConstructor() {
        helpTF("escConstructor");
    }

    @Test
    public void escConstructor2() {
        helpTF("escConstructor2");
    }

    @Test
    public void escConstructor3() {
        helpTF("escConstructor3");
    }

    @Test
    public void escConstructor4() {
        helpTF("escConstructor4");
    }
    
    @Test
    public void escConstructor5() {
        helpTF("escConstructor5");
    }

    @Test
    public void escConstructor6() {
        helpTF("escConstructor6");
    }

    @Test
    public void escShortCircuit() {
        helpTF("escShortCircuit");
    }
    
    @Test
    public void escRecursiveOld() {
        helpTF("escRecursiveOld");
    }
    
    @Test
    public void escEnsuresInfeasible() {
        helpTF("escEnsuresInfeasible");
    }

    @Test
    public void escEnsuresInfeasible2() {
        helpTF("escEnsuresInfeasible2");
    }

    @Test
    public void escConsInfeasible() {
        helpTF("escConsInfeasible");
    }

    @Test
    public void escMultipleModel() {
        helpTF("escMultipleModel");
    }

    @Test
    public void escMultipleModel2() {
        helpTF("escMultipleModel2");
    }

    @Test
    public void escMultipleModel3() {
        helpTF("escMultipleModel3");
    }

    @Test
    public void preconditionDetail() {  // FIXME - why multiple conjuncts reported
        helpTF("preconditionDetail");
    }

    @Test // FIXME - still has problems with imports in JML files and with checks on field initializers
    public void escJml() {
        helpTCF("test/escJml/Test.java","test/escJml","--specs-path=test/escJml/specs","--check-feasibility=none","--nonnull-by-default");
    }

    @Test
    public void escJml1() {
        helpTCF("test/escJml1/StorageParameters.java","test/escJml1","--specs-path=test/escJml1/specs","--check-feasibility=none","--nonnull-by-default");
    }

    @Test
    public void escJml1a() {
        helpTCF("test/escJml1a/StorageParameters.java","test/escJml1a","--specs-path=test/escJml1a/specs","--check-feasibility=none","--nullable-by-default");
    }

    @Test
    public void escJml2() {
        helpTCF("test/escJml2/StorageParameters.java","test/escJml2","--specs-path=test/escJml2/specs","--check-feasibility=none");
    }

    @Test
    public void escJml3() {
        helpTCF("test/escJml3/StorageParameters.java","test/escJml3","--specs-path=test/escJml2/specs","--check-feasibility=none");
    }

    @Test
    public void escDup() {
        helpTF("escDup");
    }

    @Test
    public void escLet() {
        helpTF("escLet","--solver-seed=9999");
    }
    
    @Test
    public void escElse() {
        helpTF("escElse");
    }

    @Test
    public void consfresh() {
        helpTF("consfresh");
    }

    @Test
    public void specificationInterfaceDemo() {
        helpTF("specificationInterfaceDemo");
    }

    @Test
    public void implicitIteration() {
        helpTF("implicitIteration");
    }

    @Test
    public void implicitIterationA() {
        helpTF("implicitIterationA");
    }

    // The following are split into multiple tests to minimize the combinatorial non-determinism in the output
    @Test
    public void sfbug420() {
        helpTF("sfbug420","--exclude=count;itemAt;main;isEmpty;push;top");
    }
    
    @Test
    public void sfbug420a() {
        helpTF("sfbug420a","--method=count");
    }
    
    @Test
    public void sfbug420b() {
        helpTF("sfbug420b","--method=itemAt");
    }
    
    @Test
    public void sfbug420c() {
        helpTF("sfbug420c","--method=main");
    }
    
    @Test
    public void sfbug420d() {
        helpTF("sfbug420d","--method=isEmpty");
    }
    
    @Test
    public void sfbug420e() {
        helpTF("sfbug420e","--method=push");
    }
    
    @Test
    public void sfbug420f() {
        helpTF("sfbug420f","--method=top");
    }
    
    @Test
    public void sfbug420X() {
        helpTF("sfbug420X");
    }
    
    @Test  // TODO - could use some additional investigation as to what this submitted file set is supposed to do
    public void escrmloop() {
        helpTF("escrmloop","--check-feasibility=none","--timeout=60");
    }
    
    @Test
    public void escrmloop2() {
        expectedExit = 1;
        helpTF("escrmloop2");
    }
    
    @Test @Ignore // not working yet
    public void escFPcompose() {
        helpTF("escFPcompose");
    }
    
    @Test
    public void escLemma() {
        helpTF("escLemma","--check-feasibility=none");
    }
    
    @Test
    public void escOld() {
        helpTF("escOld");
    }
    
    @Test
    public void exceptionCancel() {
        helpTF("exceptionCancel");
    }
    

    
    @Test @Ignore // FIXME - ignore for now; implement with real specs
    public void escRawding() {
        helpTF("escRawding","-specspath=test/escRawding","-code-math=safe");
    }
    
    // The following are really just typecheck problems

    @Test
    public void escPrivate() {
        expectedExit = 0;
        helpTF("escPrivate");
    }

    @Test  // FIXME - not yet working
    public void customPrimitiveTypes() {
        expectedExit = 0;
        helpTF("customPrimitiveTypes");
    }

    @Test
    public void enums() {
        expectedExit = 0;
        helpTF("enums");
    }

    @Test @Ignore // FIXME - not yet implemented
    public void enums1() {
        expectedExit = 0;
        helpTF("enums1");
        //helpTF("enums1","-show","-method=m5c","-subexpressions");
    }

    @Test
    public void enums2() {
        expectedExit = 0;
        helpTF("enums2");
    }

    @Test
    public void datatype() {
        expectedExit = 0;
        helpTF("datatype");
    }

    @Test // Basic problem is with the toString conversion of a \bigint, because of the -code-math=bigint setting of these
    public void factorial() {
        expectedExit = 0;
        helpTF("factorial");//,"-code-math=java");
    }

    @Test @Ignore // FIXME - times out
    public void primeNumbers() {
        expectedExit = 0;
        helpTF("primeNumbers");
    }
    
    @Test
    public void splits() {
        expectedExit = 0;
        helpTF("splits");
    }
    
    @Test
    public void splits2() {
        expectedExit = 0;
        helpTF("splits2");
    }
    
    @Test
    public void Dzmz() {
        expectedExit = 0;
        helpTF("Dzmz");
    }

    @Test
    public void refining() {
        expectedExit = 0;
        helpTF("refining");
    }

    @Test
    public void refiningBad() {
        expectedExit = 1;
        helpTF("refiningBad");
    }

    @Test @Ignore // FIXME - fix a problem with concatenation
    public void gcdcalculator() {
        expectedExit = 0;
        helpTF("gcdcalculator");
    }

    @Test
    public void visibilitySimple() {
        expectedExit = 1;
        helpTF("visibilitySimple","--normal");
    }

    @Test
    public void requiresElse() { // FIXME - why the two different formats of output
        helpTF("requiresElse","--show=program"); // --show=program is part of test results
    }

    @Test
    public void tuple() {
        helpTF("tuple");
    }

    @Test
    public void tupleBad() {
        expectedExit = 1;
        helpTF("tupleBad");
    }

    @Test @Ignore // FIXME - not yet implemented
    public void anonymousCaptures() {
        expectedExit = 1;
        helpTF("anonymousCaptures");
    }
    
    @Test @Ignore // FIXME - needs implementation
    public void streams() {
        expectedExit = 1;
        helpTF("streams");
    }
    
    @Test
    public void checkAsserts() {
        helpTF("checkAsserts");
    }
    
    @Test
    public void callstacks() {
        helpTF("callstacks");
    }
    
    @Test
    public void varargs() {
        helpTF("varargs");
    }
    
    @Test
    public void valuestrings() {
        helpTF("valuestrings");
    }
    
    @Test
    public void valuestringsBad() {
        expectedExit = 1;
        helpTF("valuestringsBad");
    }
    
    @Test // FIXME - get an infeasibility when Arrays.binarySearch uses Arrays.contains
    public void binarySearch() {
        helpTF("binarySearch");
    }
    
    @Test
    public void modelImport1() {
        expectedExit = 1;
        helpTCF("test/modelImports/Test1.java","test/modelImports/test1","--check","-cp","test/modelImports");
    }
    
    @Test
    public void modelImport2() {
        helpTCF("test/modelImports/Test2.java","test/modelImports/test2","--check","-cp","test/modelImports");
    }
    
    @Test
    public void modelImport3() {
        expectedExit = 1;
        helpTCF("test/modelImports/Test3.java","test/modelImports/test3","--check","-cp","test/modelImports");
    }
    
    @Test
    public void modelImport4() {
        expectedExit = 1;
        helpTCF("test/modelImports/Test4.java","test/modelImports/test4","--check","-cp","test/modelImports");
    }
    
    @Test
    public void modelImport5() {
        helpTCF("test/modelImports/Test5.java","test/modelImports/test5","--check","-cp","test/modelImports");
    }
}
