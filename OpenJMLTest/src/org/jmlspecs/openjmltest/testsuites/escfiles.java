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
public class escfiles extends EscBaseFiles {


    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }
    
    public void helpTCF(String n, String d, String ... opts) {
        super.helpTCF(n, d, opts);
    }

    public void helpTG(String... opts) {
        super.helpTG(opts);
    }
    
    @Test // Order of errors is somewhat non-deterministic
    public void bag() {
        expectedExit = 6;
        helpTG("--esc-max-warnings=1","--check-feasibility=none");
    }

    @Test
    public void bagModified() {
        expectedExit = 0;
        helpTG("--check-feasibility=none");
    }

    @Test
    public void loopExercises() {
        expectedExit = 0;
        helpTG("--exclude=gauss,gauss2","--check-feasibility=basic");
    }

    @Test // FIXME - nonlinear inference -- times out
    public void loopExercises2() {
        expectedExit = 0;
        helpTCF("test/loopExercises","test/loopExercises2","--method=gauss,gauss2");
    }

    @Test
    public void oldproblem() {
        helpTG();
    }

    @Test
    public void feasible() {
        helpTG();
    }

    @Test
    public void escINF() {
        helpTG();
    }

    @Test
    public void escAdd() {
        expectedExit = 0;
        helpTG("--code-math=bigint");
    }

    @Test
    public void escAdd2() {
        expectedExit = 0;
        helpTG();
    }

    @Test
    public void escArrayCopy() {
        expectedExit = 0;
        helpTG();
    }

    @Test
    public void escClone() {
        expectedExit = 0;
        helpTG();
    }
    
    @Test
    public void esc2DArray() {
        //addOptions("--method=m","--progress","--show");
        helpTG();
    }

    @Test
    public void esc2DArray2() {
        expectedExit = 0;
        helpTG();
    }

    @Test @Ignore // FIXME - axioms for multi-dimensional arrays
    public void esc2DTranspose() {
        expectedExit = 0;
        helpTG();
    }

    @Test @Ignore // FIXME - Specs need improvement
    public void verifythis2019_1() {
        expectedExit = 0;
        helpTF("verifythis2019_1","--check-feasibility=none"); // FIXME - feasibility check times out
    }

    @Test
    public void verifythis2019_2() {
        expectedExit = 0;
        helpTF("verifythis2019_2","--solver-seed=42");
    }

    @Test
    public void escCashAmountPrivate2() {   // FIXME - with demo files?
        expectedExit = 0;
        helpTCF("test/escCashAmountPrivate2/CashAmountOnlyPrivate.java","test/escCashAmountPrivate2","-classpath","test/escCashAmountPrivate2","-method=increase","-checkFeasibility=none");
    }

    @Test
    public void escVector() {
        expectedExit = 6;
        helpTG("--code-math=java","--exclude=copyIntoOK,copyIntoA");
    }

    @Test
    public void escVectorA() {
        expectedExit = 6;
        helpTG("--code-math=java","--method=copyIntoOK,copyIntoA");
    }

    @Test
    public void escDMZLoop() {
        expectedExit = 6;
        helpTG("--method=findMax");
    }

    @Test
    public void escDMZLoopA() {
        expectedExit = 0;
        helpTG("--method=findMax","--code-math=bigint","--spec-math=bigint");
    }

    @Test
    public void escDMZLoopB() {
        expectedExit = 0;
        helpTG("--method=findMax","--code-math=bigint","--spec-math=bigint");
    }

    @Test
    public void escRecursiveInvariant() {
        expectedExit = -1;
        helpTG();
    }

    @Test
    public void escRecursiveInvariant2() {
        expectedExit = -1;
        helpTG();
    }

    @Test
    public void testquant() {
        expectedExit = -1;
        helpTG("--code-math=bigint");
    }

    @Test
    public void constructorDefaults() {
        expectedExit = 0;
        helpTG();
    }

    @Test
    public void escInlineLoop() {
        expectedExit = 0;
        helpTG();
    }


    // FIXME - reasoning about getClass
    @Test
    public void escBadCast() {
        expectedExit = 0;
        helpTG();
    }

    @Test
    public void escJLS() {
        expectedExit = 0;
        helpTG();
    }

    @Test
    public void escDoublyLinkedList() {
        helpTG();
    }

    @Test
    public void escModelFields() {
        helpTG("--code-math=bigint");
    }

    @Test
    public void escSimpleString() {
        // FIXME - CVC4 crashes or is long
        helpTG("--nonnull-by-default","-timeout=240");
    }

    @Test
    public void escSimpleString2() {
        helpTG("--nonnull-by-default");
    }

    @Test
    public void escSimpleString3() {
        helpTG("--nonnull-by-default");
    }

    @Test
    public void escDiverges2() {
        helpTG("--nonnull-by-default");
    }
    
    @Test @Ignore // FIXME - string comparisons for switch statements
    public void escStrings() {
        helpTG();
    }
    
    @Test
    public void escEnum() {
        helpTG();
    }
    
    @Test
    public void escLoop() {
        helpTG();
    }

    @Test
    public void escLoopModifies() {
        helpTG();
    }

    @Test
    public void escLoopAssignable() {
        expectedExit = 1;
        helpTG();
    }

    @Test
    public void escBodySpecs() {
        helpTG();
    }

    @Test
    public void escDeterministic() {
        helpTG();
    }

    @Test
    public void escDeterministic2() {
        helpTG();
    }

    @Test
    public void escFunction() {
        helpTG();
    }
    
    @Test
    public void escAbstractSpecs() {
        helpTG();
    }
    
    @Test
    public void escAbstractSpecs2() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
    public void escInvariants() {
        helpTG();
    }

    @Test
    public void escInvariants1() {
        helpTG();
    }

    @Test
    public void escInvariants2() {
        helpTG();
    }

    @Test
    public void escSeparateJml() {
        helpTCF("test/escSeparateJml/BankingExample.java","test/escSeparateJml","-classpath","test/escSeparateJml");
    }

    @Test
    public void escAssignableBug() {
        helpTG();
    }

    @Test
    public void escDerivedInvariant() {
        helpTG();
    }

    @Test
    public void escShortCircuit() {
        helpTG("--code-math=bigint");
    }
    
    @Test
    public void escRecursiveOld() {
        helpTG();
    }
    
    @Test
    public void escEnsuresInfeasible() {
        helpTG();
    }

    @Test
    public void escEnsuresInfeasible2() {
        helpTG();
    }

    @Test
    public void escConsInfeasible() {
        helpTG();
    }

    @Test
    public void preconditionDetail() {  // FIXME - no detail?
        helpTG();
    }

    @Test
    public void preconditionDetail2() {
        helpTG();
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
        helpTG();
    }

    @Test
    public void escLet() {
        helpTG("--solver-seed=9999");
    }
    
    @Test
    public void escElse() {
        helpTG();
    }

    @Test
    public void consfresh() {
        helpTG();
    }

    @Test
    public void specificationInterfaceDemo() {
        helpTG();
    }

    @Test
    public void implicitIteration() {
        helpTG();
    }

    @Test
    public void implicitIterationA() {
        helpTG();
    }



    
    @Test @Ignore // FIXME - ignore for now; implement with real specs
    public void escRawding() {
        helpTG("-specspath=test/escRawding","-code-math=safe");
    }
    
    // The following are really just typecheck problems

    @Test
    public void escPrivate() {
        helpTG();
    }

    @Test  // FIXME - not yet working
    public void customPrimitiveTypes() {
        expectedExit = 0;
        helpTG();
    }

    @Test
    public void enums() {
        expectedExit = 6;
        helpTG();
    }

    @Test @Ignore // FIXME - not yet implemented
    public void enums1() {
        expectedExit = 6;
        helpTG();
        //helpTG("-show","-method=m5c","-subexpressions");
    }

    @Test
    public void enums2() {
        expectedExit = 6;
        helpTG();
    }

    @Test
    public void datatype() {
        helpTG();
    }

    @Test // Basic problem is with the toString conversion of a \bigint, because of the -code-math=bigint setting of these
    public void factorial() {
        helpTG("--check-feasibility=none");//,"-code-math=java");
    }

    @Test @Ignore // FIXME - times out
    public void primeNumbers() {
        helpTG();
    }
    
    @Test
    public void splits() {
        expectedExit = 6;
        helpTG();
    }
    
    @Test
    public void splits2() {
        expectedExit = 6;
        helpTG();
    }
    
    @Test
    public void splits3() {
        expectedExit = 6;
        helpTG("--no-split");
    }
    
    @Test
    public void Dzmz() {
        helpTG();
    }

    @Test
    public void refining() {
        expectedExit = 6;
        helpTG();
    }

    @Test
    public void refiningBad() {
        expectedExit = 1;
        helpTG();
    }

    @Test @Ignore // FIXME - fix a problem with concatenation
    public void gcdcalculator() {
        helpTG();

    }

    @Test
    public void visibilitySimple() {
        expectedExit = 1;
        helpTG("--normal");
    }

    @Test
    public void requiresElse() {
        helpTG("--show=program"); // --show=program is part of test results
    }

    @Test
    public void tuple() {
        helpTG();
    }

    @Test
    public void tupleBad() {
        expectedExit = 1;
        helpTG();
    }

    @Test @Ignore // FIXME - not yet implemented
    public void anonymousCaptures() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test @Ignore // FIXME - needs implementation
    public void streams() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
    public void checkAsserts() {
        helpTG();
    }
    
    @Test
    public void callstacks() {
        helpTG();
    }
    
    @Test
    public void varargs() {
        helpTG();
    }
    
    @Test
    public void valuestrings() {
        helpTG();
    }
    
    @Test
    public void valuestringsBad() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test // FIXME - get an infeasibility when Arrays.binarySearch uses Arrays.contains
    public void binarySearch() {
        helpTG();
    }
    
    @Test
    public void modelImport1() {  // FIXME - the abbreviated type names make the message less understandable
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
    
    // Tests static imports
    @Test
    public void modelImport5() {
        helpTCF("test/modelImports/Test5.java","test/modelImports/test5","--check","-cp","test/modelImports");
    }
    
    // Tests static imports
    @Test
    public void modelImport6() {
        helpTCF("test/modelImports/Test6.java","test/modelImports/test6","--check","-cp","test/modelImports");
    }
    
    // Tests static imports
    @Test
    public void modelImport7() {
        helpTCF("test/modelImports/Test7.java","test/modelImports/test7","--check","-cp","test/modelImports");
    }

}
