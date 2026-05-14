package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.fail;

import java.io.*;
import java.util.*;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.*;
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
    
    public void helpEscFile(String n, String d, String ... opts) {
        super.helpEscFile(n, d, opts);
    }

    public void helpEscSimple(String... opts) {
        super.helpEscSimple(opts);
    }
    
    @Test // Order of errors is somewhat non-deterministic
    public void bag() {
        expectedExit = 6;
        helpEscSimple("--esc-max-warnings=1","--check-feasibility=none");
    }

    @Test
    public void bagModified() {
        expectedExit = 0;
        helpEscSimple("--check-feasibility=none");
    }

    @Test
    public void loopExercises() {
        expectedExit = 0;
        helpEscSimple("--exclude=gauss,gauss2","--check-feasibility=basic");
    }

    @Test // FIXME - nonlinear inference -- times out
    public void loopExercises2() {
        expectedExit = 0;
        helpEscFile("test/loopExercises","test/loopExercises2","--method=gauss,gauss2");
    }

    @Test
    public void oldproblem() {
        helpEscSimple();
    }

    @Test
    public void feasible() {
        helpEscSimple();
    }

    @Test
    public void escINF() {
        helpEscSimple();
    }

    @Test
    public void escAdd() {
        expectedExit = 0;
        helpEscSimple("--code-math=bigint");
    }

    @Test
    public void escAdd2() {
        expectedExit = 0;
        helpEscSimple();
    }

    @Test
    public void escArrayCopy() {
        expectedExit = 0;
        helpEscSimple();
    }

    @Test
    public void escClone() {
        expectedExit = 0;
        helpEscSimple();
    }
    
    @Test
    public void esc2DArray() {
        //addOptions("--method=m","--progress","--show");
        helpEscSimple();
    }

    @Test
    public void esc2DArray2() {
        expectedExit = 0;
        helpEscSimple();
    }

    @Test @Ignore // FIXME - axioms for multi-dimensional arrays
    public void esc2DTranspose() {
        expectedExit = 0;
        helpEscSimple();
    }

    @Test @Ignore // FIXME - Specs need improvement
    public void verifythis2019_1() {
        expectedExit = 0;
        helpEscName("verifythis2019_1","--check-feasibility=none", "--code-math=bigint"); // FIXME - feasibility check times out // FIXME - not sure code-math option is needed
    }

    @Test
    public void verifythis2019_2() {
        expectedExit = 0;
        helpEscName("verifythis2019_2","--solver-seed=42", "--code-math=bigint"); // FIXME - not sure code-math option is needed
    }

    @Test
    public void escCashAmountPrivate2() {   // FIXME - with demo files?
        expectedExit = 0;
        helpEscFile("test/escCashAmountPrivate2/CashAmountOnlyPrivate.java","test/escCashAmountPrivate2","-classpath","test/escCashAmountPrivate2","-method=increase","-checkFeasibility=none");
    }

    @Test
    public void escVector() {
        expectedExit = 6;
        helpEscSimple("--code-math=java","--exclude=copyIntoOK,copyIntoA");
    }

    @Test
    public void escVectorA() {
        expectedExit = 6;
        helpEscSimple("--code-math=java","--method=copyIntoOK,copyIntoA");
    }

    @Test
    public void escDMZLoop() {
        expectedExit = 6;
        helpEscSimple("--method=findMax");
    }

    @Test
    public void escDMZLoopA() {
        expectedExit = 0;
        helpEscSimple("--method=findMax","--code-math=bigint","--spec-math=bigint");
    }

    @Test
    public void escDMZLoopB() {
        expectedExit = 0;
        helpEscSimple("--method=findMax","--code-math=bigint","--spec-math=bigint");
    }

    @Test
    public void escRecursiveInvariant() {
        expectedExit = -1;
        helpEscSimple();
    }

    @Test
    public void escRecursiveInvariant2() {
        expectedExit = -1;
        helpEscSimple();
    }

    @Test
    public void testquant() {
        expectedExit = -1;
        helpEscSimple("--code-math=bigint");
    }

    @Test
    public void constructorDefaults() {
        expectedExit = 0;
        helpEscSimple();
    }

    @Test
    public void escInlineLoop() {
        expectedExit = 0;
        helpEscSimple();
    }


    // FIXME - reasoning about getClass
    @Test
    public void escBadCast() {
        expectedExit = 0;
        helpEscSimple();
    }

    @Test
    public void escJLS() {
        expectedExit = 0;
        helpEscSimple();
    }

    @Test
    public void escDoublyLinkedList() {
        helpEscSimple();
    }

    @Test
    public void escModelFields() {
        helpEscSimple("--code-math=bigint");
    }

    @Test
    public void escSimpleString() {
        // FIXME - CVC4 crashes or is long
        helpEscSimple("--nonnull-by-default","-timeout=240");
    }

    @Test
    public void escSimpleString2() {
        helpEscSimple("--nonnull-by-default");
    }

    @Test
    public void escSimpleString3() {
        helpEscSimple("--nonnull-by-default");
    }

    @Test
    public void escDiverges2() {
        helpEscSimple("--nonnull-by-default");
    }
    
    @Test @Ignore // FIXME - string comparisons for switch statements
    public void escStrings() {
        helpEscSimple();
    }
    
    @Test
    public void escEnum() {
        helpEscSimple();
    }
    
    @Test
    public void escLoop() {
        helpEscSimple();
    }

    @Test
    public void escLoopModifies() {
        helpEscSimple();
    }

    @Test
    public void escLoopAssignable() {
        expectedExit = 1;
        helpEscSimple();
    }

    @Test
    public void escBodySpecs() {
        helpEscSimple();
    }

    @Test
    public void escDeterministic() {
        helpEscSimple();
    }

    @Test
    public void escDeterministic2() {
        helpEscSimple();
    }

    @Test
    public void escFunction() {
        helpEscSimple();
    }
    
    @Test
    public void escAbstractSpecs() {
        helpEscSimple();
    }
    
    @Test
    public void escAbstractSpecs2() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
    public void escInvariants() {
        helpEscSimple();
    }

    @Test
    public void escInvariants1() {
        helpEscSimple();
    }

    @Test
    public void escInvariants2() {
        helpEscSimple();
    }

    @Test
    public void escSeparateJml() {
        helpEscFile("test/escSeparateJml/BankingExample.java","test/escSeparateJml","-classpath","test/escSeparateJml");
    }

    @Test
    public void escAssignableBug() {
        helpEscSimple();
    }

    @Test
    public void escDerivedInvariant() {
        helpEscSimple();
    }

    @Test
    public void escShortCircuit() {
        helpEscSimple("--code-math=bigint");
    }
    
    @Test
    public void escRecursiveOld() {
        helpEscSimple();
    }
    
    @Test
    public void escEnsuresInfeasible() {
        helpEscSimple();
    }

    @Test
    public void escEnsuresInfeasible2() {
        helpEscSimple();
    }

    @Test
    public void escConsInfeasible() {
        helpEscSimple();
    }

    @Test
    public void preconditionDetail() {  // FIXME - no detail?
        helpEscSimple();
    }

    @Test
    public void preconditionDetail2() {
        helpEscSimple();
    }

    @Test // FIXME - still has problems with imports in JML files and with checks on field initializers
    public void escJml() {
        helpEscFile("test/escJml/Test.java","test/escJml","--specs-path=test/escJml/specs","--check-feasibility=none","--nonnull-by-default");
    }

    @Test
    public void escJml1() {
        helpEscFile("test/escJml1/StorageParameters.java","test/escJml1","--specs-path=test/escJml1/specs","--check-feasibility=none","--nonnull-by-default");
    }

    @Test
    public void escJml1a() {
        helpEscFile("test/escJml1a/StorageParameters.java","test/escJml1a","--specs-path=test/escJml1a/specs","--check-feasibility=none","--nullable-by-default");
    }

    @Test
    public void escJml2() {
        helpEscFile("test/escJml2/StorageParameters.java","test/escJml2","--specs-path=test/escJml2/specs","--check-feasibility=none");
    }

    @Test
    public void escJml3() {
        helpEscFile("test/escJml3/StorageParameters.java","test/escJml3","--specs-path=test/escJml2/specs","--check-feasibility=none");
    }

    @Test
    public void escDup() {
        helpEscSimple();
    }

    @Test
    public void escLet() {
        helpEscSimple("--solver-seed=9999");
    }
    
    @Test
    public void escElse() {
        helpEscSimple();
    }

    @Test
    public void consfresh() {
        helpEscSimple();
    }

    @Test
    public void specificationInterfaceDemo() {
        helpEscSimple();
    }

    @Test
    public void implicitIteration() {
        helpEscSimple();
    }

    @Test
    public void implicitIterationA() {
        helpEscSimple();
    }



    
    @Test @Ignore // FIXME - ignore for now; implement with real specs
    public void escRawding() {
        helpEscSimple("-specspath=test/escRawding","-code-math=safe");
    }
    
    // The following are really just typecheck problems

    @Test
    public void escPrivate() {
        helpEscSimple();
    }

    @Test  // FIXME - not yet working
    public void customPrimitiveTypes() {
        expectedExit = 0;
        helpEscSimple();
    }

    @Test
    public void enums() {
        expectedExit = 6;
        helpEscSimple();
    }

    @Test @Ignore // FIXME - not yet implemented
    public void enums1() {
        expectedExit = 6;
        helpEscSimple();
        //helpEscSimple("-show","-method=m5c","-subexpressions");
    }

    @Test
    public void enums2() {
        expectedExit = 6;
        helpEscSimple();
    }

    @Test
    public void datatype() {
        helpEscSimple();
    }

    @Test // Basic problem is with the toString conversion of a \bigint, because of the -code-math=bigint setting of these
    public void factorial() {
        helpEscSimple("--check-feasibility=none");//,"-code-math=java");
    }

    @Test @Ignore // FIXME - times out
    public void primeNumbers() {
        helpEscSimple();
    }
    
    @Test
    public void splits() {
        expectedExit = 6;
        helpEscSimple();
    }
    
    @Test
    public void splits2() {
        expectedExit = 6;
        helpEscSimple();
    }
    
    @Test
    public void splits3() {
        expectedExit = 6;
        helpEscSimple("--no-split");
    }
    
    @Test
    public void Dzmz() {
        helpEscSimple();
    }

    @Test
    public void record1() {
        expectedExit = 0;
        helpEscSimple();
    }

    @Test
    public void refining() {
        expectedExit = 6;
        helpEscSimple();
    }

    @Test
    public void refiningBad() {
        expectedExit = 1;
        helpEscSimple();
    }

    @Test @Ignore // FIXME - fix a problem with concatenation
    public void gcdcalculator() {
        helpEscSimple();

    }

    @Test
    public void visibilitySimple() {
        expectedExit = 1;
        helpEscSimple("--normal");
    }

    @Test
    public void requiresElse() {
        helpEscSimple("--show=program"); // --show=program is part of test results
    }

    @Test
    public void tuple() {
        helpEscSimple();
    }

    @Test
    public void tupleBad() {
        expectedExit = 1;
        helpEscSimple();
    }

    @Test @Ignore // FIXME - not yet implemented
    public void anonymousCaptures() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test @Ignore // FIXME - needs implementation
    public void streams() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test
    public void checkAsserts() {
        helpEscSimple();
    }
    
    @Test
    public void callstacks() {
        helpEscSimple();
    }
    
    @Test
    public void varargs() {
        helpEscSimple();
    }
    
    @Test
    public void valuestrings() {
        helpEscSimple();
    }
    
    @Test
    public void valuestringsBad() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Test // FIXME - get an infeasibility when Arrays.binarySearch uses Arrays.contains
    public void binarySearch() {
        helpEscSimple();
    }
    
    @Test
    public void modelImport1() {  // FIXME - the abbreviated type names make the message less understandable
        expectedExit = 1;
        helpEscFile("test/modelImports/Test1.java","test/modelImports/test1","--check","-cp","test/modelImports");
    }
    
    @Test
    public void modelImport2() {
        helpEscFile("test/modelImports/Test2.java","test/modelImports/test2","--check","-cp","test/modelImports");
    }
    
    @Test
    public void modelImport3() {
        expectedExit = 1;
        helpEscFile("test/modelImports/Test3.java","test/modelImports/test3","--check","-cp","test/modelImports");
    }
    
    @Test
    public void modelImport4() {
        expectedExit = 1;
        helpEscFile("test/modelImports/Test4.java","test/modelImports/test4","--check","-cp","test/modelImports");
    }
    
    // Tests static imports
    @Test
    public void modelImport5() {
        helpEscFile("test/modelImports/Test5.java","test/modelImports/test5","--check","-cp","test/modelImports");
    }
    
    // Tests static imports
    @Test
    public void modelImport6() {
        helpEscFile("test/modelImports/Test6.java","test/modelImports/test6","--check","-cp","test/modelImports");
    }
    
    // Tests static imports
    @Test
    public void modelImport7() {
        helpEscFile("test/modelImports/Test7.java","test/modelImports/test7","--check","-cp","test/modelImports");
    }

}
