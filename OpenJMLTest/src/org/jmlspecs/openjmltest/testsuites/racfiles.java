package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.RacBase;

import static org.junit.Assert.fail;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Ignore;
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
 * 'test'
 * <LI> add a test to this class - typically named similarly to the folder
 * containing the source data
 * </UL>
 */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racfiles extends RacBase {

    @Override
    @Before
    public void setUp() throws Exception {
        super.setUp();
    }
    
    @Test
    public void racchoose() {
        helpCompileRun("T");
    }
    
    @Test
    public void racJMLfunctionality() {
        helpCompileRun("racJMLfunctionality");
    }

    @Test
    public void rac1() {
        expectedRACExit = 1;
        helpCompileRun("Bug1","--rac-java-checks");
    }

    @Test
    public void rac1a() {
        helpCompileRun("Bug1");
    }

    @Test // Originally a Stack overflow because of recursive check of invariant
    public void racbug1() {
        expectedRACExit = 1;
        helpCompileRun("Add");
    }

    @Test // Originally a Stack overflow because of recursive check of invariant
    public void racStackTrace() {
        helpCompileRun("CantCompileRAC");
    }

    @Test // Originally crashed because of a model method in a library class
    public void racPoint() {
        helpCompileRun("Point");
    }

    @Test // Originally crashed because of a model method in a library class
    public void racPoint2() {
        helpCompileRun("Point");
    }

    @Test
    public void firstTest() {
        helpCompileRun("FirstTest","--rac-java-checks","--rac-check-assumptions");
    }

    @Test
    public void uniqueList() {
        helpCompileRun("UniqueList","--rac-java-checks","--rac-check-assumptions");
    }

    @Test 
    public void uniqueListBug1() {
        helpCompileRun("UniqueListBug1","--rac-java-checks","--rac-check-assumptions");
    }

    @Test 
    public void uniqueListBug2() {
        helpCompileRun("UniqueListBug2");
    }

    @Test
    public void testDecimal() {
        helpCompileRun("sv_rac.Decimal");
    }

    @Test
    public void testDecimal2() {
        helpCompileRun("sv_rac/Decimal");
    }
    
    @Test
    public void Dzmz() {
        expectedRACExit = 1;
        helpCompileRun("Dzmz","--rac-java-checks");
    }
    
    @Test
    public void gitbug869() {
        expectedExit = 1;
        helpCompileOnly("--specs-path=test/gitbug869");
    }
    
    @Test
    public void gitbug877() {
        helpCompileRun("ZZ");
    }
    
    @Test
    public void gitbug879() {
        expectedRACExit = 1;
        helpCompileRun("ArrayUtils","--rac-compile-to-java-assert");
    }
    
    @Test
    public void racWithMethods() {
        helpCompileRun("TestInv");
    }

    @Test
    public void racNoModel1() {
        helpRac("test/racNoModel","test/racNoModel/test1","NoModelTest","--rac-missing-model-field-rep=skip");
    }

    @Test
    public void racNoModel2() {
        expectedExit = 1;
        helpRac("test/racNoModel","test/racNoModel/test2","NoModelTest","--rac-missing-model-field-rep=fail");
    }

    @Test
    public void racNoModel3() {
        helpRac("test/racNoModel","test/racNoModel/test3","NoModelTest","--rac-missing-model-field-rep=zero");
    }

    @Test
    public void racNoModel4() {
        helpRac("test/racNoModel","test/racNoModel/test4","NoModelTest","--rac-missing-model-field-rep=skip-quiet");
    }

    @Test
    public void racNoModel5() {
        helpRac("test/racNoModel","test/racNoModel/test5","NoModelTest","--rac-missing-model-field-rep=zero-quiet");
    }

    @Test
    public void racNoModel6() {
        expectedExit = 2;
        runrac=false;
        helpRac("test/racNoModel","test/racNoModel/test6","NoModelTest","--rac-missing-model-field-rep=zzz");
    }

    @Test
    public void racNoModel7() { // Same result as test1
        helpRac("test/racNoModel","test/racNoModel/test1","NoModelTest","--rac-missing-model-field-rep=");
    }
    
    @Test
    public void racNoModelInh1() {
        helpRac("test/racNoModelInh","test/racNoModelInh/test1","NoModelTest","--rac-missing-model-field-rep=skip");
    }

    @Test
    public void racNoModelInh2() {
        expectedExit = 1;
        helpRac("test/racNoModelInh","test/racNoModelInh/test2","NoModelTest","--rac-missing-model-field-rep=fail");
    }

    @Test
    public void racNoModelInh3() {
        helpRac("test/racNoModelInh","test/racNoModelInh/test3","NoModelTest","--rac-missing-model-field-rep=zero");
    }

    @Test
    public void racNoModelInh4() {
        helpRac("test/racNoModelInh","test/racNoModelInh/test4","NoModelTest","--rac-missing-model-field-rep=skip-quiet");
    }

    @Test
    public void racNoModelInh5() {
        helpRac("test/racNoModelInh","test/racNoModelInh/test5","NoModelTest","--rac-missing-model-field-rep=zero-quiet");
    }

    @Test
    public void racNoModelInh6() {
        expectedExit = 2;
        runrac=false;
        helpRac("test/racNoModelInh","test/racNoModelInh/test6","NoModelTest","--rac-missing-model-field-rep=zzz");
    }

    @Test
    public void racNoModelInh7() { // Same result as test1
        expectedExit = 0;
        helpRac("test/racNoModelInh","test/racNoModelInh/test1","NoModelTest","--rac-missing-model-field-rep=");
    }

    @Test
    public void racMainActivity() {
        runrac = false; // FIXME: Don't try running executable until we supply some input
        //rac = new String[]{jdk, "-classpath","bin"+z+"bin-runtime"+z+"testcompiles"+z+"test/racaddng/jmlunitng.jar",null};
        helpCompileRun("MainActivity");
    }


    @Test
    public void racMainActivityMicro() {
        helpCompileRun("CharAt");
    }

    @Test // FIXME - should we allow and compensate for \result in an \old environment
    public void racold() {
        expectedExit = 1;
        runrac = false;
        helpCompileRun("ArrayExample");
    }
    
    @Test
    public void racHans2() {
        rac = new String[]{jdk, "-ea", "-classpath","../OpenJML/bin"+z+"../OpenJML/bin-runtime"+z+"testcompiles/"+getTestName()+z+"test/hans/OpenJMLTest/bin"+z+"test/hans/icecapSDK/src",null};

        runrac = true;
        helpRac("test/racHans2/account",
                "test/racHans2",
                "account.AllTests",
                "-cp","test/hans/OpenJMLTest/bin"+z+"test/hans/icecapSDK/src"+z+"test/racHans2",
                //"-rac",
                "--specs-path","test/racHans2/specs",
                "--rac-check-assumptions","--rac-java-checks","--show-not-implemented","--nullable-by-default","-Xlint:none"
                );
    }

    @Test
    public void racHansStorage() {
    	expectedRACExit = 0;
    	helpRac("test/racHansStorage/StorageParameters.java","test/racHansStorage","StorageParameters","--rac-check-assumptions","--specs-path=test/racHansStorage");
    	rac = null;
    }

    @Test
    public void racHansStorageA() {
    	expectedRACExit = 0;
    	helpRac("test/racHansStorage/StorageParameters.java","test/racHansStorageA","StorageParameters","--rac-check-assumptions","--specs-path=test/racHansStorage","--nullable-by-default");
    	rac = null;
    }

    @Test
    public void racHansStorageB() {
        expectedRACExit = 0;
    	helpRac("test/racHansStorageB/StorageParameters.java","test/racHansStorageB","StorageParameters","--rac-check-assumptions","--specs-path=test/racHansStorageB");
    	rac = null;
    }

    @Test // Bug in that some annotations had to be in the .java file, not the .jml, fixed
    public void racHansStorageC() {
        expectedRACExit = 0;
    	helpRac("test/racHansStorageC/StorageParameters.java","test/racHansStorageC","StorageParameters","--rac-check-assumptions","--specs-path=test/racHansStorageC");
    	rac = null;
    }

    @Test  // Bug in that import statements must be in .java files, not .jml // FIXME - partially fixed - .jml imports are merged into .java imports
    public void racHansStorageD() {
        expectedRACExit = 0;
    	helpRac("test/racHansStorageD/StorageParameters.java","test/racHansStorageD","StorageParameters","--rac-check-assumptions","--specs-path=test/racHansStorageD");
    	rac = null;
    }
    
    @Test
    public void racNoGhostField() {
        helpCompileRun("Magic","-jmltesting");
    }
    
    @Test public void gitbug500c() {
        helpCompileOnly("--rac-missing-model-field-rep=skip-quiet");  // Just RAC compilation - did have a RAC compile crash
    }

    @Test public void gitbug500d() {
        helpRac("test/gitbug500c", "test/gitbug500d", null, "--rac-missing-model-field-rep=zero-quiet");  // Just RAC compilation - RAC compile crash
    }

    @Test public void gitbug529() {
        //helpCompileOnly();  // Just RAC compilation  // FIXME - try running also
        helpCompileRun("T");
    }

    @Test
    public void gitbug600() {
        expectedExit = 0;
        helpCompileOnly("--rac-check-assumptions","--rac-precondition-entry");
    }
    
    @Test
    public void gitbug532() {
        helpCompileRun("Big","--no-rac-check-assumptions");
    }

    @Test
    public void gitbug532a() {
        helpCompileRun("Big");
    }

    @Test
    public void gitbug533() {
        helpCompileRun("TestSum","--rac-check-assumptions");
    }

    @Test
    public void gitbug533a() {
        helpCompileRun("TestSum");
    }

    @Test
    public void gitbug534() {
        helpCompileRun("S");
    }

    @Test
    public void gitbug536() {
        helpCompileRun("Test536","-code-math=safe","-spec-math=safe","--no-rac-check-assumptions");
    }

    @Test
    public void gitbug536a() {
        runrac = true;
        expectedRACExit = 0;
        helpRac("test/gitbug536","test/gitbug536a","Test536","-code-math=safe","-spec-math=bigint");
    }

    @Test
    public void gitbug542() {
        helpCompileRun("Test542");
    }

    @Test
    public void gitbug542a() {
        runrac = true;
        expectedRACExit = 0;
        helpRac("test/gitbug542","test/gitbug542a","Test542","--spec-math=java");
    }

    @Test
    public void gitbug542b() {
        runrac = true;
        expectedRACExit = 0;
        helpRac("test/gitbug542","test/gitbug542b","Test542","--spec-math=safe");
    }

    @Test
    public void gitbug542c() {
        runrac = true;
        expectedRACExit = 0;
        helpRac("test/gitbug542","test/gitbug542c","Test542","--spec-math=bigint");
    }

    @Test
    public void gitbug547() {
        helpCompileRun("Test547");
    }

    @Test
    public void gitbug547a() {
        expectedExit = 1;
        expectedRACExit = 0;
        helpCompileRun("Test547");
    }

    @Test
    public void gitbug547b() {
        expectedExit = 1;
        helpCompileRun("Test547");
    }

    @Test
    public void gitbug547c() {
        expectedRACExit = 1;
        helpCompileRun("Test547");
    }

    @Test
    public void gitbug547d() {
        expectedRACExit = 1;
        helpCompileRun("Test547");
    }

    @Test
    public void gitbug548rac() {
        helpCompileRun("Test");
    }

    @Test
    public void gitbug548racB() {
        helpCompileRun("Test");
    }

    @Test
    public void gitbug578() {
        helpCompileRun("Test");
    }

    @Test
    public void gitbug599() {
        helpCompileRun("Prime");
    }

    @Test
    public void gitbug627a() {
        helpCompileRun("Test");
    }

    @Test
    public void gitbug688racA() {
        runrac = true;
        expectedRACExit = 0;
        helpRac("test/gitbug688","test/gitbug688racA","DayTimeMain","-spec-math=bigint");
    }

    @Test
    public void gitbug688racB() {
        runrac = true;
        expectedRACExit = 0;
        helpRac("test/gitbug688","test/gitbug688racB","DayTimeMain","-spec-math=safe");
    }

    @Test
    public void gitbug688racC() {
        runrac = true;
        expectedRACExit = 0;
        helpRac("test/gitbug688","test/gitbug688racC","DayTimeMain","-spec-math=java");
    }

    @Test
    public void gitbug807() {
        helpCompileRun("Foo","-Xlint:none");
    }

    @Test
    public void gitbug766() {
        helpCompileOnly();
    }

    @Test
    public void gitbug809() {
        runrac = false;  // FIXME - why not run
        helpCompileRun("Parent");
    }
    
    @Test
    public void gitbug860() {
        // The bug produces error output
        helpCompileRun("Test");
    }
    
    @Test
    public void gitbug861() {
        helpCompileRun("Test");
    }

    @Test
    public void gitbug885() {
        helpCompileOnly();
    }

    @Test
    public void gitbug932() {
        helpCompileRun("M");
    }

    @Test
    public void gitbug932a() {
        helpCompileRun("M");
    }

    @Test
    public void sfbug413() {
        helpCompileRun("Main");
    }

    @Test
    public void sfbug402() {
        runrac = false; // FIXME - why false
        helpCompileRun("Main","--rac-missing-model-field-rep=zero-quiet");
    }

    @Test
    public void sfbug420() {
        helpCompileRun("stack.StackImpl");
    }

    @Test
    public void sfbug396() {
        runrac = false; // FIXME - why false
        helpCompileRun("Main");
    }

    @Test @Ignore // not a complete program; appears to be an abandoned demo
    public void racRM1() {
        helpCompileRun("MaxSumArray","-code-math=java","-spec-math=java");
    }

    @Test @Ignore // not a complete program; appears to be an abandoned demo
    public void racRM1a() {
        expectedRACExit = 0;
        helpRac("test/racRM1","test/racRM1","MaxSumArray","-code-math=safe","-spec-math=bigint");
    }

    @Test @Ignore // not a complete program; appears to be an abandoned demo
    public void racRM2() {
        helpCompileRun("MaxSumArray","-code-math=java","-spec-math=java");
    }

    @Test @Ignore // not a complete program; appears to be an abandoned demo
    public void racRM2a() {
        expectedRACExit = 0;
        helpRac("test/racRM2","test/racRM2","MaxSumArray","-code-math=safe","-spec-math=bigint");
    }
    
    @Test
    public void record1() {
        helpCompileRun("RR");
    }
    
    @Test
    public void returnNullity() {
        helpCompileRun("ReturnNullable");
    }
    
    // Only these two textBlock tests have main methods (FIXME - is that OK?)
    @Test
    public void textBlock4() {
        helpCompileRun("Test");
    }
    
    @Test
    public void textBlock4b() {
        helpCompileRun("Test");
    }
    
    @Test
    public void choosex() {
        helpCompileRun("Demo");
    }
    
    @Test
    public void racprinting() {
        helpCompileRun("PR", "--rac-java-checks");
    }
    
    @Test
    public void racbehaviors() {
        helpCompileRun("Behaviors");
    }
    
    @Test
    public void byteQuant() {
        helpCompileRun("Test");
    }
    
    @Test
    public void termination() {
        helpCompileRun("Termination");
    }
    
    @Test
    public void terminationBad() {
        helpCompileRun("Test");
    }
    
    @Test
    public void gitbug862() {
        helpCompileRun("Test");
    }
    
    @Test
    public void gitbug864() {
        helpCompileRun("ListUtils");
    }
    
    @Test
    public void gitbug865() {
        helpCompileOnly("--warn=missing-measured-by");
    }
    
    @Test
    public void gitbug866() {
        helpCompileRun("ConsecutiveChecker");
    }
    
    @Test
    public void gitbug872() {
        helpCompileRun("BitRotator");
    }
    
    @Test
    public void gitbug873() {
        helpCompileRun("StringUtils");
    }
    
    @Test
    public void gitbug874() {
        helpCompileRun("SequenceUtilsTest");
    }
    
    @Test
    public void gitbug875() {
        helpCompileRun("TestSets");
    }
    
    @Test
    public void gitbug940() {
        helpCompileRun("Test");
    }
    
    @Test
    public void gitbug950() {
        helpCompileRun("p.Test");
        Assert.assertTrue(new java.io.File(outdir + "/module-info.class").exists());
    }
    
    @Test
    public void textRac() {
        helpCompileRun("BL");
    }
}
