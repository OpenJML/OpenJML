package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.fail;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Test;

/** These tests exercise the RAC checking.  They compile a test class 
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racnewWithSpecs extends RacBase {

    @Override
    public void setUp() throws Exception {
        testspecpath1 = "$A"+z+"$B"+z+"$SY";
        //noCollectDiagnostics = true; print = true;
        super.setUp();
        //main.addOptions("-verboseness=4");
        expectedNotes = 2;
        addOptions("-jmltesting");
        addOptions("--rac-show-source=line");
    }
    
    @Override
    public void tearDown() throws Exception {
        testspecpath1 = "$A"+z+"$B";
    }


    @Test public void testTypeOf() {
        expectedNotes = 4;
        helpTCX("tt.TestJava",
                   """
                   package tt; import static org.jmlspecs.lang.JML.*; public class TestJava {
                      public static void main(String[] args) {
                           m(new Object());
                           m(new String(""));
                           m(Boolean.TRUE);
                           System.out.println("END"); // FIXME - crash with using new String() with no argument
                      }
                   
                      //@ requires JML.informal("asd") && (\\lbl CLS (\\typeof(i)).erasure()) == Object.class;
                      static public void m(/*@nullable*/Object i) {
                          System.out.println("CLASS " + i.getClass());
                      }
                   }
                   """
                ,"LABEL CLS = class java.lang.Object" // precondition check by caller
                ,"LABEL CLS = class java.lang.Object" // precondition check by callee
                ,"CLASS class java.lang.Object"
                // FIXME?
                    // These model methods are defined, but the library classes are not compiled with RAC so the model methods do not exist.
//                ,"Skipping a specification clause because it contains an uncompiled model method: 'boolean java.lang.String.initialCharSequence"
//                ,"Skipping a specification clause because it contains an uncompiled model method: 'boolean java.lang.String.equals"
                ,"LABEL CLS = class java.lang.String"
                ,"/tt/TestJava.java:4: verify: JML precondition is false"
                ,"/tt/TestJava.java:10: verify: Associated declaration"
                ,"LABEL CLS = class java.lang.String"
                ,"/tt/TestJava.java:9: verify: JML precondition is false"
                ,"CLASS class java.lang.String"
                ,"LABEL CLS = class java.lang.Boolean"
                ,"/tt/TestJava.java:5: verify: JML precondition is false"
                ,"/tt/TestJava.java:10: verify: Associated declaration"
                ,"LABEL CLS = class java.lang.Boolean"
                ,"/tt/TestJava.java:9: verify: JML precondition is false"
                ,"CLASS class java.lang.Boolean"
                ,"END"
                );
        
    }

}
