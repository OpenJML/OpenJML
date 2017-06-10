package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.junit.runners.ParameterizedWithNames;

@RunWith(ParameterizedWithNames.class)
public class escoption extends EscBase {

    public escoption(String options, String solver) {
        super(options,solver);
    }
    
    @Parameters
    static public Collection<String[]> parameters() {
        return minQuantAndSolvers(solvers);
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        captureOutput = true;
        super.setUp();
        main.addOptions("-nullableByDefault"); // Because the tests were written this way
        main.addOptions("-quiet");
        main.addOptions("-checkFeasibility=none");
        //main.addOptions("-trace");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
 
    
    
    @Test
    public void testOption() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert(boolean bb, boolean b) { /*@ assume b; */ /*@assert false;*/   }\n" // Should fail because of the explicit assert false
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  @Options(\"-progress\") \n"
                +"  public static void bassert2(boolean bb, boolean b) { /*@ assume b; */ /*@assert !bb;*/   }\n" // Should fail because of the tautologically false assert
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert3(boolean bb, boolean b) { /*@ assume bb; */ /*@assert b;*/   }\n" // Should fail because of the unprovable assert
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method bassert",75
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method bassert2",76
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method bassert3",77
        );
        String out = output();
        org.junit.Assert.assertEquals(out,
              "Starting proof of tt.TestJava.bassert2(boolean,boolean) with prover !!!!" + eol + 
              "Completed proof of tt.TestJava.bassert2(boolean,boolean) with prover !!!! - with warnings" + eol
              ) ;

    }
    
    @Test
    public void testOption2() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"  @Options(\"-progress\") "
                +"public class TestJava { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert(boolean bb, boolean b) { /*@ assume b; */ /*@assert false;*/   }\n" // Should fail because of the explicit assert false
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  @Options(\"-quiet\") \n"
                +"  public static void bassert2(boolean bb, boolean b) { /*@ assume b; */ /*@assert !bb;*/   }\n" // Should fail because of the tautologically false assert
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert3(boolean bb, boolean b) { /*@ assume bb; */ /*@assert b;*/   }\n" // Should fail because of the unprovable assert
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method bassert",75
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method bassert2",76
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method bassert3",77
        );
        String out = output();
        org.junit.Assert.assertEquals(out,
                "Proving methods in tt.TestJava" + eol +
        		"Starting proof of tt.TestJava.TestJava() with prover !!!!" + eol +
        		"Completed proof of tt.TestJava.TestJava() with prover !!!! - no warnings" + eol +
                "Starting proof of tt.TestJava.bassert(boolean,boolean) with prover !!!!" + eol + 
                "Completed proof of tt.TestJava.bassert(boolean,boolean) with prover !!!! - with warnings" + eol +
                "Starting proof of tt.TestJava.bassert3(boolean,boolean) with prover !!!!" + eol + 
                "Completed proof of tt.TestJava.bassert3(boolean,boolean) with prover !!!! - with warnings" + eol +
                "Completed proving methods in tt.TestJava" + eol 
        		) ;

    }
    
    @Test
    public void testOption3() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"  @Options(\"-progress\") "
                +"public class TestJava { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert(boolean bb, boolean b) { /*@ assume b; */ /*@assert false;*/   }\n" // Should fail because of the explicit assert false
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  @Options(\"-quiet\") \n"
                +"  public static void bassert2(boolean bb, boolean b) { /*@ assume b; */ /*@assert !bb;*/   }\n" // Should fail because of the tautologically false assert
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert3(boolean bb, boolean b) { /*@ assume bb; */ /*@assert b;*/   }\n" // Should fail because of the unprovable assert
                +"}\n"
                +"class A { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert(boolean bb, boolean b) { /*@ assume b; */ /*@assert false;*/   }\n" // Should fail because of the explicit assert false
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method bassert",75
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method bassert2",76
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method bassert3",77
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method bassert",75
        );
        String out = output();
        org.junit.Assert.assertEquals(out,
                "Proving methods in tt.TestJava" + eol +
        		"Starting proof of tt.TestJava.TestJava() with prover !!!!" + eol +
        		"Completed proof of tt.TestJava.TestJava() with prover !!!! - no warnings" + eol +
                "Starting proof of tt.TestJava.bassert(boolean,boolean) with prover !!!!" + eol + 
                "Completed proof of tt.TestJava.bassert(boolean,boolean) with prover !!!! - with warnings" + eol +
                "Starting proof of tt.TestJava.bassert3(boolean,boolean) with prover !!!!" + eol + 
                "Completed proof of tt.TestJava.bassert3(boolean,boolean) with prover !!!! - with warnings" + eol +
                "Completed proving methods in tt.TestJava" + eol 
              ) ;

    }
    
    
}

