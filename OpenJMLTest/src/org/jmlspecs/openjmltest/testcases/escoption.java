package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escoption extends EscBase {

    public escoption(String options, String solver) {
        super(options,solver);
    }
    
    @Parameters
    static public Collection<String[]> parameters() {
        return EscBase.parameters();
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        captureOutput = true;
        super.setUp();
        main.addOptions("-nullableByDefault"); // Because the tests were written this way
        main.addOptions("-quiet");
        main.addOptions("-checkFeasibility=none","-no-require-white-space");
        //main.addOptions("-trace");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
 
    @Test
    public void testOptionValueBoolean() {
    	collectOutput(false);
    	Assert.assertEquals("openjml",JmlOption.value(main.context(), JmlOption.LANG));
    	Assert.assertEquals("openjml",JmlOption.value(main.context(), JmlOption.LANG));
    	Assert.assertEquals("openjml",JmlOption.value(main.context(), "--lang"));
    	Assert.assertEquals("openjml",JmlOption.value(main.context(), "--lang"));
    	JmlOption.putOption(main.context(), JmlOption.LANG, "jml");
    	Assert.assertEquals("jml",JmlOption.value(main.context(), JmlOption.LANG));
        JmlOption.putOption(main.context(), JmlOption.LANG, "openjml");
        Assert.assertEquals("openjml",JmlOption.value(main.context(), JmlOption.LANG));
    	main.addOptions("-lang=jml");
    	Assert.assertEquals("jml",JmlOption.value(main.context(), JmlOption.LANG));
        main.addOptions("-lang=openjml");
        Assert.assertEquals("openjml",JmlOption.value(main.context(), JmlOption.LANG));
    	JmlOption.putOption(main.context(), JmlOption.LANG, "openjml");
    	Assert.assertEquals("openjml",JmlOption.value(main.context(), JmlOption.LANG));
        String out = output();
        org.junit.Assert.assertEquals("",out);
    }
    
    @Test
    public void testOptionValue() {
    	collectOutput(false);
    	Assert.assertEquals(null,JmlOption.value(main.context(), JmlOption.METHOD));
    	Assert.assertEquals(null,JmlOption.value(main.context(), "-method"));
    	JmlOption.putOption(main.context(), JmlOption.METHOD, "xxx");
    	Assert.assertEquals("xxx",JmlOption.value(main.context(), JmlOption.METHOD));
    	JmlOption.putOption(main.context(), JmlOption.METHOD, null);
    	Assert.assertEquals(null,JmlOption.value(main.context(), JmlOption.METHOD));
    	JmlOption.putOption(main.context(), JmlOption.METHOD, "");
    	Assert.assertEquals("",JmlOption.value(main.context(), JmlOption.METHOD));
        String out = output();
        org.junit.Assert.assertEquals("",out);
    }
    
    @Test // FIXME bassert3 not printed -- quiet does not turn back to progress
    public void testOption() {
    	main.addOptions("-quiet");
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
        org.junit.Assert.assertEquals(
              "Starting proof of tt.TestJava.bassert2(boolean,boolean) with prover !!!!" + eol + 
              "Completed proof of tt.TestJava.bassert2(boolean,boolean) with prover !!!! - with warnings" + eol
              ,out) ;

    }
    
    @Test // FIXME bassert3 not printed -- quiet does not turn back to progress
    public void testOption2() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"  @Options({\"-progress\",\"-checkFeasibility=none\"}) "
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
        org.junit.Assert.assertEquals(
                "Proving methods in tt.TestJava" + eol +
        		"Starting proof of tt.TestJava.TestJava() with prover !!!!" + eol +
        		"Completed proof of tt.TestJava.TestJava() with prover !!!! - no warnings" + eol +
                "Starting proof of tt.TestJava.bassert(boolean,boolean) with prover !!!!" + eol + 
                "Completed proof of tt.TestJava.bassert(boolean,boolean) with prover !!!! - with warnings" + eol +
                "Starting proof of tt.TestJava.bassert3(boolean,boolean) with prover !!!!" + eol + 
                "Completed proof of tt.TestJava.bassert3(boolean,boolean) with prover !!!! - with warnings" + eol +
                "Completed proving methods in tt.TestJava" + eol 
        		,out) ;

    }
    
    @Test // FIXME bassert3 not printed -- quiet does not turn back to progress
    public void testOption3() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"  @Options({\"-progress\",\"-checkFeasibility=none\"}) "
                +"public class TestJava { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert(boolean bb, boolean b) { /*@ assume b; */ /*@ assert false;*/   }\n" // Should fail because of the explicit assert false
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  @Options(\"-quiet\") \n"
                +"  public static void bassert2(boolean bb, boolean b) { /*@ assume b; */ /*@ assert !bb;*/   }\n" // Should fail because of the tautologically false assert
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert3(boolean bb, boolean b) { /*@ assume bb; */ /*@ assert b;*/   }\n" // Should fail because of the unprovable assert
                +"}\n"
                +"class A { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert(boolean bb, boolean b) { /*@ assume b; */ /*@ assert false;*/   }\n" // Should fail because of the explicit assert false
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method bassert",76
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method bassert2",77
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method bassert3",78
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method bassert",76
        );
        String out = output();
        org.junit.Assert.assertEquals(
                "Proving methods in tt.TestJava" + eol +
        		"Starting proof of tt.TestJava.TestJava() with prover !!!!" + eol +
        		"Completed proof of tt.TestJava.TestJava() with prover !!!! - no warnings" + eol +
                "Starting proof of tt.TestJava.bassert(boolean,boolean) with prover !!!!" + eol + 
                "Completed proof of tt.TestJava.bassert(boolean,boolean) with prover !!!! - with warnings" + eol + 
                "Starting proof of tt.TestJava.bassert3(boolean,boolean) with prover !!!!" + eol + 
                "Completed proof of tt.TestJava.bassert3(boolean,boolean) with prover !!!! - with warnings" + eol +
                "Completed proving methods in tt.TestJava" + eol 
              ,out) ;

    }
    
    @Test
    public void testSkipped() {
    	main.addOptions("-progress","--show-skipped","-method=bassert","-exclude=tt.TestJava.bassert(boolean,boolean)","-checkFeasibility=none");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert(boolean bb, boolean b) {   }\n"
                +"  //@ requires true;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert() {   }\n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert2(boolean bb, boolean b) {    }\n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  //@ skipesc \n"
                +"  public static void bassert3(boolean bb, boolean b) {  }\n" 
                +"}\n"
        );
        String out = output();
        org.junit.Assert.assertEquals(
                "Proving methods in tt.TestJava" + eol +
        		"Skipping proof of tt.TestJava.TestJava() (excluded by -method)" + eol +
                "Skipping proof of tt.TestJava.bassert(boolean,boolean) (excluded by -method)" + eol + 
                "Starting proof of tt.TestJava.bassert() with prover !!!!" + eol + 
                "Completed proof of tt.TestJava.bassert() with prover !!!! - no warnings" + eol +
                "Skipping proof of tt.TestJava.bassert2(boolean,boolean) (excluded by -method)" + eol + 
                "Skipping proof of tt.TestJava.bassert3(boolean,boolean) (excluded by skipesc)" + eol + 
                "Completed proving methods in tt.TestJava" + eol 
              ,out) ;

    }
    
    @Test
    public void testNoSkipped() {
    	main.addOptions("-progress","--no-show-skipped","-method=bassert","-exclude=tt.TestJava.bassert(boolean,boolean)","-checkFeasibility=none");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert(boolean bb, boolean b) {   }\n"
                +"  //@ requires true;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert() {   }\n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert2(boolean bb, boolean b) {    }\n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  //@ skipesc \n"
                +"  public static void bassert3(boolean bb, boolean b) {  }\n" 
                +"}\n"
        );
        String out = output();
        org.junit.Assert.assertEquals(
                "Proving methods in tt.TestJava" + eol +
                "Starting proof of tt.TestJava.bassert() with prover !!!!" + eol + 
                "Completed proof of tt.TestJava.bassert() with prover !!!! - no warnings" + eol +
                "Completed proving methods in tt.TestJava" + eol 
              ,out) ;

    }
    
    
    @Test
    public void testSkippedDefault() {
    	main.addOptions("-progress","--method=bassert","--exclude=tt.TestJava.bassert(boolean,boolean)","--check-feasibility=none");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert(boolean bb, boolean b) {   }\n"
                +"  //@ requires true;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert() {   }\n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert2(boolean bb, boolean b) {    }\n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  //@ skipesc \n"
                +"  public static void bassert3(boolean bb, boolean b) {  }\n" 
                +"}\n"
        );
        String out = output();
        org.junit.Assert.assertEquals(
                "Proving methods in tt.TestJava" + eol +
        		"Skipping proof of tt.TestJava.TestJava() (excluded by -method)" + eol +
                "Skipping proof of tt.TestJava.bassert(boolean,boolean) (excluded by -method)" + eol + 
                "Starting proof of tt.TestJava.bassert() with prover !!!!" + eol + 
                "Completed proof of tt.TestJava.bassert() with prover !!!! - no warnings" + eol +
                "Skipping proof of tt.TestJava.bassert2(boolean,boolean) (excluded by -method)" + eol + 
                "Skipping proof of tt.TestJava.bassert3(boolean,boolean) (excluded by skipesc)" + eol + 
                "Completed proving methods in tt.TestJava" + eol 
              ,out) ;

    }
    
    @Test
    public void testNowarnA() {
        main.addOptions("-no-jmltesting");
        helpTCX("NoWarn",
            """
            public class NoWarn extends A {
            
              //@ ensures true;
              public void m() {
                //@ assert false;
              }
           }
           class A {
             //@ ensures true;
             public void m() {}
           }
           """
           ,"/NoWarn.java:3: warning: Method m overrides parent class methods and so its specification should begin with 'also' (NoWarn.m() overrides A.m())",8
           ,"/NoWarn.java:5: verify: The prover cannot establish an assertion (Assert) in method m",10
           );

    }
    
    @Test
    public void testNowarnB() {
        com.sun.tools.javac.util.Options.instance(context).put("-Xlint:none",""); // desugaring of -nowarn -- see Option.java
        main.addOptions("-no-jmltesting");
        helpTCX("NoWarn",
            """
            public class NoWarn extends A {
            
              //@ ensures true;
              public void m() {
                //@ assert false;
              }
            }
            class A {
              //@ ensures true;
              public void m() {}
            }
            """
            ,"/NoWarn.java:5: verify: The prover cannot establish an assertion (Assert) in method m",9
            );

       }
}

