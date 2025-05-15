package org.jmlspecs.openjmltest.testsuites;

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

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        captureOutput = true;
        super.setUp();
        main.addOptions("--nullable-by-default"); // Because the tests were written this way
        main.addOptions("--quiet");
        main.addOptions("--check-feasibility=none","--no-require-white-space");
        //main.addOptions("-trace");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
 
    @Test
    public void testOptionValueBoolean() {
    	collectOutput(false);
    	Assert.assertEquals("A", "openjml",JmlOption.value(main.context(), JmlOption.LANG));
    	Assert.assertEquals("B", "openjml",JmlOption.value(main.context(), JmlOption.LANG));
    	Assert.assertEquals("C", "openjml",JmlOption.value(main.context(), "--lang"));
    	Assert.assertEquals("D", "openjml",JmlOption.value(main.context(), "--lang"));
    	JmlOption.putOption(main.context(), JmlOption.LANG, "jml");
    	Assert.assertEquals("E", "jml",JmlOption.value(main.context(), JmlOption.LANG));
        JmlOption.putOption(main.context(), JmlOption.LANG, "openjml");
        Assert.assertEquals("F", "openjml",JmlOption.value(main.context(), JmlOption.LANG));
    	main.addOptions("--lang=jml");
    	Assert.assertEquals("G", "jml",JmlOption.value(main.context(), JmlOption.LANG));
        main.addOptions("--lang=openjml");
        Assert.assertEquals("H", "openjml",JmlOption.value(main.context(), JmlOption.LANG));
    	JmlOption.putOption(main.context(), JmlOption.LANG, "openjml");
    	Assert.assertEquals("I", "openjml",JmlOption.value(main.context(), JmlOption.LANG));
        String out = output();
        org.junit.Assert.assertEquals("J", "",out);
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
    	main.addOptions("--quiet");
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
                +"  @Options({\"--progress\",\"--check-feasibility=none\"}) "
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
                +"  @Options({\"--progress\",\"--check-feasibility=none\"}) "
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
    	main.addOptions("--progress","--show-skipped","--method=bassert","--exclude=tt.TestJava.bassert(boolean,boolean)","--check-feasibility=none");
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
                "Skipping proof of tt.TestJava.TestJava() (Skipping tt.TestJava.TestJava because it does not match bassert)" + eol +
                "Skipping proof of tt.TestJava.bassert(boolean,boolean) (Skipping tt.TestJava.bassert because it matches the exclusion tt.TestJava.bassert(boolean,boolean))" + eol + 
                "Starting proof of tt.TestJava.bassert() with prover !!!!" + eol + 
                "Completed proof of tt.TestJava.bassert() with prover !!!! - no warnings" + eol +
                "Skipping proof of tt.TestJava.bassert2(boolean,boolean) (Skipping tt.TestJava.bassert2 because it does not match bassert)" + eol + 
                "Skipping proof of tt.TestJava.bassert3(boolean,boolean) (excluded by skipesc)" + eol + 
                "Completed proving methods in tt.TestJava" + eol 
              ,out) ;

    }
    
    @Test
    public void testNoSkipped() {
    	main.addOptions("-progress","--no-show-skipped","--method=bassert","--exclude=tt.TestJava.bassert(boolean,boolean)","--check-feasibility=none");
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
    	main.addOptions("--progress","--method=bassert","--exclude=tt.TestJava.bassert(boolean,boolean)","--check-feasibility=none");
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
                """
                Proving methods in tt.TestJava
                Skipping proof of tt.TestJava.TestJava() (Skipping tt.TestJava.TestJava because it does not match bassert)
                Skipping proof of tt.TestJava.bassert(boolean,boolean) (Skipping tt.TestJava.bassert because it matches the exclusion tt.TestJava.bassert(boolean,boolean))
                Starting proof of tt.TestJava.bassert() with prover !!!!
                Completed proof of tt.TestJava.bassert() with prover !!!! - no warnings
                Skipping proof of tt.TestJava.bassert2(boolean,boolean) (Skipping tt.TestJava.bassert2 because it does not match bassert)
                Skipping proof of tt.TestJava.bassert3(boolean,boolean) (excluded by skipesc)
                Completed proving methods in tt.TestJava
                """
              ,out) ;

    }
    
    @Test
    public void testBadFeasibility() {
        expectedExit = 2;
        addOptions("--check-feasibility=xyz");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
        ,"error: Unexpected value as argument for --check-feasibility: xyz",-1
        );
        org.junit.Assert.assertTrue(output().isEmpty());
    }
    
    @Test
    public void testQuotedFeasibility() {
        expectedExit = 2;
        addOptions("--check-feasibility","\"xyz\"");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
        ,"error: Unexpected value as argument for --check-feasibility: xyz",-1
        );
        org.junit.Assert.assertTrue(output().isEmpty());
    }
    
    @Test
    public void testBadQuoted() {
        expectedExit = 2;
        addOptions("--check-feasibility","\"xyz");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
        ,"error: Unexpected value as argument for --check-feasibility: \"xyz",-1
        );
        org.junit.Assert.assertTrue(output().isEmpty());
    }
    
    @Test
    public void testBadQuoted2() {
        expectedExit = 2;
        addOptions("--check-feasibility","\"");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
        ,"error: Unexpected value as argument for --check-feasibility: \"",-1
        );
        org.junit.Assert.assertTrue(output().isEmpty());
    }
    
    @Test
    public void testQuotedKey() {
        expectedExit = 0;
        addOptions("\"--check-feasibility\"","none");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertTrue(output().isEmpty());
    }
    
    @Test
    public void nullDefault() {
        expectedExit = 0;
        addOptions("--method=","--check");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertTrue(output().isEmpty());
    }
    
    @Test
    public void testWhitespace() {
        expectedExit = 1;
        addOptions("--check","--require-white-space=false");
        helpTCX("tt.TestJava", "package tt; /*@zzz*/ public class TestJava {}"
                ,"/tt/TestJava.java:1: error: Unexpected or misspelled JML token: zzz",16
        );
        org.junit.Assert.assertTrue(output().isEmpty());
    }
    
    @Test
    public void testWhitespace2() {
        expectedExit = 0;
        addOptions("--check","--require-white-space=true");
        helpTCX("tt.TestJava", "package tt; /*@zzz*/ public class TestJava {}"
        );
        org.junit.Assert.assertTrue(output().isEmpty());
    }
    
    @Test
    public void testDebugFeasibility() {
        expectedExit = 0;
        addOptions("--check-feasibility=debug:100");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertEquals("",output());
    }
    
    @Test
    public void testAllFeasibility() {
        expectedExit = 0;
        addOptions("--check-feasibility=all");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertEquals("",output());
    }
    
    @Test
    public void oldDirs() {
        expectedExit = 0;
        addOptions("-dirs");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Option -dirs is deprecated in favor of --dirs",-1
        );
        org.junit.Assert.assertEquals("",output());
        
    }
    
    @Test
    public void oldDir() {
        expectedExit = 0;
        addOptions("-dir=.");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Option -dir is deprecated in favor of --dir",-1
        );
        org.junit.Assert.assertEquals("",output());
        
    }
    
    @Test
    public void dirs() {
        expectedExit = 0;
        addOptions("--dirs=p,q");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Ignoring p (not a file or folder)",-1
                ,"warning: Ignoring q (not a file or folder)",-1
        );
        org.junit.Assert.assertEquals("",output());
        
    }
    
    @Test
    public void dirsDup() {
        expectedExit = 0;
        addOptions("--dirs=p","--dirs=q");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Ignoring p (not a file or folder)",-1
                ,"warning: Ignoring q (not a file or folder)",-1
        );
        org.junit.Assert.assertEquals("",output());
        
    }
    
    @Test
    public void dirss() {
        expectedExit = 0;
        addOptions("--dirs","p","--","Test.java");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Ignoring p (not a file or folder)",-1
                ,"warning: Ignoring q (not a file or folder)",-1
        );
        org.junit.Assert.assertEquals("",output());
        
    }
    
    @Test
    public void dir() {
        expectedExit = 0;
        addOptions("--dir=p");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Ignoring p (not a file or folder)",-1
        );
        org.junit.Assert.assertEquals("",output());
        
    }
    
    @Test
    public void dirDup() {
        expectedExit = 0;
        addOptions("--dir","p","--dir=q");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Ignoring p (not a file or folder)",-1
                ,"warning: Ignoring q (not a file or folder)",-1
        );
        org.junit.Assert.assertEquals("",output());
        
    }
    
    @Test
    public void dirx() {
        expectedExit = 0;
        addOptions("--dir","p");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Ignoring p (not a file or folder)",-1
        );
        org.junit.Assert.assertEquals("",output());
        
    }
    
    @Test
    public void negDirs() {
        expectedExit = 0;
        addOptions("--no-dirs");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: -no is not permitted on --dirs (ignored)",-1
        );
        org.junit.Assert.assertEquals("",output());
        
    }
    
    @Test
    public void negDir() {
        expectedExit = 0;
        addOptions("--no-dir","p");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: no- is only permitted for boolean options (and --warn)",-1
        );
        org.junit.Assert.assertEquals("",output());
        
    }
    
    @Test
    public void badBool() {
        expectedExit = 0;
        addOptions("--stop-if-parse-errors=yyy");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: This command-line option is not supposed to have a parameter: --stop-if-parse-errors",-1
        );
        org.junit.Assert.assertEquals("",output());
    }
    
    @Test
    public void negDefault() {
        expectedExit = 0;
        addOptions("--no-stop-if-parse-errors=");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: no- is not permitted with set-to-default (empty string after = character)",-1
        );
        org.junit.Assert.assertEquals("",output());
    }
    
    @Test
    public void negWarn() {
        expectedExit = 0;
        addOptions("--no-warn=implicit-everything");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertEquals("",output());
    }
    
    @Test
    public void nullProperties() {
        expectedExit = 0;
        addOptions("--properties",null);
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: --properties requires a non-null, non-empty argument",-1
        );
        org.junit.Assert.assertEquals("",output());
    }
    
    @Test
    public void emptyProperties() {
        expectedExit = 0;
        addOptions("--properties","");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: --properties requires a non-null, non-empty argument",-1
        );
        org.junit.Assert.assertEquals("",output());
    }

    @Test
    public void keysNull() {
        expectedExit = 0;
        addOptions("--keys",null);
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertEquals("",output());
    }

    @Test
    public void keysEmpty() {
        expectedExit = 0;
        addOptions("--keys","");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertEquals("",output());
    }

    @Test
    public void stringDefault() {
        expectedExit = 0;
        addOptions("--check","--show");
        helpTCX("tt.TestJava", "package tt; public "
        );
        org.junit.Assert.assertEquals("",output());
    }

    @Test
    public void helpBadEmpty() {
        expectedExit = 0;
        addOptions("--help=");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: No detailed help available for ''", -1
        );
        org.junit.Assert.assertEquals("",output());
    }

    @Test
    public void helpBad() {
        expectedExit = 0;
        addOptions("--help=zzz");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: No detailed help available for 'zzz'", -1
        );
        org.junit.Assert.assertEquals("",output());
    }

    @Test
    public void helpWarn() {
        expectedExit = 0;
        addOptions("--help=warn");
        helpTCX("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertEquals("Implemented warning keys: [implicit-everything]\n",output());
    }

    // FIXME - these tests abort the unittests -- something is wrong with capturing and testing the stdout/stderr
//    @Test
//    public void checkStdout() {
//        System.out.println("OUT");
//        org.junit.Assert.assertEquals("OUT\n",output());
//    }
//    
////    @Test
//    public void checkStdERR() {
//        System.err.println("ERROR");
//        org.junit.Assert.assertEquals("",output());
//    }
    
    
}

