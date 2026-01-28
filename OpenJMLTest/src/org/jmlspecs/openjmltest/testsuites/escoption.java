package org.jmlspecs.openjmltest.testsuites;

import java.util.Collection;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlOptions;
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
        captureOutput = true;
        checkOutput = false;
        super.setUp();
        addOptions("--nullable-by-default"); // Because the tests were written this way
        addOptions("--normal");
        addOptions("--check-feasibility=none","--no-require-white-space");
    }
 
    @Test
    public void testOptionValueBoolean() {
        collectSystemOutput(false);
        JmlOptions options = JmlOptions.instance(main.context());
        Assert.assertEquals("A", "openjml",JmlOption.LANG.value(context));
        Assert.assertEquals("B", "openjml",JmlOption.LANG.value(context));
        Assert.assertEquals("C", "openjml",options.get("--lang"));
        Assert.assertEquals("D", "openjml",options.get("--lang"));
        options.put(JmlOption.LANG, "jml");
        Assert.assertEquals("E", "jml",JmlOption.LANG.value(context));
        options.put(JmlOption.LANG, "openjml");
        Assert.assertEquals("F", "openjml",JmlOption.LANG.value(context));
        main.addOptions("--lang=jml");
        Assert.assertEquals("G", "jml",JmlOption.LANG.value(context));
        main.addOptions("--lang=openjml");
        Assert.assertEquals("H", "openjml",JmlOption.LANG.value(context));
        options.put(JmlOption.LANG, "openjml");
        Assert.assertEquals("I", "openjml",JmlOption.LANG.value(context));
        String out = output();
        org.junit.Assert.assertEquals("J", "",out);
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }

    // FIXME -- adjust JmlOption calls
    @Test
    public void testOptionValue() {
        collectSystemOutput(false);
        JmlOptions options = JmlOptions.instance(context);
        Assert.assertEquals(null, JmlOption.METHOD.value(main.context()));
        Assert.assertEquals(null, options.get("-method"));
        options.put(JmlOption.METHOD, "xxx");
        Assert.assertEquals("xxx",options.value(JmlOption.METHOD));
        options.put(JmlOption.METHOD, null);
        Assert.assertEquals(null, JmlOption.METHOD.value(main.context()));
        options.put(JmlOption.METHOD, "");
        Assert.assertEquals("", options.value(JmlOption.METHOD));
        String out = output();
        org.junit.Assert.assertEquals("",out);
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }

    @Test
    public void testOption() {
        addOptions("--normal");
        helpEsc("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
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
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method bassert",75
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method bassert2",76
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method bassert3",77
        );
        String out = output();
        org.junit.Assert.assertEquals(
              "Starting proof of tt.TestJava.bassert2(boolean,boolean) with prover !!!!" + eol + 
              "Completed proof of tt.TestJava.bassert2(boolean,boolean) with prover !!!! - with warnings" + eol
              ,out) ;
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void testOption2() {
        helpEsc("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"  @Options({\"--progress\",\"--check-feasibility=none\"}) "
                +"public class TestJava { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert(boolean bb, boolean b) { /*@ assume b; */ /*@assert false;*/   }\n" // Should fail because of the explicit assert false
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  @Options(\"--normal\") \n"
                +"  public static void bassert2(boolean bb, boolean b) { /*@ assume b; */ /*@assert !bb;*/   }\n" // Should fail because of the tautologically false assert
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert3(boolean bb, boolean b) { /*@ assume bb; */ /*@assert b;*/   }\n" // Should fail because of the unprovable assert
                +"}"
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method bassert",75
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method bassert2",76
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method bassert3",77
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
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void testOption3() {
        helpEsc("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"  @Options({\"--progress\",\"--check-feasibility=none\"}) "
                +"public class TestJava { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert(boolean bb, boolean b) { /*@ assume b; */ /*@ assert false;*/   }\n" // Should fail because of the explicit assert false
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  @Options(\"--normal\") \n"
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
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method bassert",76
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method bassert2",77
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method bassert3",78
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assert) in method bassert",76
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
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void testSkipped() {
    	main.addOptions("--progress","--show-skipped","--method=bassert","--exclude=tt.TestJava.bassert(boolean,boolean)","--check-feasibility=none");
        helpEsc("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
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
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void testNoSkipped() {
    	main.addOptions("-progress","--no-show-skipped","--method=bassert","--exclude=tt.TestJava.bassert(boolean,boolean)","--check-feasibility=none");
        helpEsc("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
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
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void testSkippedDefault() {
    	main.addOptions("--progress","--method=bassert","--exclude=tt.TestJava.bassert(boolean,boolean)","--check-feasibility=none");
        helpEsc("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
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
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void testBadFeasibility() {
        expectedExit = 2;
        addOptions("--check-feasibility=xyz");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
        ,"error: Unexpected value as argument for --check-feasibility: xyz",-1
        );
        org.junit.Assert.assertTrue(output().isEmpty());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void testQuotedFeasibility() {
        expectedExit = 2;
        addOptions("--check-feasibility","\"xyz\"");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
        ,"error: Unexpected value as argument for --check-feasibility: xyz",-1
        );
        org.junit.Assert.assertTrue(output().isEmpty());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void testBadQuoted() {
        expectedExit = 2;
        addOptions("--check-feasibility","\"xyz");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
        ,"error: Unexpected value as argument for --check-feasibility: \"xyz",-1
        );
        org.junit.Assert.assertTrue(output().isEmpty());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void testBadQuoted2() {
        expectedExit = 2;
        addOptions("--check-feasibility","\"");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
        ,"error: Unexpected value as argument for --check-feasibility: \"",-1
        );
        org.junit.Assert.assertTrue(output().isEmpty());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void testQuotedKey() {
        expectedExit = 0;
        addOptions("\"--check-feasibility\"","none");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertTrue(output().isEmpty());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void nullDefault() {
        expectedExit = 0;
        addOptions("--method=","--check");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertTrue(output().isEmpty());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void testWhitespace() {
        expectedExit = 1;
        addOptions("--check","--require-white-space=false");
        helpEsc("tt.TestJava", "package tt; /*@zzz*/ public class TestJava {}"
                ,"/tt/TestJava.java:1: error: Unexpected or misspelled JML token: zzz",16
        );
        org.junit.Assert.assertTrue(output().isEmpty());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void testWhitespace2() {
        expectedExit = 0;
        addOptions("--check","--require-white-space=true");
        helpEsc("tt.TestJava", "package tt; /*@zzz*/ public class TestJava {}"
        );
        org.junit.Assert.assertTrue(output().isEmpty());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
   }
    
    @Test
    public void testDebugFeasibility() {
        expectedExit = 0;
        addOptions("--check-feasibility=debug:100");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertEquals(
                """
                Proving methods in tt.TestJava
                Starting proof of tt.TestJava.TestJava() with prover !!!!
                Completed proof of tt.TestJava.TestJava() with prover !!!! - no warnings
                Completed proving methods in tt.TestJava
                """
                ,output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void testAllFeasibility() {
        expectedExit = 0;
        addOptions("--check-feasibility=all");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertEquals("", output());
        org.junit.Assert.assertEquals("", errorOutput());
    }
    
    @Test
    public void oldDirs() {
        expectedExit = 0;
        addOptions("-dirs");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Option -dirs is deprecated in favor of --dirs",-1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void oldDir() {
        expectedExit = 0;
        addOptions("-dir=.");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Option -dir is deprecated in favor of --dir",-1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void dirs() {
        expectedExit = 0;
        addOptions("--dirs=p,q");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Ignoring p (not a file or folder)",-1
                ,"warning: Ignoring q (not a file or folder)",-1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void dirsDup() {
        expectedExit = 0;
        addOptions("--dirs=p","--dirs=q");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Ignoring p (not a file or folder)",-1
                ,"warning: Ignoring q (not a file or folder)",-1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void dirss() {
        expectedExit = 0;
        addOptions("--dirs","p","--","Test.java");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Ignoring p (not a file or folder)",-1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void dir() {
        expectedExit = 0;
        addOptions("--dir=p");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Ignoring p (not a file or folder)",-1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void dirDup() {
        expectedExit = 0;
        addOptions("--dir","p","--dir=q");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Ignoring p (not a file or folder)",-1
                ,"warning: Ignoring q (not a file or folder)",-1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void dirx() {
        expectedExit = 0;
        addOptions("--dir","p");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: Ignoring p (not a file or folder)",-1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void negDirs() {
        expectedExit = 0;
        addOptions("--no-dirs");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: -no is not permitted on --dirs (ignored)",-1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void negDir() {
        expectedExit = 0;
        addOptions("--no-dir","p");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: no- is only permitted for boolean options (and --warn)",-1
                ,"warning: Ignoring p (not a file or folder)",-1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void badBool() {
        expectedExit = 0;
        addOptions("--show-summary=yyy");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: This command-line option is not supposed to have a parameter: --show-summary",-1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void okBool() {
        expectedExit = 0;
        addOptions("--show-summary=false","--check");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void negDefault() {
        expectedExit = 0;
        addOptions("--no-show-summary=");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: no- is not permitted with set-to-default (empty string after = character)",-1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void negWarn() {
        expectedExit = 0;
        addOptions("--no-warn=implicit-everything");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void nullProperties() {
        expectedExit = 0;
        addOptions("--properties",null);
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: --properties requires a non-null, non-empty argument",-1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    @Test
    public void emptyProperties() {
        expectedExit = 0;
        addOptions("--properties","");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: --properties requires a non-null, non-empty argument",-1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
   }

    @Test
    public void keysNull() {
        expectedExit = 0;
        addOptions("--keys",null);
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
   }

    @Test
    public void keysEmpty() {
        expectedExit = 0;
        addOptions("--keys","");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }

    @Test
    public void stringDefault() {
        expectedExit = 0;
        addOptions("--check","--show");
        helpEsc("tt.TestJava", "package tt; public "
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }

    @Test
    public void helpBadEmpty() {
        expectedExit = 0;
        addOptions("--help=");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: No detailed help available for ''", -1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }

    @Test
    public void helpBad() {
        expectedExit = 0;
        addOptions("--help=zzz");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"warning: No detailed help available for 'zzz'", -1
        );
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }

    @Test
    public void helpWarn() {
        expectedExit = 0;
        addOptions("--help=warn");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertEquals("Help: --help=warn   Subcommands: none all list reset\nImplemented warning keys: [implicit-everything, literal-divide-by-zero, missing-measured-by, missing-semicolon, missing-specs, missing-specs-path]\n",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }

    @Test
    public void helpInfer() {
        expectedExit = 0;
        addOptions("--help=infer");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
        );
        org.junit.Assert.assertEquals("Help: --help=infer   Subcommands: none all list reset show\nImplemented specification inference keys: [loop-assigns]\n",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }

    /** Simple test of output capturing */
    @Test
    public void checkStdout() {
        this.out.println("OUT");
        org.junit.Assert.assertEquals("OUT\n",output());
        org.junit.Assert.assertTrue(errorOutput().isEmpty());
    }
    
    /** Simple test of error output capturing */
    @Test
    public void checkStderr() {
        System.err.println("ERROR");
        org.junit.Assert.assertEquals("",output());
        org.junit.Assert.assertEquals("ERROR\n",errorOutput());
    }
}

