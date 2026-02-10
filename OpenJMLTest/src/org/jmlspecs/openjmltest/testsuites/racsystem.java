package org.jmlspecs.openjmltest.testsuites;

import java.util.ArrayList;
import java.util.Collection;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

// These tests are run for both new and custom translations.

/** These tests check the RAC functionality of outputting a stack trace along with
 * notification of failed RAC assertions.  These test that library class files 
 * recompiled with RAC actually get used and produce errors.  Hence the need to 
 * put the new system classes (in jdkbin) in the bootclasspath ahead of the regular
 * java classes.
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racsystem extends RacBase {
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        addOptions("--rac-show-source=line");
    }
    
    @Override
    public void tearDown() throws Exception {
        System.clearProperty("org.jmlspecs.openjml.racexitcode");
    }

    /** Testing with getting a stack trace */
    @Test // FIXME - should this say what exception violated the signals clause
    public void testFile2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static void main(String[] args) {
                        org.jmlspecs.runtime.Utils.useExceptions = true;
                        try { m(); } catch (Throwable e) { System.out.println("Catching an AssertionError: " + e.getClass() + " " + e.getMessage()); }
                        System.out.println("END");
                        org.jmlspecs.runtime.Utils.useExceptions = false;
                    }
                    static void m() {
                        int i = (new java.io.File("A")).compareTo((java.io.File)null);
                    }
                }
                """
                ,"Catching an AssertionError: class org.jmlspecs.runtime.JmlAssertionError /tt/TestJava.java:10: verify: JML signals condition is false"
                ,"$SPECS/java/io/File.jml:100: verify: Associated declaration: /tt/TestJava.java:10:"
                ,"END"
                );
    }
   
    /** Testing with getting a stack trace - Exception does not catch it */
    @Test
    public void testFile2a() {
        expectedRACExit = 1;
        addOptions("--rac-show-source=none"); // FIXME fix comparisons so these all can be "line"
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static void main(String[] args) {
                        org.jmlspecs.runtime.Utils.useExceptions = true;
                        try {
                            m();
                        } catch (Exception e) {
                            System.out.println("CAUGHT ASSERTION");
                            e.printStackTrace(System.out);
                        }
                        System.out.println("END");
                    }
                    /*@ signals (Exception e) false;*/
                    static void m() {
                        int i = (new java.io.File("A")).compareTo((java.io.File)null);
                    }
                }
                """
                
                ,"Exception in thread \"main\" org.jmlspecs.runtime.JmlAssertionError: verify: JML signals condition is false"
                ,"Associated declaration: /tt/TestJava.java:14:"
                ,"\tat java.base/org.jmlspecs.runtime.Utils.createException"+locA
                ,"\tat java.base/org.jmlspecs.runtime.Utils.assertionFailureL"+locB
                ,"\tat tt.TestJava.m(TestJava.java:14)"
                ,"\tat tt.TestJava.main(TestJava.java:6)"       
                );
    }

    /** Testing with getting a stack trace - Exception does not catch it */
    @Test
    public void testFile2pre() {
        expectedRACExit = 1;
        addOptions("--rac-show-source=none");
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static void main(String[] args) {
                        org.jmlspecs.runtime.Utils.useExceptions = true;
                        try {
                            m();
                        } catch (Exception e) {
                            System.out.println("CAUGHT ASSERTION");
                            e.printStackTrace(System.out);
                        } finally {
                            org.jmlspecs.runtime.Utils.useExceptions = false;
                        }
                        System.out.println("END");
                        org.jmlspecs.runtime.Utils.useExceptions = false;
                    }
                    /*@ requires false;*/
                    static public void m() {
                        int i = (new java.io.File("A")).compareTo((java.io.File)null);
                    }
                }
                """
                ,"Exception in thread \"main\" org.jmlspecs.runtime.JmlAssertionError$Precondition: verify: JML precondition is false"
                ,"verify: Associated declaration: /tt/TestJava.java:6:"
                ,"\tat java.base/org.jmlspecs.runtime.Utils.createException"+locD
                ,"\tat java.base/org.jmlspecs.runtime.Utils.assertionFailureL"+locB
                ,"\tat tt.TestJava.main(TestJava.java:6)"
                );
    }

    /** Testing with getting a stack trace - Error does catch it */
    @Test
    public void testFile2c() {
        addOptions("--rac-show-source=none");
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static void main(String[] args) {
                        org.jmlspecs.runtime.Utils.useExceptions = true;
                        try {
                            m();
                        } catch (Error e) {
                            System.out.println("CAUGHT ASSERTION");
                            e.printStackTrace(System.out);
                        }
                        System.out.println("END");
                    }
                    /*@ signals (Exception e) false;*/
                    static void m() {
                      var f = (new java.io.File("A"));
                      int i = f.compareTo((java.io.File)null);  // Line 16
                    }
                }
                """
                ,"CAUGHT ASSERTION"
                ,"org.jmlspecs.runtime.JmlAssertionError: verify: JML signals condition is false"
                ,"verify: Associated declaration: /tt/TestJava.java:14:"
                ,"\tat java.base/org.jmlspecs.runtime.Utils.createException"+locA
                ,"\tat java.base/org.jmlspecs.runtime.Utils.assertionFailureL"+locB
                ,"\tat tt.TestJava.m(TestJava.java:14)"
                ,"\tat tt.TestJava.main(TestJava.java:6)"
                ,"END"
                );
    }
    

    /** Testing with getting a stack trace using showStack */
    @Test
    public void testFile2d() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static void main(String[] args) {
                        org.jmlspecs.runtime.Utils.showStack = true;
                        m();
                        System.out.println(\"END\");
                    }
                    static void m() {
                        //@ assert false;
                    }
                }
                """
                ,"org.jmlspecs.runtime.JmlAssertionError: /tt/TestJava.java:9: verify: JML assertion is false"
                ,"\tat java.base/org.jmlspecs.runtime.Utils.createException"+locA
                ,"\tat java.base/org.jmlspecs.runtime.Utils.assertionFailureL"+locC
                ,"\tat tt.TestJava.m(TestJava.java:9)"
                ,"\tat tt.TestJava.main(TestJava.java:5)"
                ,"END"
                );
    }
    
    /** Testing with an exit code */
    @Test
    public void testFile2e() {
        expectedRACExit = 5;
        addOptions("--rac-show-source=line");
        rac = new String[]{jdk, "-Dorg.jmlspecs.openjml.racexitcode=5", "-esa", "-classpath", null, "tt.TestJava"};
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static void main(String[] args) {
                        m();
                        System.out.println(\"END\");
                    }
                    static void m() {
                        //@ assert false;
                    }
                }
                """
                ,"/tt/TestJava.java:8: verify: JML assertion is false"
                ,"END"
                ,"1 verification error"
                );
    }
    
    @Test
    public void testFile3() {
        addOptions("--rac-show-source=none");
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static void main(String[] args) {
                        try {
                            m();
                        } catch (Exception e) {
                            System.out.println(\"CAUGHT EXCEPTION\");
                        }
                        System.out.println(\"END\");
                    }
                    //@ signals_only Exception;
                    static void m() {
                        var k = (new java.io.File((String)null)); // Precondition NOT OK
                    }
                }
                """
                ,"verify: JML actual argument may not be null: arg0 in File(java.lang.String)"
                ,"verify: Associated declaration: /tt/TestJava.java:13:"
                ,"verify: JML precondition is false"
                ,"verify: Associated declaration: /tt/TestJava.java:13:"
                ,"CAUGHT EXCEPTION"
                ,"END"
                );
    }
    
    @Test
    public void testHashCode() {
        helpRacText("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.runtime.Utils.showStack = true; \n"
                +"int i = ( new Object().hashCode()); \n"
                +"int j = ( new Object().hashCode()); \n"
                +" System.out.println(i==j);"
                +"System.out.println(\"END\"); }"
                +"}"
                ,"false"
                ,"END"
                );
    }
    
    /** This tests a bug in which matching with no specs file to a main
     * routine with String... did not work.  Here we use String[] which
     * did work.
     */
    @Test
    public void testMain() {
        addOptions("--rac-show-source=line");
        helpRacText("tt.TestJava","package tt; public class TestJava { \n"
                +"public static void main(String[] args) { \n"
                +"  System.out.println(\"START\"); \n"
                +"  //@ assert args.length != 0;\n"
                +"  System.out.println(\"END\"); }"
                +"}"
                ,"START"
                ,"/tt/TestJava.java:4: JML assertion is false"
                ,"END"
                );
    }
    
    /** This tests a bug in which matching with no specs file to a main
     * routine with String... did not work.  
     */
    @Test
    public void testMain2() {
        addOptions("--rac-show-source=line");
        helpRacText("tt.TestJava","package tt; public class TestJava { \n"
                +"public static void main(String... args) { \n"
                +"  System.out.println(\"START\"); \n"
                +"  //@ assert args.length != 0;\n"
                +"  System.out.println(\"END\"); }"
                +"}"
                ,"START"
                ,"/tt/TestJava.java:4: JML assertion is false"
                ,"END"
                );
    }
}
