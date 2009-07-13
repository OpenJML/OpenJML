package tests;

/** These tests check the RAC functionality of outputting a stack trace along with
 * notification of failed RAC assertions.  These test that library class files 
 * recompiled with RAC actually get used and produce errors.  Hence the need to 
 * put the new system classes (in jdkbin) in the bootclasspath ahead of the regular
 * java classes.
 */
public class racsystem extends RacBase {

    /** THe command-line to use to run RACed programs - note the inclusion of the
     * RAC-compiled JDK library classes ahead of the regular Java libaray classes
     * in the boot class path. (This may not work on all platforms)
     */
    // The bootclasspath here consists of the JDK library files (RAC-compiled) plus
    // utilities that they depend on - the content of jmlruntime.jar.
    String[] sysrac = new String[]{jdk, "-Xbootclasspath/p:jdkbin"+z+"bin-runtime", "-classpath","bin"+z+"bin-runtime"+z+"testdata",null};

    protected void setUp() throws Exception {
        rac = sysrac;
        jdkrac = true;
        //noCollectDiagnostics = true;
        super.setUp();
        options.put("-noPurityCheck",""); // To shut off complaints about misuse of purity in Java specifications
        //options.put("-jmldebug",   "");
        //options.put("-jmlverbose",   "");
        //options.put("-noInternalSpecs",   "");
        //options.put("-useExceptions",   "");
        //print = true;
    }

    /** Testing with getting a stack trace */
    public void testFile2() {
        expectedRACExit = 1; 
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.useExceptions = true; \n"
                +"try { m(); } catch (Exception e) { e.printStackTrace(System.out); } \n"
                +"System.out.println(\"END\"); }"
                +"static void m() {\n"
                +"  int i = (new java.io.File(\"A\")).compareTo((java.io.File)null);\n"
                +"}"
                +"}"
                
                ,"Exception in thread \"main\" org.jmlspecs.utils.Utils$JmlAssertionError: File.refines-spec:77: JML precondition is false"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailure(Utils.java:38)"
                ,"\tat java.io.File.compareTo(File.java:1)"
                ,"\tat tt.TestJava.m(TestJava.java:5)"
                ,"\tat tt.TestJava.main(TestJava.java:3)"
                );
    }

    /** Testing with getting a stack trace - Exception does not catch it */
    public void testFile2a() {
        expectedRACExit = 1;
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.useExceptions = true; \n"
                +"try { m(); } catch (Exception e) { e.printStackTrace(System.out); } \n"
                +"System.out.println(\"END\"); }"
                +"static void m() {\n"
                +"  int i = (new java.io.File(\"A\")).compareTo((java.io.File)null);\n"
                +"}"
                +"}"
                
                ,"Exception in thread \"main\" org.jmlspecs.utils.Utils$JmlAssertionError: File.refines-spec:77: JML precondition is false"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailure(Utils.java:38)"
                ,"\tat java.io.File.compareTo(File.java:1)"
                ,"\tat tt.TestJava.m(TestJava.java:5)"
                ,"\tat tt.TestJava.main(TestJava.java:3)"
                );
    }

    /** Testing with getting a stack trace - Error does catch it */
    public void testFile2c() {
        expectedRACExit = 0;
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.useExceptions = true; \n"
                +"try { m(); } catch (Error e) { e.printStackTrace(System.out); } \n"
                +"System.out.println(\"END\"); }"
                +"static void m() {\n"
                +"  int i = (new java.io.File(\"A\")).compareTo((java.io.File)null);\n"
                +"}"
                +"}"
                
                ,"org.jmlspecs.utils.Utils$JmlAssertionError: File.refines-spec:77: JML precondition is false"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailure(Utils.java:38)"
                ,"\tat java.io.File.compareTo(File.java:1)"
                ,"\tat tt.TestJava.m(TestJava.java:5)"
                ,"\tat tt.TestJava.main(TestJava.java:3)"
                ,"END"
                );
    }
    

    /** Testing with getting a stack trace using showStack */
    public void testFile2d() {
        expectedRACExit = 0;
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.showStack = true; \n"
                +"m();\n"
                +"System.out.println(\"END\"); }\n"
                +"static void m() {\n"
                +"  //@ assert false;\n"
                +"}"
                +"}"
                
                ,"/tt/TestJava.java:6: JML assertion is false"
                ,"org.jmlspecs.utils.Utils$JmlAssertionError: /tt/TestJava.java:6: JML assertion is false"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailure(Utils.java:40)"
                ,"\tat tt.TestJava.m(TestJava.java:6)"
                ,"\tat tt.TestJava.main(TestJava.java:3)"
                ,"END"
                );
    }
    
    public void testFile3() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"try { m(); } catch (Exception e) {  } \n"
                +"System.out.println(\"END\"); }"
                +"static void m() {\n"
                +"  int i = (new java.io.File(\"A\")).compareTo((java.io.File)null);\n"
                +"}"
                +"}"
                ,"File.refines-spec:77: JML precondition is false"
                ,"File.refines-spec:115: JML unexpected exception"
                ,"END"
                );
    }
    
    public void testFile() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.showStack = true; \n"
                +"try { m(); } catch (Exception e) {  } \n"
                +"System.out.println(\"END\"); }"
                +"static void m() throws Exception {\n"
                +"  int i = (new java.io.File(\"A\")).compareTo((java.io.File)null);\n"
                +"}"
                +"}"
                ,"File.refines-spec:77: JML precondition is false"
                ,"org.jmlspecs.utils.Utils$JmlAssertionError: File.refines-spec:77: JML precondition is false"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailure(Utils.java:40)"
                ,"\tat java.io.File.compareTo(File.java:1)"
                ,"\tat tt.TestJava.m(TestJava.java:5)"
                ,"\tat tt.TestJava.main(TestJava.java:3)"
                ,"File.refines-spec:115: JML unexpected exception"
                ,"org.jmlspecs.utils.Utils$JmlAssertionError: File.refines-spec:115: JML unexpected exception"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailure(Utils.java:40)"
                ,"\tat java.io.File.compareTo(File.java:1)"
                ,"\tat tt.TestJava.m(TestJava.java:5)"
                ,"\tat tt.TestJava.main(TestJava.java:3)"
                ,"END"
                );
    }

    /** Not sure what this is supposed to test (TODO) */
    public void testHashCode() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.showStack = true; \n"
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
    public void testMain() {
        helpTCX("tt.TestJava","package tt; public class TestJava { \n"
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
     * routine with String... did not work.  Here we use String[] which
     * did work.
     */
    public void testMain2() {
        options.put("-noInternalSpecs","");
        helpTCX("tt.TestJava","package tt; public class TestJava { \n"
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
