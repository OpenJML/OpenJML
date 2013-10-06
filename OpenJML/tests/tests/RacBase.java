package tests;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.File;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Strings;

import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;

/** This is a base class for unit test files that exercise the RAC.
 * It inherits from JmlTestCase the diagnostic collector implementation
 * and the (optional) collection of System.out and System.err.  It 
 * implements as well the mechanisms for running RAC via programmatic
 * calls to openjml and then executing the resulting program.
 * 
 * @author David R. Cok
 *
 */
public abstract class RacBase extends JmlTestCase {

    static String testspecpath1 = "$A"+z+"$B";
    static String testspecpath;
    int expectedExit = 0; // Expected result of compiler
    int expectedRACExit = 0; // Expected result of RACed program
    int expectedNotes; // Number of messages to ignore (e.g. uninteresting compiler warnings)
    boolean jdkrac = false; // Set to true to do external system tests of RAC (emulating outside of JUnit)
    boolean continueAnyway = false; // If true, attempt to run the program despite compiler warnings or errors

    /** These are the default command-line arguments for running the RACed
     * program.  The first argument is the java executable; the null argument
     * is replaced by the class name of the class containing the main method.     
     * */
    String[] defrac = new String[]{jdk, "-ea", "-classpath","bin"+z+"bin-runtime"+z+"testdata",null};

    /** These are actual command-line arguments, if they are set differently
     * by a subclass.
     */
    String[] rac; // initialized in subclasses
    

    /** Derived classes can initialize
     * testspecpath1 - the specspath to use
     * <BR>jdkrac - default is false; if true, adjusts the classpath???
     * <BR>rac - the command-line to run the raced program; default is the contents of defrac
     * <BR>
     * After this call, if desired, modify
     * <BR>print - if true, prints out errors as encountered, for test debugging (and disables failing the JUnit test if the error mismatches)
     * <BR>expectedExit - the expected exit code from running openjml
     * <BR>expectedRacExit - the expected exit code from running the RACed program
     * <BR>expectedErrors - the expected number of errors from openjml (typically and by default 0)
     */
    @Override
    public void setUp() throws Exception {
        //System.out.println("Using " + jdk);
        
        // Use the default specs path for tests
        testspecpath = testspecpath1;
        // Define a new collector that filters out the notes
        collector = new FilteredDiagnosticCollector<JavaFileObject>(false);
        super.setUp();
        
        // Setup the options
        main.addOptions("-specspath",   testspecpath);
        main.addOptions("-d", "testdata"); // This is where the output program goes
        main.addOptions("-rac","-racJavaChecks","-racCheckAssumptions");
        if (jdkrac) {
            String sy = Options.instance(context).get(Strings.eclipseProjectLocation);
            if (sy == null) {
                fail("The OpenJML project location should be set using -D" + Strings.eclipseProjectLocation + "=...");
            } else if (!new File(sy).exists()) {
                fail("The OpenJML project location set using -D" + Strings.eclipseProjectLocation + " to " + sy + " does not exist");
            } else {
                main.addOptions("-classpath",sy+"/testdata"+z+sy+"/jdkbin"+z+sy+"/bin");
            }
        }
        main.addOptions("-showNotImplemented");
        main.addOptions("-no-purityCheck"); // System specs have a lot of purity errors, so turn this off for now
        main.addOptions("-no-internalSpecs"); // Faster with this option; should work either way
        main.addOptions("-no-racShowSource");
        specs = JmlSpecs.instance(context);
        expectedExit = 0;
        expectedRACExit = 0;
        expectedNotes = 2; // Two lines to ignore
        print = false;
    }
    
    @Override
    public void tearDown() throws Exception {
        super.tearDown();
        specs = null;
    }

//    public void helpFailure(String failureMessage, String s, Object ... list) {
//        noExtraPrinting = true;
//        boolean failed = false;
//        try {
//            helpTC(s,list);
//        } catch (AssertionFailedError a) {
//            failed = true;
//            assertEquals("Failure report wrong",failureMessage,a.getMessage());
//        }
//        if (!failed) fail("Test Harness failed to report an error");
//    }

//    public void helpTC(String s, Object ... list) {
//        helpTCX(null,s,list);
//    }
//
//    public void helpTCF(String filename,String s, Object ... list) {
//        helpTCX(filename,s,list);
//    }
    
    /** This method does the running of a RAC test.  No output is
     * expected from running openjml to produce the RACed program;
     * the number of expected diagnostics is set by 'expectedErrors'.
     * @param classname The fully-qualified classname for the test class
     * @param s the compilation unit text
     * @param list any expected diagnostics from openjml, followed by the error messages from the RACed program, line by line
     */
    public void helpTCX(String classname, String s, Object... list) {

        String term = "\n|(\r(\n)?)"; // any of the kinds of line terminators
        StreamGobbler out=null,err=null;
        try {
            ListBuffer<JavaFileObject> files = new ListBuffer<JavaFileObject>();
            String filename = classname.replace(".","/")+".java";
            JavaFileObject f = new TestJavaFileObject(filename,s);
            files.append(f);
            for (JavaFileObject ff: mockFiles) {
                if (ff.toString().endsWith(".java")) files.append(ff);
            }

            Log.instance(context).useSource(files.first());
            int ex = main.compile(new String[]{}, null, context, files.toList(), null);
            
            if (print) printDiagnostics();
            int observedMessages = collector.getDiagnostics().size() - expectedNotes;
            if (observedMessages < 0) observedMessages = 0;

            for (int i=0; i<observedMessages; i++) {
                int k = 2*i + 2*expectedNotes;
                if (k >= list.length) {
                    if (!print) printDiagnostics();
                    fail("More diagnostics than expected");
                }
                assertEquals("Message " + i, list[k].toString(), noSource(collector.getDiagnostics().get(i)));
                assertEquals("Message " + i, ((Integer)list[k+1]).intValue(), collector.getDiagnostics().get(i).getColumnNumber());
            }
            if (ex != expectedExit) fail("Compile ended with exit code " + ex);
            if (ex != 0 && !continueAnyway) return;
            
            if (rac == null) rac = defrac;
            rac[rac.length-1] = classname;
            Process p = Runtime.getRuntime().exec(rac);
            
            out = new StreamGobbler(p.getInputStream());
            err = new StreamGobbler(p.getErrorStream());
            out.start();
            err.start();
            if (timeout(p,10000)) { // 10 second timeout
                fail("Process did not complete within the timeout period");
            }
            
            int i = observedMessages*2;
            if (print) {
                String data = out.input();
                if (data.length() > 0) {
                    String[] lines = data.split(term);
                    for (String line: lines) {
                        System.out.println("OUT: " + line);
                    }
                }
                data = err.input();
                if (data.length() > 0) {
                    String[] lines = data.split(term);
                    for (String line: lines) {
                        System.out.println("ERR: " + line);
                    }
                }
            }
            String data = out.input();
            if (data.length() > 0) {
                String[] lines = data.split(term);
                for (String line: lines) {
                    if (i < list.length) assertEquals("Output line " + i, list[i], line);
                    i++;
                }
            }
            data = err.input();
            if (data.length() > 0) {
                String[] lines = data.split(term);
                for (String line: lines) {
                    if (i < list.length) assertEquals("Output line " + i, list[i], line);
                    i++;
                }
            }

            if (i != list.length && !print) { // if print, then we already printed
                printDiagnostics();
            }
            if (i> list.length) fail("More output than specified: " + i + " vs. " + list.length + " lines");
            if (i< list.length) fail("Less output than specified: " + i + " vs. " + list.length + " lines");
            if (p.exitValue() != expectedRACExit) fail("Exit code was " + p.exitValue());
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            if (!print) printDiagnostics();
            if (!print && !noExtraPrinting) {
                if (out != null) {
                    String[] lines = out.input().split(term);
                    for (String line: lines) {
                        System.out.println("OUT: " + line);
                    }
                }
                if (err != null) {
                    String[] lines = err.input().split(term);
                    for (String line: lines) {
                        System.out.println("ERR: " + line);
                    }
                }
            }
            throw e;
        } finally {
//            if (r != null) 
//                try { r.close(); } 
//                catch (java.io.IOException e) { 
//                    // Give up if there is an exception
//                }
//            if (rerr != null) 
//                try { rerr.close(); } 
//                catch (java.io.IOException e) {
//                    // Give up if there is an exception
//                }
        }
    }


}
