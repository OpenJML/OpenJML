package tests;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.net.URI;

import javax.tools.JavaFileObject;

import junit.framework.AssertionFailedError;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Utils;

import tests.JmlTestCase.FilteredDiagnosticCollector;

import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;

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
    int expectedExit = 0;
    int expectedRACExit = 0;
    int expectedErrors = 0;
    boolean jdkrac = false;

    /** The java executable */
    // TODO: This is going to use the external setting for java, rather than
    // the current environment within Eclipse
    String jdk = System.getProperty("java.home") + "/bin/java";

    /** These are the default command-line arguments for running the RACed
     * program.  The first argument is the java executable; the null argument
     * is replaced by the class name of the class containing the main method.     
     * */
    String[] defrac = new String[]{jdk, "-classpath","bin"+z+"testdata",null};

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
    protected void setUp() throws Exception {
        //System.out.println("Using " + jdk);
        
        // Use the default specs path for tests
        testspecpath = testspecpath1;
        // Define a new collector that filters out the notes
        collector = new FilteredDiagnosticCollector<JavaFileObject>(true);
        super.setUp();
        
        // Setup the options
        options.put("-specspath",   testspecpath);
        options.put("-d", "testdata"); // This is where the output program goes
        options.put("-rac",   "");
        if (jdkrac) {
            String sy = System.getProperty(Utils.eclipseProjectLocation);
            if (sy == null) {
                fail("The OpenJML project location should be set using -D" + Utils.eclipseProjectLocation + "=...");
            } else if (!new File(sy).exists()) {
                fail("The OpenJML project location set using -D" + Utils.eclipseProjectLocation + " to " + sy + " does not exist");
            } else {
                options.put("-classpath",sy+"/testdata"+z+sy+"/jdkbin"+z+sy+"/bin");
            }
        }
        specs = JmlSpecs.instance(context);
        Log.instance(context).multipleErrors = true;
        expectedExit = 0;
        expectedRACExit = 0;
        expectedErrors = 0;
        print = false;
    }
    
    protected void tearDown() throws Exception {
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
        helpTCX(new String[]{classname},s,list);
    }
    public void helpTCX(String[] classnames, String s, Object... list) {
        BufferedReader r = null;
        BufferedReader rerr = null;
        try {
            ListBuffer<JavaFileObject> files = new ListBuffer<JavaFileObject>();
            for (String classname: classnames) {
                String filename = classname.replace(".","/")+".java";
                JavaFileObject f = new TestJavaFileObject(filename,s);
                files.append(f);
            }
            Log.instance(context).useSource(files.first());
            int ex = main.compile(new String[]{}, context, files.toList(), null);
            
            if (print || collector.getDiagnostics().size()!=expectedErrors) printErrors();
            assertEquals("Errors seen",expectedErrors,collector.getDiagnostics().size());
            for (int i=0; i<expectedErrors; i++) {
                assertEquals("Error " + i, list[2*i].toString(), noSource(collector.getDiagnostics().get(i)));
                assertEquals("Error " + i, ((Integer)list[2*i+1]).intValue(), collector.getDiagnostics().get(i).getColumnNumber());
            }
            if (ex != expectedExit) fail("Compile ended with exit code " + ex);
            if (ex != 0) return;
            
            if (rac == null) rac = defrac;
            rac[rac.length-1] = classnames[0];
            Process p = Runtime.getRuntime().exec(rac);
            // Give the process some time to get started and generate output
            Thread.sleep(100);  // If we use p.waitFor() we sometimes get a process that locks up - esp. if it has errors
            r = new BufferedReader(new InputStreamReader(p.getInputStream()));
            rerr = new BufferedReader(new InputStreamReader(p.getErrorStream()));
            int i = expectedErrors*2;
            boolean done = false;
            boolean edone = false;
            while (!done || !edone) {
                // DO we read the output or the error?  Every test is supposed to
                // generate output if it is successful.  If it fails to run (which
                // it should not), only error output may be generated.  We hope that
                // rerr is ready at this point (hence the delay above) if there is
                // only error output, otherwise we block on the readLine call.
                // (we did not used to have this problem??) (TODO: adjust to using java.nio?)
                while (!done && !rerr.ready()) {
                    String ss = r.readLine();
                    if (ss == null) { done = true; break; }
                    if (print || i >= list.length) { System.out.println("OUT: " + ss); }
                    if (!print && i < list.length) assertEquals("Output line " + i, list[i], ss);
                    i++;
                }

                while (!edone && !r.ready()) {
                    String ss = rerr.readLine();
                    if (ss == null) { edone = true; break; }
                    if (print || i >= list.length) { System.out.println("ERR: " + ss); }
                    if (!print && i < list.length) assertEquals("Output line " + i, list[i], ss);
                    i++;
                }
            }
            if (i> list.length) fail("More output than specified: " + i + " vs. " + list.length + " lines");
            if (i< list.length) fail("Less output than specified: " + i + " vs. " + list.length + " lines");
            if (p.exitValue() != expectedRACExit) fail("Exit code was " + p.exitValue());
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionFailedError e) {
            if (!print && !noExtraPrinting) printErrors();
            throw e;
        } finally {
            if (r != null) 
                try { r.close(); } 
                catch (java.io.IOException e) { 
                    // Give up if there is an exception
                }
            if (rerr != null) 
                try { rerr.close(); } 
                catch (java.io.IOException e) {
                    // Give up if there is an exception
                }
        }
    }


}
