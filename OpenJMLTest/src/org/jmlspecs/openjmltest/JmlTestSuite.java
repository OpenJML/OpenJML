package org.jmlspecs.openjmltest;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.net.URI;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticListener;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjmltest.OutputCompare.AnyOrder;
import org.jmlspecs.openjmltest.OutputCompare.OneOf;
import org.jmlspecs.openjmltest.OutputCompare.Optional;
import org.jmlspecs.openjmltest.OutputCompare.Seq;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.rules.TestName;
import org.openjml.MockJavaFileObject;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Position;


/** This class provides basic functionality for the JUnit tests for OpenJML.
 * It is expected that actual JUnit test suites will derive from this class.
 * <P>
 * It is also expected that the unit tests have 'OpenJMLTest' as the working directory (at least initially)
 * <P>
 * It creates a DiagnosticListener that collects all of the error and warning
 * messages from executing the test.  This class does not capture other messages
 * (e.g. straight to std out), but some subclasses do.  The captured error and 
 * warning messages are compared against test supplied text - for both the text
 * of the message, which includes file name and line number - and the column 
 * number.
 * 
 * @author David Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public abstract class JmlTestSuite {

    // By default the output from a test case goes to System.out
    // But where the output is captured and checked as part of the test case,
    // these fields should be temporarily set to some stream that is unique to the test case
    // or at least to the thread running it.
    public java.io.PrintStream out = System.out;
    public java.io.PrintStream err = System.err;

    /** A purposefully short abbreviation for the system path separator
     * ( ; or : )
     */
    public static final String z = java.io.File.pathSeparator;
    
    /** The relative path from OpenJMLTest to the OpenJMLDemo repo */
    public static final String OpenJMLDemoPath = "../../OpenJMLDemo";

    // The test output expects that the current working directory while running unittests is  .../OpenJML/OpenJMLTest

    // In a 'standard' local OpenJML github working environment, root will be the container for
    // OpenJML/OpenJML21, OpenJML/OpenJMLTest, Specs, etc.
    // This value is needed because some tests emit a full absolute path name in error messages
    // The code to set this value presumes the initial working directory of the test runner is 'OpenJMLTest'
    static final public String root = new File(".").getAbsoluteFile().getParentFile().getParentFile().getParent();
    {
        if (!new File(root + "/OpenJML").exists() || !new File(root + "/OpenJML/OpenJMLTest").exists()) {
            out.println("The current working directory for tests is incorrect");
            System.exit(1);
        }
    }
    
    public java.io.PrintStream tempout;
    {
        try {
            tempout = new java.io.PrintStream("tempout.txt");
        } catch (FileNotFoundException e) {
            out.println("Could not create temp file");
        }
    }
    
    /** Holds an absolute path to the location of system library spec files, that is the folder holding java/lang/*.jml etc. */
    public final static String specsdir = Main.specs;
    
    public final static String streamLine = "10"; // This line number is present in many test oracle files, but changes as edits are made to Stream.jml

    /** Replace aspects of expected output that depend on the local environment */
    public static String doReplacements(String s) {
        return s.replace("$ROOT",JmlTestSuite.root).replace("$SPECS",specsdir).replace("$STRL", JmlTestSuite.streamLine)
                .replaceAll("#DEMO", OpenJMLDemoPath);
    }

    /** An object holding routines for comparing actual output with expected output */
    public OutputCompare outputCompare = new OutputCompare();

    /** The name of the current test, injected by the initiating unit test structure (not used if a conventional JUnit test runner is used). */
    public String testname; // name is injected by the initiating unit test structure
    /** The name of the current test, when the OpenJML custom test runner is used */
    public String getTestName() { return testname; }
    
    /** This is here so we can get the name of a test, using name.getMethodName(), but this is valid only when
     * a conventional JUnit runner is used.
     **/
    @Rule public TestName testnameRule = new TestName();
    
    /** The java executable */
    // TODO: This is going to use the external setting for java, rather than
    // the current environment within Eclipse // FIXME - no longer valid
    // Needed for RAC tests
    protected String jdk = System.getProperty("java.home") + "/bin/java";

    /** Cached value of the end of line character string */
    static final public String eol = System.getProperty("line.separator");

    /** Adds arguments to the sequence of command-line arguments */
    public void addOptions(String ... options) {
    	main.addOptions(options);
    }

    /** A Diagnostic listener that can report all the collected diagnostics */
    static public interface DiagnosticListenerX<S> extends DiagnosticListener<S> {
        public List<Diagnostic<? extends S>> getDiagnostics();
    }
    
    public void allowNotes(boolean allow) {
        if (collector instanceof FilteredDiagnosticCollector c) c.noNotes = !allow;
    }
    
    /** A Diagnostic Listener that collects the diagnostics, so that they can be compared against expected results */
    final public static class FilteredDiagnosticCollector<S> implements DiagnosticListenerX<S> {
        /** Constructs a diagnostic listener that collects all of the diagnostics,
         * with the ability to filter out the notes.  If print is true, diagnostics are printed
         * as well as collected.
         */
        public FilteredDiagnosticCollector(boolean noNotes, /*@ nullable */ PrintStream out) {
            this.noNotes = noNotes;
            this.out = out;
        }
        
        /** If true, no notes are collected; some test output contains notes, so this must generally be false */
        boolean noNotes = false;
        /** Generally null, but if not null, diagnostics are printed (as well as being collected) -- helpful for seeing diagnostic messages
         * in the context of debugging output. */
        PrintStream out = null;
        
        // FIXME - comment
        Context context;
        
        /** The collection (in order) of diagnostics heard so far. */
        private java.util.List<Diagnostic<? extends S>> diagnostics =
            Collections.synchronizedList(new ArrayList<Diagnostic<? extends S>>());

        /** The method called by the system when there is a diagnostic to report,
         * implemented here to collect the diagnstic. */
        public void report(Diagnostic<? extends S> diagnostic) {
            diagnostic.getClass(); // null check
            if (out != null) out.println(diagnostic.toString());
            if (!noNotes || diagnostic.getKind() != Diagnostic.Kind.NOTE ||
            		diagnostic.getMessage(java.util.Locale.getDefault()).contains("Associated")) // FIXME - what 'kind' are associated declaration messages?
                diagnostics.add(diagnostic);
        }

        /**
         * Gets a list view of diagnostics collected by this object.
         *
         * @return a list view of diagnostics
         */
        public java.util.List<Diagnostic<? extends S>> getDiagnostics() {
            return Collections.unmodifiableList(diagnostics);
        }
    }
    
    // A class to manage communication with external processes, that is with both the input from
    // the external's System.out and from System.err. Just used for RAC.
    public static class StreamGobbler extends Thread
    {
        private InputStream is;
        private StringBuffer input = new StringBuffer();
        
        public StreamGobbler(InputStream is) {
            this.is = is;
        }
        
        public String input() {
            return input.toString();
        }
        
        public void run() {
            try (InputStreamReader isr = new InputStreamReader(is); BufferedReader br = new BufferedReader(isr)){
                char[] cbuf = new char[10000]; // The 10000 is arbitrary -- it just sets the max amount of input read at once
                                            // If less is available, the reader just reads what is available
                                            // If more is available, multiple reads will occur successively
                int n;
                while ((n = br.read(cbuf)) != -1) {
                    input.append(cbuf,0,n);
                }
            } catch (IOException ioe) {
                ioe.printStackTrace();  
            }
        }
    }
    
    /** Class used by the timeout mechanism */
    private static class InterruptScheduler extends TimerTask {
        Thread target = null;
        
        public InterruptScheduler(Thread target) {
            this.target = target;
        }
        
        @Override
        public void run() {
            target.interrupt();
        }
    }
    
    // FIXME - use JUnit's facility for timeout?
    
    /** Used to set a timeout on a RAC process; returns true if the process was interrupted by the timeout */
    public static boolean timeout(Process p, long milliseconds) {
        // Set a timer to interrupt the process if it does not return within the timeout period
        Timer timer = new Timer();
        timer.schedule(new InterruptScheduler(Thread.currentThread()), new Date(System.currentTimeMillis()+milliseconds));
        try {
            p.waitFor();
        } catch (InterruptedException e) {
            // Stop the process from running
            p.destroy();
            return true;
        } finally {
            // Stop the timer
            timer.cancel();
        }
        return false;
    }

    // References to various tools needed in testing
    protected Context context;
    protected Main main;
    
    /** This collection of mock files are those on the specs path */
    protected org.openjml.MockFiles mockFiles;
    /** This list of mock files are added to the command-line */
    protected LinkedList<JavaFileObject> javamockFiles = new LinkedList<>();
    
    /** Normally false, but set to true in tests of the test harness itself, to
     * avoid printing out diagnostic messages when a test intentionally fails.
     */
    public boolean noExtraPrinting = false;

    /** Set this to true in a test to print out more detailed information about
     * what the test is doing (as a debugging aid); should be false in normal
     * test execution.
     */
    public boolean print = false;
    
    /** Set in some testcase classes to ignore Notes reported by the tool. 
     *  Set the value before calling super.setUp()
     *  */
    public boolean ignoreNotes = true;

    /** Set this to true (in the setUp for a test, before calling super.setUp)
     * if you want diagnostics to be printed as they occur (as well as being collected).
     */
    public boolean printDiagnostics = System.getenv("VERBOSE") != null || System.getenv("PRINT") != null || System.getenv("SCANNER") != null || System.getenv("STACK") != null;
    
    /** A collector for all of the diagnostic messages*/
    protected DiagnosticListenerX<JavaFileObject> collector; // initialized in setUp()
    
    /** Set this to true (for an individual test) if you want debugging information */
    public boolean jmldebug = false;
    
    /** This does some setup, but most of it has to be left to the derived classes because we have to
     * set the options before we register most of the JML tools.
     */
    @Before
    public void setUp() throws Exception {
        if (System.getenv("NOJML")!=null) {
            fail("Cannot test with NOJML= within the test suite. Use a scripted test.");
        }
        try {
            main = new org.jmlspecs.openjml.Main("openjml-unittest",new PrintWriter(out, true));
            setCollector(ignoreNotes, printDiagnostics ? out : null);
            context = main.initialize(collector);
            ((FilteredDiagnosticCollector<JavaFileObject>)collector).context = context;

            mockFiles = main.mockFiles;
            Log.alwaysReport = true; // Always report errors (even if they would be suppressed because they are at the same position
        } catch (Throwable t) {
            fail("EXCEPTION IN SETUP");
            t.printStackTrace(out);
        }
    }
    
    public void setCollector(boolean ignoreNotes, PrintStream printer) {
        collector = new FilteredDiagnosticCollector<JavaFileObject>(ignoreNotes,printer);    	
    }
    
    /** Calls compile, converting the List of options and files to an array */
    public int compile(com.sun.tools.javac.util.List<String> args) {
    	return compile(args.toArray(new String[args.size()]));
    }
    
    /** Calls compile, converting the java.util.List of options and files to an array */
    public int compile(java.util.List<String> args) {
    	return compile(args.toArray(new String[args.size()]));
    }
    
    /** Calls main.compile, i.e. runs openjml on the array of command-line arguments (options and files).
     * Note that the called method will also use anything in main.mockFiles
     */
    public int compile(String ... args) {
		return main.compile(args, this.context).exitCode;  // FIXME - main already has context -- why do we need to pass it in
    }
    
    /** Nulls out all the references visible in this class */
    @After
    public void tearDown() throws Exception {
        context = null;
        main.close();
        main = null;
        collector = null;
        if (mockFiles != null) mockFiles.clear(); 
        mockFiles = null;
    }

    /** Does a tearDown and a setUp, in order to reset state for a second execution in the same test */
    public void reset() {
        try {
            tearDown();
            setUp();
        } catch (Exception e) {
            org.junit.Assert.assertTrue("tearDown/setUp failed: " + e, false);
        }
    }


    /** Prints out the errors collected by the diagnostic listener */
    public void printDiagnostics() {
        this.out.print(diagnosticsToString(collector.getDiagnostics())); // diagnostic string includes a eol
        this.out.flush();
    }
    
    public static String diagnosticToString(Diagnostic<? extends JavaFileObject> diag) {
        long line = diag.getLineNumber();
        long start = diag.getStartPosition();
        long pos = diag.getPosition();
        long end = diag.getEndPosition();
        long col = diag.getColumnNumber();
        return (noSource(diag) + " line=" + line + " col=" + col + " start=" + start + " pos=" + pos + " end=" + end);
    }

    public static String diagnosticsToString(Iterable<Diagnostic<? extends JavaFileObject>> diagnostics) {
        String r = "";
        for (Diagnostic<? extends JavaFileObject> dd: diagnostics) {
            r += diagnosticToString(dd) + "\n";
        }
        return r;
    }
    
    /** Checks that all of the collected diagnostic messages match the data supplied, throwing an AssertionError if not.
     * The input list is expected to have a sequence of message, column, start, position, end for each diagnostic in sequence.
     * If there is just one number, it is the column */
    public void checkDiagnostics(Object ...  expected) { // FIXME - change to an outputCompare
        outputCompare.compareResults(expected,  collector, true);
    }
    
    protected ByteArrayOutputStream berr;
    protected ByteArrayOutputStream bout;
    protected PrintStream savederr;
    protected PrintStream savedout;
    protected String recordedErr;
    protected String recordedOut;

    /** Manages the capturing of output to System.out and System.err; call with argument=true to start
     * capturing; call with the argument=false to stop capturing, at which point the Strings recordedOut 
     * and recordedErr will contain the collected output (access them through output() and errorOutput() ).
     * 
     * To be thread-safe and to work with this output collection, tests must all use this.out and this.err,
     * not System.out and System.err.
     */
    public void collectSystemOutput(boolean collect) {
        if (collect) {
            //System.out.println("STARTING COLLECTING " + (bout == null));
            if (bout != null) return; // Already collecting
            recordedOut = null;
            recordedErr = null;
            savederr = System.err;
            savedout = System.out;
            System.setErr(new PrintStream(berr=new ByteArrayOutputStream(10000)));
            System.setOut(new PrintStream(bout=new ByteArrayOutputStream(10000)));
            this.out = System.out;
            //savedout.println("STARTING COLLECTING-A " + (berr!=null));
        } else {
            //savedout.println("ENDING COLLECTING " + (bout != null) + " " + (berr!=null));
            if (bout == null) return; // Already not collecting
            System.err.flush();
            System.out.flush();
            System.setErr(savederr);
            System.setOut(savedout);
            //System.out.println("ENDED COLLECTING-A " + (bout != null) + " " + (berr!=null) + " " + recordedOut);
            this.out = System.out;
            recordedErr = berr.toString();
            recordedOut = bout.toString();
            bout = berr = null;
            //System.out.println("ENDED COLLECTING " + recordedOut + " " + (berr!=null) + " ##" + recordedErr + "##");
        }
    }
    
    /** Returns the standard-out output; valid once collectOutput(false) has been called. */
    public String output() { 
        if (bout != null) collectSystemOutput(false);
        return recordedOut;
    }
    /** Returns the standard-err output; valid once collectOutput(false) has been called. */
    public String errorOutput() { 
        if (berr != null) collectSystemOutput(false);
        return recordedErr;
    }


    /** Used to add a pseudo file to the file system. Note that for testing, a 
     * typical filename given here might be #B/A.java, where #B denotes a 
     * mock directory on the specification path
     * @param filename the name of the file, including leading directory components 
     * @param content the String constituting the content of the pseudo-file
     */
    protected void addMockFile(/*@ non_null */ String filename, /*@ non_null */String content) {
        try {
            addMockFile(filename,new MockJavaFileObject(new URI("file:///" + filename),content));
        } catch (Exception e) {
            fail("Exception in creating a URI: " + e);
        }
    }

    /** Used to add a pseudo file to the file system. Note that for testing, a 
     * typical filename given here might be #B/A.java, where #B denotes a 
     * mock directory on the specification path
     * @param filename the name of the file, including leading directory components 
     * @param file the JavaFileObject to be associated with this name
     */
    protected void addMockFile(String filename, JavaFileObject file) { // FIXME - why not use the filename in the JavaFileObject
        if (filename.endsWith(".java")) javamockFiles.add(file);
        mockFiles.addMockFile(filename, file);
    }
    
    /** Prints a diagnostic as it is in an error or warning message, but without
     * any line of source code (or pointer to a column).  
     * This is how dd.toString() used to behave, but in OpenJDK
     * build 55, toString also included the source information.  So we need to 
     * wrap dd in this call (or change all of the tests).
     * @param dd the diagnostic
     * @return
     */
    static protected String noSource(Diagnostic<? extends JavaFileObject> dd) {
        return dd instanceof JCDiagnostic ? noSource((JCDiagnostic)dd) : dd.toString();
    }

   /** Returns the diagnostic message without the source code line;
     *  source file may be null, in which case it is omitted from the generated string;
     *  line number may be -1, in which case it is omitted also */
    static String noSource(JCDiagnostic dd) {
        var f = dd.getFormatter();
        var l = java.util.Locale.getDefault();
        String src = dd.getSource() == null ? "" : (f.formatSource(dd,true,l) + ":");
        String ln = dd.getLineNumber() == Position.NOPOS ? "" : (dd.getLineNumber() + ":" );
        String sp = src.isEmpty() && ln.isEmpty() ? "" : " ";
        return src + ln + sp + dd.getPrefix() + dd.getMessage(l);
    }

    /** Used by some tests to set the Java deprecation option */
    public void setDeprecation() {
        Options.instance(context).put("-Xlint:deprecation","true");
    }

    /** Used to indicate that just one of the list of objects will be part of the test output */
    static public OneOf oneof(Object ... list) { return new OneOf(list); }
    /** Used to indicate that all of the listed objects will be in the test output, but in an arbitrary order */
    static public AnyOrder anyorder(Object ... list) { return new AnyOrder(list); }
    /** Used to indicate that the given list is optionally part of the test output */
    static public Optional optional(Object ... list) { return new Optional(list); }
    /** Used to indicate that the list objects should all be sequentially found in the test output */
    static public Seq seq(Object ... list) { return new Seq(list); }
}


