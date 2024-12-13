package org.jmlspecs.openjmltest;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.net.URI;
import java.nio.file.Paths;
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

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Utils;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.rules.TestName;

import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Position;


/** This class provides basic functionality for the JUnit tests for OpenJML.
 * It is expected that actual JUnit test suites will derive from this class.
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
public abstract class JmlTestCase {

    // The test output expects that the current working directory while running unittests is  .../OpenJML/OpenJMLTest

    // In a 'standard' local OpenJML github working environment, root will be the container for
    // OpenJML/OpenJML21, OpenJML/OpenJMLTest, Specs, etc.
    // This value is needed because some tests emit a full absolute path name in error messages
    static final public String root = new File(".").getAbsoluteFile().getParentFile().getParentFile().getParent();
    {
    	if (!new File(root + "/OpenJML").exists() || !new File(root + "/OpenJML/OpenJMLTest").exists()) {
    		System.out.println("The current working directory for tests is incorrect");
    		System.exit(1);
    	}
    }
    static final public String bruntime = "../" + root + "/OpenJML/OpenJML21/bin-runtime";
    static final public String  runtime = "../" + root + "/OpenJML/OpenJML21/runtime";

    public final static String specsdir;
    static {
    	String s = System.getenv("OPENJML_ROOT") + "../../Specs/specs";
    	try { s = new File(s).getCanonicalPath(); } catch (Exception e) {}
    	specsdir = s;
    }
    public final static String streamLine = "10"; // This line number is present in many test oracle files, but changes as edits are made to Stream.jml
    /** Replace aspects of expected output that depend on the local environment */
    public static String doReplacements(String s) {
        return s.replace("$ROOT",JmlTestCase.root).replace("$SPECS",specsdir).replace("$STRL", JmlTestCase.streamLine)
        		.replaceAll("#DEMO", RacBase.OpenJMLDemoPath);
    }
    
    // FIXME - do not rely on eclipse
    static protected String projLocation = System.getProperty("openjml.eclipseProjectLocation");
    
    // An object holding routines for comparing output with oracle output
    public OutputCompare outputCompare = new OutputCompare();

    /** This is here so we can get the name of a test, using name.getMethodName() */
    @Rule public TestName name = new TestName();
    
    public String getMethodName(int i) {
    	return (new RuntimeException()).fillInStackTrace().getStackTrace()[i+1].getMethodName();
    }
    

    /** The java executable */
    // TODO: This is going to use the external setting for java, rather than
    // the current environment within Eclipse // FIXME - no longer valid
    // Needed for RAC tests
    protected String jdk = System.getProperty("java.home") + "/bin/java";

    /** A purposefully short abbreviation for the system path separator
     * ( ; or : )
     */
    static final public String z = java.io.File.pathSeparator;
    
    /** Cached value of the end of line character string */
    static final public String eol = System.getProperty("line.separator");

    /** A Diagnostic listener that can report all the collected diagnostics */
    static public interface DiagnosticListenerX<S> extends DiagnosticListener<S> {
        public List<Diagnostic<? extends S>> getDiagnostics();
    }
    
    // Set in some testcase classes to ignore Notes reported by the tool. Set the value
    // before calling super.setUp()
    public boolean ignoreNotes = true;
    
    public void addOptions(String ... options) {
    	main.addOptions(options);
    }
   

    /** A Diagnostic Listener that collects the diagnostics, so that they can be compared against expected results */
    final public static class FilteredDiagnosticCollector<S> implements DiagnosticListenerX<S> {
        /** Constructs a diagnostic listener that collects all of the diagnostics,
         * with the ability to filter out the notes.
         * @param noNotes if true, no notes (only errors and warnings) are collected
         */
        public FilteredDiagnosticCollector(boolean noNotes, boolean print) {
            this.noNotes = noNotes;
            this.print = print;
        }
        
        /** If true, no notes are collected; some test output contains notes, so this mut generally be false */
        boolean noNotes;
        /** If true, diagnostics are printed (as well as being collected) */
        boolean print;
        
        Context context;
        
        /** The collection (in order) of diagnostics heard so far. */
        private java.util.List<Diagnostic<? extends S>> diagnostics =
            Collections.synchronizedList(new ArrayList<Diagnostic<? extends S>>());

        /** The method called by the system when there is a diagnostic to report. */
        public void report(Diagnostic<? extends S> diagnostic) {
            diagnostic.getClass(); // null check
        	//if (System.getenv("NOJML")==null) System.out.println("LOG-VDH " + Log.instance(context).getDiagnosticFormatter().getClass() + " " + Log.instance(context).getDiagnosticFormatter().hashCode());
            //if (print) System.out.println(Log.instance(context).getDiagnosticFormatter().format(diagnostic, Locale.getDefault()));
            if (print) System.out.println(diagnostic.toString());
            //((JCDiagnostic)diagnostic).setFormatter(Log.instance(context).getDiagnosticFormatter());
            //if (print) System.out.println(diagnostic.toString());
           if (!noNotes || diagnostic.getKind() != Diagnostic.Kind.NOTE ||
            		diagnostic.getMessage(java.util.Locale.getDefault()).contains("Associated"))
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
            try {
                char[] cbuf = new char[10000];
                InputStreamReader isr = new InputStreamReader(is);
                BufferedReader br = new BufferedReader(isr);
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
    
    /** Used to set a timeout on a RAC process */
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
    protected Options options;
    protected JmlSpecs specs; // initialized in derived classes
    protected LinkedList<JavaFileObject> mockFiles;
    
    /** Normally false, but set to true in tests of the test harness itself, to
     * avoid printing out diagnostic messages when a test intentionally fails.
     */
    public boolean noExtraPrinting = false;

    /** Set this to true in a test to print out more detailed information about
     * what the test is doing (as a debugging aid).
     */
    public boolean print = false;
    
    /** Set this to true (in the setUp for a test, before calling super.setUp)
     * if you want diagnostics to be printed as they occur (as well as being collected).
     */
    public boolean printDiagnostics = System.getenv("VERBOSE") != null || System.getenv("PRINT") != null || System.getenv("SCANNER") != null || System.getenv("STACK") != null;
    
    /** A collector for all of the diagnostic messages*/
    protected DiagnosticListenerX<JavaFileObject> collector;
    
    /** Set this to true (for an individual test) if you want debugging information */
    public boolean jmldebug = false;
    
    /** This does some setup, but most of it has to be left to the derived classes because we have to
     * set the options before we register most of the JML tools.
     */
    @Before
    public void setUp() throws Exception {
        main = new org.jmlspecs.openjml.Main("openjml-unittest",new PrintWriter(System.out, true));
        setCollector(ignoreNotes, printDiagnostics);
        if (System.getenv("NOJML")!=null) {
            context = main.context = new Context();
            JavacFileManager.preRegister(context); // can't create it until Log has been set up
        } else {
            try {
        	context = main.initialize(collector);
            } catch (Exception e) {
                e.printStackTrace(System.out);
            }
        }
        ((FilteredDiagnosticCollector<JavaFileObject>)collector).context = context;

        specs = JmlSpecs.instance(context);
        mockFiles = new LinkedList<JavaFileObject>();
        Log.alwaysReport = true; // Always report errors (even if they would be suppressed because they are at the same position
        if (System.getenv("VERBOSE") != null) {
        	main.addOptions("-verbose","true"); // FIXME
        	main.addOptions("-jmlverbose","3");
        }
    }
    
    public void setCollector(boolean ignoreNotes, boolean printDiagnostics) {
        collector = new FilteredDiagnosticCollector<JavaFileObject>(ignoreNotes,printDiagnostics);    	
    }
    
    public int compile(com.sun.tools.javac.util.List<String> args) {
    	return compile(args.toArray(new String[args.size()]));
    }
    
    public int compile(java.util.List<String> args) {
    	return compile(args.toArray(new String[args.size()]));
    }
    
    public int compile(String ... args) {
		return main.compile(args, this.context).exitCode;
    }
    
    /** Nulls out all the references visible in this class */
    @After
    public void tearDown() throws Exception {
        context = null;
        main = null;
        collector = null;
        options = null;
        specs = null;
        mockFiles.clear(); mockFiles = null;
    }


    
    /** Prints out the errors collected by the diagnostic listener */
    public void printDiagnostics() {
    	synchronized (System.out) {
    		System.out.println("DIAGNOSTICS " + collector.getDiagnostics().size() + " " + name.getMethodName());
    		for (Diagnostic<? extends JavaFileObject> dd: collector.getDiagnostics()) {
    			long line = dd.getLineNumber();
    			long start = dd.getStartPosition();
    			long pos = dd.getPosition();
    			long end = dd.getEndPosition();
    			long col = dd.getColumnNumber();
    			System.out.println(noSource(dd) + " line=" + line + " col=" + col + " pos=" + pos + " start=" + start + " end=" + end);
    		}
    	}
    }

//    /** Checks that all of the collected diagnostic messages match the data supplied
//     * in the arguments.
//     * @param messages an array of expected messages that are checked against the actual messages
//     * @param cols an array of expected column numbers that are checked against the actual diagnostics
//     */ // TODO - not used
//    public void checkMessages(/*@ non_null */String[] messages, /*@ non_null */int[] cols) {
//        List<Diagnostic<? extends JavaFileObject>> diags = collector.getDiagnostics();
//        if (print || (!noExtraPrinting && messages.length != diags.size())) printDiagnostics();
//        assertEquals("Saw wrong number of errors ",messages.length,diags.size());
//        assertEquals("Saw wrong number of columns ",cols.length,diags.size());
//        for (int i = 0; i<diags.size(); ++i) {
//            assertEquals("Message for item " + i,messages[i],noSource(diags.get(i)));
//            assertEquals("Column number for item " + i,cols[i],diags.get(i).getColumnNumber()); // Column number is 1-based
//        }
//    }

    /** Checks that all of the collected messages match the data supplied
     * in the arguments.
     * @param a a sequence of expected values, alternating between error message and column numbers
     */
    public void checkMessages(/* nonnullelements */Object ... a) {
        try {
            assertEquals("Wrong number of messages seen",a.length,2*collector.getDiagnostics().size());
            List<Diagnostic<? extends JavaFileObject>> diags = collector.getDiagnostics();
            if (print || (!noExtraPrinting && 2*diags.size() != a.length)) printDiagnostics();
            assertEquals("Saw wrong number of errors ",a.length,2*diags.size());
            for (int i = 0; i<diags.size(); ++i) {
                assertEquals("Message for item " + i,a[2*i].toString(),noSource(diags.get(i)));
                assertEquals("Column number for item " + i,((Integer)a[2*i+1]).intValue(),diags.get(i).getColumnNumber()); // Column number is 1-based
            }
        } catch (AssertionError ae) {
            if (!print && !noExtraPrinting) printDiagnostics();
            throw ae;
        }
    }
    
    /** Checks that there are no diagnostic messages */
    public void checkMessages() {
        if (print || (!noExtraPrinting && 0 != 2*collector.getDiagnostics().size())) printDiagnostics();
        assertEquals("Saw wrong number of messages ",0,collector.getDiagnostics().size());
    }

    protected ByteArrayOutputStream berr;
    protected ByteArrayOutputStream bout;
    protected PrintStream savederr;
    protected PrintStream savedout;
    protected String recordedErr;
    protected String recordedOut;

    /** Manages the capturing of output to System.out and System.err; call with argument=true to start
     * capturing; call with the argument=false to stop capturing, at which point the Strings actualOut 
     * and actualErr will contain the collected output (access them through output() and errorOutput() ).
     */
    public void collectOutput(boolean collect) {
        if (collect) {
        	if (bout != null) return; // Already collecting
            recordedOut = null;
            recordedErr = null;
            savederr = System.err;
            savedout = System.out;
            System.setErr(new PrintStream(berr=new ByteArrayOutputStream(10000)));
            System.setOut(new PrintStream(bout=new ByteArrayOutputStream(10000)));
        } else {
        	if (bout == null) return; // Already not collecting
            System.err.flush();
            System.out.flush();
            recordedErr = berr.toString();
            recordedOut = bout.toString();
            berr = null;
            bout = null;
            System.setErr(savederr);
            System.setOut(savedout);
        }
    }
    
    /** Returns the standard-out output; valid once collectOutput(false) has been called. */
    public String output() { return recordedOut; }
    /** Returns the standard-err output; valid once collectOutput(false) has been called. */
    public String errorOutput() { return recordedErr; }


    /** Used to add a pseudo file to the file system. Note that for testing, a 
     * typical filename given here might be #B/A.java, where #B denotes a 
     * mock directory on the specification path
     * @param filename the name of the file, including leading directory components 
     * @param content the String constituting the content of the pseudo-file
     */
    protected void addMockFile(/*@ non_null */ String filename, /*@ non_null */String content) {
        try {
            addMockFile(filename,new TestJavaFileObject(new URI("file:///" + filename),content));
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
    protected void addMockFile(String filename, JavaFileObject file) {
        if (filename.endsWith(".java")) mockFiles.add(file);
        specs.addMockFile(filename,file);
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
    	// This ought to match the format being used, but only does so manually
    	var f = dd.getFormatter();
    	var l = java.util.Locale.getDefault();
    	String src = dd.getDiagnosticSource() == null ? "" : (f.formatSource(dd,true,l) + ":");
    	String ln = dd.getLineNumber() == Position.NOPOS ? "" : (dd.getLineNumber() + ":" );
    	String sp = src.isEmpty() && ln.isEmpty() ? "" : " ";
        return src + ln + sp + dd.getPrefix() + dd.getMessage(l);
    }

    /** Used by some tests to set the Java deprecation option */
    public void setDeprecation() {
        Options.instance(context).put("-Xlint:deprecation","true");
    }

}


