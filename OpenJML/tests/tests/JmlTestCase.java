package tests;
import java.io.PrintWriter;
import java.net.URI;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticCollector;
import javax.tools.DiagnosticListener;
import javax.tools.JavaFileObject;

import org.junit.*;
import static org.junit.Assert.*;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.util.Options;
import java.util.*;
import java.util.concurrent.TimeoutException;
import java.io.*;


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
public abstract class JmlTestCase extends junit.framework.TestCase {

    /** A purposefully short abbreviation for the system path separator
     * ( ; or : )
     */
    static final public String z = java.io.File.pathSeparator;

    static public interface DiagnosticListenerX<S> extends DiagnosticListener<S> {
        public List<Diagnostic<? extends S>> getDiagnostics();
    }

    final static public class FilteredDiagnosticCollector<S> implements DiagnosticListenerX<S> {
        /** Constructs a diagnostic listener that collects all of the diagnostics,
         * with the ability to filter out the notes.
         * @param filtered if true, no notes (only errors and warnings) are collected
         */
        public FilteredDiagnosticCollector(boolean filtered) {
            this.filtered = filtered;
        }
        
        /** If true, no notes are collected. */
        boolean filtered;
        
        /** The collection (in order) of diagnostics heard so far. */
        private java.util.List<Diagnostic<? extends S>> diagnostics =
            Collections.synchronizedList(new ArrayList<Diagnostic<? extends S>>());

        /** The method called by the system when there is a diagnostic to report. */
        public void report(Diagnostic<? extends S> diagnostic) {
            diagnostic.getClass(); // null check
            if (!filtered || diagnostic.getKind() != Diagnostic.Kind.NOTE)
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
    
    private class InterruptScheduler extends TimerTask {
        Thread target = null;
        
        public InterruptScheduler(Thread target) {
            this.target = target;
        }
        
        @Override
        public void run() {
            target.interrupt();
        }
    }
    
    public boolean timeout(Process p, long milliseconds) {
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
    Context context;
    Main main;
    Options options;
    JmlSpecs specs; // initialized in derived classes
    LinkedList<JavaFileObject> mockFiles;
    
    /** Normally false, but set to true in tests of the test harness itself, to
     * avoid printing out diagnostic messages when a test fails.
     */
    public boolean noExtraPrinting = false;

    /** Set this to true in a test to print out more detailed information about
     * what the test is doing (as a debugging aid).
     */
    public boolean print = false;
    
    /** Set this to true (in the setUp for a test, before calling super.setUp)
     * if you want diagnostics to be printed as they occur, rather than being
     * collected.
     */
    public boolean noCollectDiagnostics = false;
    
    /** A collector for all of the diagnostic messages */
    DiagnosticListenerX<JavaFileObject> collector = new FilteredDiagnosticCollector<JavaFileObject>(false);
    
    /** Set this to true (for an individual test) if you want debugging information */
    public boolean jmldebug = false;
    
    /** This does some setup, but most of it has to be left to the derived classes because we have to
     * set the options before we register most of the JML tools.
     */
    protected void setUp() throws Exception {
        main = new Main("",new PrintWriter(System.out, true),!noCollectDiagnostics?collector:null);
        context = main.context();
        options = Options.instance(context);
        if (jmldebug) { Utils.instance(context).jmldebug = true; options.put("-jmldebug", "");}
        print = false;
        mockFiles = new LinkedList<JavaFileObject>();
        //System.out.println("JUnit: Testing " + getName());
    }

    /** Nulls out all the references visible in this class */
    @After
    protected void tearDown() throws Exception {
        context = null;
        main = null;
        collector = null;
        options = null;
        specs = null;
    }


    /** Prints a diagnostic as it is in an error or warning message, but without
     * any source line.  This is how dd.toString() used to behave, but in OpenJDK
     * build 55, toString also included the source information.  So we need to 
     * wrap dd in this call (or change all of the tests).
     * @param dd the diagnostic
     * @return
     */
    protected String noSource(Diagnostic<? extends JavaFileObject> dd) {
        return dd instanceof JCDiagnostic ? ((JCDiagnostic)dd).noSource() : dd.toString();
    }

    
    /** Prints out the errors collected by the diagnostic listener */
    public void printErrors() {
        System.out.println("ERRORS " + collector.getDiagnostics().size() + " " + getName());
        for (Diagnostic<? extends JavaFileObject> dd: collector.getDiagnostics()) {
            System.out.println(noSource(dd) + " col=" + dd.getColumnNumber());
        }
    }

    /** Checks that all of the collected error messages match the data supplied
     * in the arguments.
     * @param errors an array of expected error messages that are checked against the actual messages
     * @param cols an array of expected column numbers that are checked against the actual diagnostics
     */
    public void checkMessages(/*@ non_null */String[] errors, /*@ non_null */int[] cols) {
        List<Diagnostic<? extends JavaFileObject>> diags = collector.getDiagnostics();
        if (print || (!noExtraPrinting && errors.length != diags.size())) printErrors();
        assertEquals("Saw wrong number of errors ",errors.length,diags.size());
        assertEquals("Saw wrong number of columns ",cols.length,diags.size());
        for (int i = 0; i<diags.size(); ++i) {
            assertEquals("Message for item " + i,errors[i],noSource(diags.get(i)));
            assertEquals("Column number for item " + i,cols[i],diags.get(i).getColumnNumber()); // Column number is 1-based
        }
    }

    /** Checks that all of the collected error messages match the data supplied
     * in the arguments.
     * @param a a sequence of expected values, alternating between error message and column numbers
     */
    public void checkMessages(/*@ nonnullelements */Object ... a) {
        try {
            assertEquals("Wrong number of messages seen",a.length,2*collector.getDiagnostics().size());
            List<Diagnostic<? extends JavaFileObject>> diags = collector.getDiagnostics();
            if (print || (!noExtraPrinting && 2*diags.size() != a.length)) printErrors();
            assertEquals("Saw wrong number of errors ",a.length,2*diags.size());
            for (int i = 0; i<diags.size(); ++i) {
                assertEquals("Message for item " + i,a[2*i].toString(),noSource(diags.get(i)));
                assertEquals("Column number for item " + i,((Integer)a[2*i+1]).intValue(),diags.get(i).getColumnNumber()); // Column number is 1-based
            }
        } catch (AssertionError ae) {
            if (!print && !noExtraPrinting) printErrors();
            throw ae;
        }
    }
    
    /** Checks that there are no diagnostic messages */
    public void checkMessages() {
        if (print || (!noExtraPrinting && 0 != 2*collector.getDiagnostics().size())) printErrors();
        assertEquals("Saw wrong number of errors ",0,collector.getDiagnostics().size());
    }

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
        mockFiles.add(file);
        specs.addMockFile(filename,file);
    }


}


