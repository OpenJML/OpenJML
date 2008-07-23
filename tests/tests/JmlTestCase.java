package tests;
import java.util.ArrayList;
import java.util.Collections;
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
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.util.Options;


/** This class provides basic functionality for the JUnit tests for OpenJML.
 * It is expected that actual JUnit test suites will derive from this class.
 * 
 * @author David Cok
 *
 */
public abstract class JmlTestCase extends junit.framework.TestCase {

    static public interface DiagnosticListenerX<S> extends DiagnosticListener<S> {
        public List<Diagnostic<? extends S>> getDiagnostics();
    }

    final static public class FilteredDiagnosticCollector<S> implements DiagnosticListenerX<S> {
        public FilteredDiagnosticCollector(boolean filtered) {
            this.filtered = filtered;
        }
        boolean filtered;
        
        private java.util.List<Diagnostic<? extends S>> diagnostics =
            Collections.synchronizedList(new ArrayList<Diagnostic<? extends S>>());

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

    // References to various tools needed in testing
    Context context;
    Main main;
    Options options;
    JmlSpecs specs; // initialized in derived classes
    
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
        //super.setUp();
        main = new Main();
        context = new Context();
        if (!noCollectDiagnostics) context.put(DiagnosticListener.class, collector);
        JavacFileManager.preRegister(context); // can't create it until Log has been set up
        options = Options.instance(context);
        if (jmldebug) { Utils.jmldebug = true; options.put("-jmldebug", "");}
        print = false;
    }

    /** Nulls out all the references visible in this class */
    @After
    protected void tearDown() throws Exception {
        //super.tearDown();
        context = null;
        main = null;
        collector = null;
        options = null;
        specs = null;
    }


 

    
    /** Prints out the errors collected by the diagnostic listener */
    public void printErrors() {
        System.out.println("ERRORS " + collector.getDiagnostics().size() + " " + getName());
        for (Diagnostic<? extends JavaFileObject> dd: collector.getDiagnostics()) {
            System.out.println(dd + " col=" + dd.getColumnNumber());
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
            assertEquals("Node type for token " + i,errors[i],diags.get(i).toString());
            assertEquals("Column number for token " + i,cols[i],diags.get(i).getColumnNumber()); // Column number is 1-based
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
            if (print || 2*diags.size() != a.length) printErrors();
            assertEquals("Saw wrong number of errors ",a.length,2*diags.size());
            for (int i = 0; i<diags.size(); ++i) {
                assertEquals("Node type for token " + i,a[2*i].toString(),diags.get(i).toString());
                assertEquals("Column number for token " + i,((Integer)a[2*i+1]).intValue(),diags.get(i).getColumnNumber()); // Column number is 1-based
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


    /* Just to avoid Junit framework complaints about no tests */
//    public void test() {} 
}


