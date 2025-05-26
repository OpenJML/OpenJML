package org.jmlspecs.openjmltest;
import java.net.URI;

import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlSpecs;

import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;

import static org.junit.Assert.*;

import org.jmlspecs.openjmltest.OutputCompare.*;


/** This is a base class for all tests that parse and typecheck a
 * test string of source code.  Mock files are created (or real ones used)
 * to simulate a set of input files.  Any diagnostics are captured with
 * a listener and compared with the expected diagnostics.
 * 
 * FIXME - should we be checking the out and err outputs as well?
 * 
 * @author David R. Cok
 *
 */
public abstract class TCBase extends JmlTestSuite {

    protected static String z = java.io.File.pathSeparator;
    protected static String testspecpath1 = "$A"+z+"$B"+z+root+"/Specs/specs";
    protected String testspecpath;
    protected String testSourcePath;
    protected int expectedExit;
    protected boolean specialCompare;
    
    @Override
    public void setUp() throws Exception {
    	testspecpath = testspecpath1;
        testSourcePath = testspecpath1;
        specialCompare = false;
        super.setUp();
        addOptions("--specs-path",   testspecpath + z + "$SY" );
        addOptions("--source-path",   testSourcePath);
        addOptions("--class-path",   "src" + z + testSourcePath);
        addOptions(JmlOption.PURITYCHECK.optionName()+"=false");
        expectedExit = -1; // -1 means use default: some message==>1, no messages=>0
                    // this needs to be set manually if all the messages are warnings
        //print = true;
    }
    
    @Override
    public void tearDown() throws Exception {
        super.tearDown();
    }

    // Helper method for tests: content is the test text; list are the expected messages and column numbers
    public void helpTC(String content, Object ... list) {
        helpTCX(null,content,list);
    }

    // Helper method for tests: 
    // filename is the pseudo-filename in which content is considered to be
    // content is the test text; 
    // list are the expected messages and column numbers
    public void helpTCF(/*@ nullable*/String filename, String content, Object ... expected) {
        helpTCX(filename,content,expected);
    }

    // Helper method for tests: 
    // filename is the pseudo-filename in which content is considered to be
    // content is the test text; 
    // list are the expected messages and column numbers
    public void helpTCX(/*@ nullable*/String filename, String content, Object ... expected) {
        try {
            JavaFileObject f = new TestJavaFileObject(filename,content);
            if (filename != null) addMockFile("#B/" + filename,f);
            Log.instance(context).useSource(f);
            List<JavaFileObject> files = List.of(f);
            // If additional Java options are wanted (e.g. -verbose), add them here
            int ex = main.compile(new String[]{ "-Xlint:unchecked" }, files).exitCode;
            
            if (!specialCompare) checkDiagnostics(expected); // This comparator does not handle seq, anyorder etc.
            else outputCompare.compareResults(expected, collector); // This comparator does not handle having more than one position number
            
            if (expectedExit == -1) expectedExit = expected.length == 0?0:1;
            assertEquals("Wrong exit code",expectedExit, ex);
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }
}

