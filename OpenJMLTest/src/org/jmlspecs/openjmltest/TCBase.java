package org.jmlspecs.openjmltest;
import java.net.URI;

import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlOption;

import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;

import static org.junit.Assert.*;

import org.jmlspecs.openjmltest.OutputCompare.*;
import org.openjml.MockJavaFileObject;


/** This is a base class for all tests that parse and typecheck a
 * test string (containing a compilation unit) of source code.  
 * Mock files are created (or real ones used)
 * to simulate a set of input files.  Any diagnostics are captured with
 * a listener and compared with the expected diagnostics.
 * 
 * FIXME - should we be checking the out and err outputs as well?
 */
public abstract class TCBase extends JmlTestSuite {

    protected static String testspecpath1 = "$A"+z+"$B";
    protected String testspecpath;
    protected String testSourcePath;
    protected int expectedExit;
    
    @Override @org.junit.Before
    public void setUp() throws Exception {
    	testspecpath = testspecpath1;
        testSourcePath = testspecpath1;
        super.setUp();
        addOptions("--specs-path",   testspecpath);
        addOptions("--source-path",  testSourcePath);
        addOptions("--class-path",   "src" + z + testSourcePath);
        addOptions("-Xlint:unchecked");
        expectedExit = -1; // -1 means use default: some message==>1, no messages=>0
                    // this needs to be set manually if all the messages are warnings
    }

    public void helpTCText(/*@ nullable*/String mockFilename, String content, Object ... expected) {
        JavaFileObject f = new MockJavaFileObject(mockFilename,content);
        List<JavaFileObject> files = List.of(f);
        
        // Includes any options already added through addOptions() -- FIXME - verify this; check in tcharness
        int ex = main.compile(new String[]{ }, files).exitCode; // FIXME - get rid of first argument?
        
        if (print) printDiagnostics();
        outputCompare.compareResults(expected, collector, true);

        if (expectedExit == -1) expectedExit = expected.length == 0?0:1;
        if (expectedExit != ex && !print) printDiagnostics();
        assertEquals("Wrong exit code",expectedExit, ex);
    }
}

