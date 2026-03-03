package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.JmlTestSuite;

import static com.sun.tools.javac.parser.Tokens.*;
import static com.sun.tools.javac.parser.Tokens.TokenKind.*;
import static org.jmlspecs.openjml.ext.SingletonExpressions.*;
import static org.junit.Assert.assertEquals;

import org.jmlspecs.openjml.IJmlClauseKind;

import com.sun.tools.javac.parser.JavaTokenizer;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.JmlToken;
import com.sun.tools.javac.parser.Scanner;
import com.sun.tools.javac.parser.ScannerFactory;
import com.sun.tools.javac.util.Log;

import org.junit.*;
import org.openjml.MockJavaFileObject;


/** This test suite checks that various debug options run without crashing (and also executes code lines for coverage measurement).
 * In particular, this code makes use of static fields in OpenJML that are only used for debugging because they are not thread safe
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class staticstuff extends JmlTestSuite {

    ScannerFactory fac;
    
    // TODO - do we need to collect and compare System.out,err
    
    /** Initializes a fresh scanner factory for each test */
    @Override @org.junit.Before
    public void setUp() throws Exception {
        super.setUp(); // Sets up a main program, diagnostic collector
        org.jmlspecs.openjml.JmlOptions.instance(context).optionsAllSet = true;
        fac = ScannerFactory.instance(context);
        print = false;
    }
    
    @Override @org.junit.After
    public void tearDown() throws Exception {
        super.tearDown();
    }

    @Test public void debugScanner() {
        var text = "a /*@ requires true; */ //@ ensures c; \n //@ forbid  ";
        Log.instance(context).useSource(new MockJavaFileObject(text));
        JmlScanner sc = (JmlScanner)fac.newScanner(text, true);
        sc.scannerDebug = true;
        do {
            sc.nextToken();
        } while (sc.token().kind != EOF && sc.token().kind != ERROR);
        JavaTokenizer.scannerDebug = sc.scannerDebug = false;
        printDiagnostics();
        assertEquals("Saw wrong number of messages ",0,collector.getDiagnostics().size());
    }
}
