package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.fail;

import java.io.*;
import java.util.*;

import org.jmlspecs.openjmltest.*;

import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** These tests check running ESC on files in the file system, comparing the
 * output against expected files. These tests are a bit easier to create, since 
 * the file and output do not have to be converted into Strings; however, they
 * are not as easily read, since the content is tucked away in files, rather 
 * than immediately there in the test class.
 * <P>
 * To add a new test:
 * <UL>
 * <LI> create a directory containing the test files as a subdirectory of 
 * 'test'
 * <LI> add a test to this class - typically named similarly to the folder
 * containing the source data
 * </UL>
 */

public class escfileslist extends EscBaseFiles implements Utils {
    
    static double split1 = 0.24;
    static double split2 = 0.40;
    
    /** A list of test suites whose test are excluded from the list generated here */
    public static String[] testsuites = new String[]{
            "org.jmlspecs.openjmltest.testsuites.escfpfiles",
            "org.jmlspecs.openjmltest.testsuites.jmldoctests",
            "org.jmlspecs.openjmltest.testsuites.escfiles",
            "org.jmlspecs.openjmltest.testsuites.escfiles2",
            "org.jmlspecs.openjmltest.testsuites.escfiles3",
            "org.jmlspecs.openjmltest.testsuites.escfilesdemo",
            "org.jmlspecs.openjmltest.testsuites.escfilesmodels",
            "org.jmlspecs.openjmltest.testsuites.escfilesTrace",
            "org.jmlspecs.openjmltest.testsuites.escfpfiles",
            "org.jmlspecs.openjmltest.testsuites.escnonpublic",
            "org.jmlspecs.openjmltest.testsuites.escfeatures",
            "org.jmlspecs.openjmltest.testsuites.primesc1",
            "org.jmlspecs.openjmltest.testsuites.primesc2",
            "org.jmlspecs.openjmltest.testsuites.SFBugs"
    };
    
    /** A routine that computes a List of one-element String arrays, where each of those elements is a 
     * test directory that is not already used in a test by any of the testsuites in the 'testsuites' array above.
     */
    public static java.util.List<String[]> alldata() { 
        return Utils.findTests((File f, String nm) -> f.isDirectory() &&
                (!new java.io.File(f, "skip").exists() && !new java.io.File(f, "run").exists() && !nm.startsWith("rac"))
                && (!new java.io.File(f, "rac").exists() || new java.io.File(f, "expected").exists()) ,
                testsuites);
    }

    /** The name of the test, which is also the name of the directory (in OpenJMLTest/test), filled in from the
     * Parameters array for each individual test.
     */
    String testName;
    
    /** A constructor to allow running listTests() below as a test */
    public escfileslist() {}
    
    /** A constructor used by subclass test suites, along with suitable Parameters */
    protected escfileslist(String testName) {
        this.testName = testName;
    }
    
    /** Common JUnit test setup routine */
    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }
    
    /** An empty options list, to avoid always creating one when needed */
    static String[] noargs = new String[] {};
    
    /** Returns a list of options from the 'testName'/config file, returning an empty list if the file does not exist or contains no options */
    String[] getOptions() {
        String config = "test/"+testName+"/config";
        String args = null;
        if (new java.io.File(config).exists()) {
            try {
                var lines = java.nio.file.Files.readAllLines(java.nio.file.Paths.get(config));
                for (var line: lines) {
                    line = line.strip();
                    if (line.startsWith("EXIT=")) expectedExit = Integer.valueOf(line.substring(5));
                    if (line.startsWith("ARGS+=\"")) args = line.substring(7, line.length()-1).trim();
                    if (line.startsWith("ARGS=\"")) args = line.substring(6, line.length()-1).trim();
                }
            } catch (Exception e) {
                this.out.println("EXCEPTION " + e);
                return noargs;
            }
        }
        return args == null || args.isEmpty() ? noargs : args.split(" ");
    }
    
    /** This test just lists, for information, the tests that will be done by escfileslist1,2,3
        We do not want this test to be inherited and executed by those subclass suites, or at least
        not to emit any output.*/
    @Test
    public void listTests() {
        if (getClass() != escfileslist.class) return;
        for (var d: escfileslist1.data()) this.out.print(d[0] + " ");
        this.out.println(";");
        for (var d: escfileslist2.data()) this.out.print(d[0] + " ");
        this.out.println(";");
        for (var d: escfileslist3.data()) this.out.print(d[0] + " ");
        this.out.println(";");
    }
}
