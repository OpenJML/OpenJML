package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.*;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** These tests check running RAC on files in the file system, comparing the
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

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racfileslist extends RacBase {

    @Override
    @Before
    public void setUp() throws Exception {
        setUpForFiles();
        super.setUp();
        ignoreNotes = true;
    }
    
    @Parameters
    static public Collection<String[]> data() {
        try {
            java.util.SortedSet<String> allfiles = new java.util.TreeSet<String>();
            var dir = new File("test");
            for (var f: dir.listFiles()) {
                if (new java.io.File(f, "rac").exists() && !new java.io.File(f, "skip").exists()) {
                    allfiles.add(f.getName());
                }
            }
            for (var f: dir.list((f,s)->s.startsWith("rac"))) {
                allfiles.add(f);
            }
            var racfiles = Class.forName("org.jmlspecs.openjmltest.testsuites.racfiles");
            var racmethods = java.util.Arrays.stream(racfiles.getDeclaredMethods()).filter(method->method.getAnnotationsByType(org.junit.Test.class).length != 0)
                    .map(m->m.getName()).collect(java.util.stream.Collectors.toList());
            var racfiles2 = Class.forName("org.jmlspecs.openjmltest.testsuites.racfilesmodels");
            var racmethods2 = java.util.Arrays.stream(racfiles2.getDeclaredMethods()).filter(method->method.getAnnotationsByType(org.junit.Test.class).length != 0)
                    .map(m->m.getName()).collect(java.util.stream.Collectors.toList());
            System.out.println("RCMETHODS " + racmethods + " " + racmethods2);
            allfiles.removeAll(racmethods);
            allfiles.removeAll(racmethods2);
            System.out.println("REMAINING " + allfiles);
            var tests = allfiles.stream().map(f->new String[] {f}).collect(java.util.stream.Collectors.toList());
            return tests;
        } catch (Exception e) {
            throw new AssertionError("Exception while determining test methods in racfileslist: " + e);
        }
    }
    
    String testName;
    
    public racfileslist(String testName) {
        this.testName = testName;
    }
    
    @Test
    public void test() {
        helpTCF("test/" + testName,"test/" + testName,"T");
    }

}
