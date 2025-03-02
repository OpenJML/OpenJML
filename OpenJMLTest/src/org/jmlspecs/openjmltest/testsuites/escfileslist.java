package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.Assume;
import org.junit.FixMethodOrder;
import org.junit.Ignore;
import org.junit.Test;
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

public class escfileslist extends EscBaseFiles {
    
    public static String[] testsuites = new String[]{
            "org.jmlspecs.openjmltest.testsuites.escfpfiles",
            "org.jmlspecs.openjmltest.testsuites.jmldoctests",
            "org.jmlspecs.openjmltest.testsuites.escfiles",
            "org.jmlspecs.openjmltest.testsuites.escfiles2",
            "org.jmlspecs.openjmltest.testsuites.escfilesdemo",
            "org.jmlspecs.openjmltest.testsuites.escfilesmodels",
            "org.jmlspecs.openjmltest.testsuites.escfilesTrace",
            "org.jmlspecs.openjmltest.testsuites.compiler",
            "org.jmlspecs.openjmltest.testsuites.SFBugs"
    };
    
    static boolean hasJavaFile(File d) {
        for (var f: d.listFiles()) {
            if (f.isDirectory()) {
                if (hasJavaFile(f)) return true;
            } else {
                if (f.getName().endsWith(".java")) return true;
            }
        }
        return false;
    }
    
    public static java.util.List<String[]> alldata() { 
        var tests = new java.util.LinkedList<String>();
        var namedTests = System.getenv("NAMEDTEST");
        if (namedTests != null) {
            for (var s: namedTests.trim().split(" ")) {
                var ss = s.trim(); if (!ss.isEmpty()) tests.add(ss);
            }
        } else {
            var dir = new File("test");
            for (var f: dir.listFiles()) {
                String nm = f.getName();
                if (!f.isDirectory()) continue;
                if (!new java.io.File(f, "skip").exists() && !new java.io.File(f, "run").exists() && !nm.startsWith("rac")) {
                    if (!new java.io.File(f, "rac").exists() || new java.io.File(f, "expected").exists()) {
                        tests.add(nm);
                    }
                }
            }
            for (var suite: testsuites) {
                try {
                    var escfiles = Class.forName(suite);
                    var methods = java.util.Arrays.stream(escfiles.getDeclaredMethods()).filter(method->method.getAnnotationsByType(org.junit.Test.class).length != 0)
                            .map(m->m.getName()).collect(java.util.stream.Collectors.toList());
                    tests.removeAll(methods);
                } catch (Exception e) {
                    System.out.println("FAILED TO FIND TESTS IN " + suite);
                }
            }
            tests.sort((e1,e2)->e1.compareTo(e2));
            for (var nn: tests) {
                if (!hasJavaFile(new File(dir,nn))) {
                    System.out.println("No source files " + nn);
                }
            }
            System.out.println("REMAINING " + tests);
        }
        var params = tests.stream().map(f->new String[] {f}).collect(java.util.stream.Collectors.toList());
        return params;
    }

    String testName;
    
    public escfileslist(String testName) {
        this.testName = testName;
    }
    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }
    
    static String[] noargs = new String[] {};
    
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
                System.out.println("EXCEPTION " + e);
                return noargs;
            }
        }
        return args == null ? noargs : args.split(" ");
    }
    
}
