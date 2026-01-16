package org.jmlspecs.openjmltest;
import java.io.File;
import java.io.FilenameFilter;
import java.util.function.BiPredicate;

public interface Utils {
    
    /** Utility method that returns true iff the argument is a directory containing a .java file --
     * meaning that it can be the source for a unit test that runs openjml on the file */
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
    
    /** A routine that computes a List of one-element String arrays, where each of those elements is a 
     * test directory that is not already used in a test by any of the given names of test suites.
     */
    public static java.util.List<String[]> findTests(BiPredicate<File,String> pred, String[] suitesToExclude) { 
        var tests = new java.util.LinkedList<String>();
        var dir = new File("test"); // Presumes the current working directory is OpenJMLTest (parent of 'test')
        for (var f: dir.listFiles()) {
            String nm = f.getName();
            if (pred.test(f,nm)) tests.add(nm);
        }
        for (var suite: suitesToExclude) {
            try {
                var escfiles = Class.forName(suite);
                var methods = java.util.Arrays.stream(escfiles.getDeclaredMethods()).filter(method->method.getAnnotationsByType(org.junit.Test.class).length != 0)
                        .map(m->m.getName()).collect(java.util.stream.Collectors.toList());
                tests.removeAll(methods);
            } catch (Exception e) {
                System.out.println("FAILED TO FIND TESTS IN " + suite + " " + e);
            }
        }
        tests.sort((e1,e2)->e1.compareTo(e2));
        for (var nn: tests) {
            if (!hasJavaFile(new File(dir,nn))) {
                System.out.println("No source files " + nn);
            }
            //System.out.println("ORPHANED " + tests);
        }
        var params = tests.stream().map(f->new String[] {f}).collect(java.util.stream.Collectors.toList());
        return params;
    }
}