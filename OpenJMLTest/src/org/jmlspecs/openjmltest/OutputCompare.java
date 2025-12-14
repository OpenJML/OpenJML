package org.jmlspecs.openjmltest;

import static org.junit.Assert.*;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticCollector;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjmltest.JmlTestSuite.DiagnosticListenerX;
import org.jmlspecs.openjmltest.OutputCompare.AnyOrder;
import org.jmlspecs.openjmltest.OutputCompare.OneOf;
import org.jmlspecs.openjmltest.OutputCompare.Optional;
import org.jmlspecs.openjmltest.OutputCompare.Seq;
import org.junit.Assert;

public class OutputCompare {

    DiagnosticListenerX<JavaFileObject> collector;

    protected int failureLocation;
    protected String failureString;
    protected int failureCol;
    
    protected int diagListPos;
    
    protected static class Special {
        public String toString(String head, Object[] list) {
            String s = head + "(";
            for (Object o: list) {
                if (o instanceof Object[]) {
                    s = s + toString("",(Object[])o);
                } else {
                    s = s + o + ",\n";
                }
            }
            s = s + ")\n";
            return s;
        }
        
        public boolean compare(Object[] list) { return false; }
    }
    
    protected static class Optional extends Special {
        public Object[] list;
        public Optional(Object... list) {
            this.list = list;
        }
        public String toString() {
            return toString("optional",list);
        }
    }
    
    protected static class OneOf extends Special {
        public Object[] list;
        public OneOf(Object ... list) {
            this.list = list;
        }
        public String toString() {
            return toString("oneof",list);
        }
    }
    
    protected static class Seq extends Special {
        public Object[] list;
        public Seq(Object ... list) {
            this.list = list;
        }
        public String toString() {
            return toString("seq",list);
        }
    }
    
    protected static class AnyOrder extends Special {
        public Object[] list;
        public AnyOrder(Object ... list) {
            this.list = list;
        }
        public String toString() {
            return toString("anyorder",list);
        }
    }


    
    /** Compares actual diagnostics against the given list of expected results */
    public void compareResults(Object[] expectedErrors, DiagnosticListenerX<JavaFileObject> collectorp) {
        collector = collectorp;
        failureLocation = -1;
        failureString = null;
        diagListPos = 0;
        if (!compareResults(expectedErrors)) {
            if (collector.getDiagnostics().size() <= failureLocation) {
                Assert.fail("Too little actual output: " + collector.getDiagnostics().size() + " diagnostics");
            } else {
                Diagnostic<? extends JavaFileObject> d = collector.getDiagnostics().get(failureLocation);
                String act = JmlTestSuite.noSource(d);
                long actualColumn = d.getColumnNumber();
                if (failureString != null) {
                    assertEquals("Error " + failureLocation, failureString, act);
                } else {
                    assertEquals("Error " + failureLocation, failureCol, actualColumn);
                }
            }
        } else {
            Assert.assertEquals("Too little expected output: ",diagListPos,collector.getDiagnostics().size());
        }
    }
    
    /** Compares actual diagnostics, beginning at position j, to given list. The
     * returned result is either the initial value of j, if no match was made,
     * or the value of j advanced over all matching items. If optional is false,
     * then error messages are printed if no match is found.
     */
    protected boolean compareResults(Object expectedErrors) {
        return compareResults(new Object[]{expectedErrors});
    }
    
    protected boolean compareResults(Object[] expectedErrors) {
        int i = 0;
        int initPos = diagListPos;
        while (i < expectedErrors.length) {
            if (expectedErrors[i] == null) { i+=2; continue; }
            if (!(expectedErrors[i] instanceof Special)) {
                if (comparePair(expectedErrors,i,diagListPos,false)) {
                    diagListPos ++;
                    i += 2;
                } else {
                    diagListPos = initPos;
                    return false;
                }
            } else if (expectedErrors[i] instanceof AnyOrder) {
                if (compareAnyOrder(((AnyOrder)expectedErrors[i]).list)) {
                    ++i;
                } else {
                    diagListPos = initPos;
                    return false;
                }
            } else if (expectedErrors[i] instanceof OneOf) {
                if (compareOneOf(((OneOf)expectedErrors[i]).list)) {
                    ++i;
                } else {
                    diagListPos = initPos;
                    return false;
                }
            } else if (expectedErrors[i] instanceof Optional) {
                int initPos2 = diagListPos;
                if (!compareResults(((Optional)expectedErrors[i]).list)) {
                    diagListPos = initPos2;
                }
                ++i;
                // It is OK if the optional did not match
            } else if (expectedErrors[i] instanceof Seq) {
                if (compareResults(((Seq)expectedErrors[i]).list)) {
                    ++i;
                } else {
                    diagListPos = initPos;
                    return false;
                }
            }
        }
        return true;
    }

    protected boolean comparePair(Object[] list, int i, int j, boolean issueErrors) {
        int col = ((Integer)list[i+1]).intValue();
        if (collector.getDiagnostics().size() <= j) {
            failureLocation = j;
            failureString = null;
            return false;
        }
        String act = JmlTestSuite.noSource(collector.getDiagnostics().get(j)).replace('\\','/');
        String exp = null;
        if (list[i] != null) {
            exp = JmlTestSuite.doReplacements(list[i].toString()).replace('\\','/');
        }
        long actualColumn = -1;
        if (!exp.equals(act)) {
            failureLocation = j;
            failureString = exp;
            failureCol = -1;
            if (issueErrors) {
                assertEquals("Error " + j, exp, act);
            }
            return false;
        } else if (col != (actualColumn = Math.abs(collector.getDiagnostics().get(j).getColumnNumber()))) {
            failureLocation = j;
            failureString = null;
            failureCol = col;
            if (issueErrors) {
                assertEquals("Error " + j, col, actualColumn);
            }
            return false;
        } else {
            return true;
        }
    }


    protected boolean compareOneOf(Object[] list) {
        // None of lists[i] may be null or empty
        int i = 0;
        int latestFailure = -2;
        String latestString = null;
        int latestCol = 0;
        while (i < list.length) {
            if (compareResults(list[i])) {
                // Matched
                failureLocation = -1;
                return true;
            }
            i++;
            if (failureLocation > latestFailure) {
                latestFailure = failureLocation;
                latestString = failureString;
                latestCol = failureCol;
            }
        }
        failureLocation = latestFailure;
        failureString = latestString;
        failureCol = latestCol;
        return false;
    }


    protected boolean compareAnyOrder(Object[] list) {
        // None of lists[i] may be null or empty
        boolean[] used = new boolean[list.length];
        for (int i=0; i<used.length; ++i) used[i] = false;
        int initPos = diagListPos;
        int latestFailure = -2;
        String latestString = null;
        int latestCol = 0;
        int toMatch = list.length;
        more: while (toMatch > 0) {
            for (int i = 0; i < list.length; ++i) {
                if (used[i]) continue;
                failureLocation = -3;
                if (compareResults(list[i])) {
                    // Matched
                    used[i] = true;
                    toMatch--;
                    continue more;
                } else {
                    if (failureLocation > latestFailure) {
                        latestFailure = failureLocation;
                        latestString = failureString;
                        latestCol = failureCol;
                    }
                }
            }
            // No options match
            diagListPos = initPos;
            failureLocation = latestFailure;
            failureString = latestString;
            failureCol = latestCol;
            return false;
        }
        return true;
    }
    
    public boolean ignoreNotes = true;

    /** Compares two files, returning null if the same; returning a String of
     * explanation if they are different.
     */
    public String compareFiles(String expected, String actual) {
        BufferedReader exp = null,act = null;
        String diff = "";
        try {
            exp = new BufferedReader(new FileReader(expected));
            act = new BufferedReader(new FileReader(actual));
            
            int line = 0;
            while (true) {
                line++;
                //boolean hasVerify = true;
                String sexp = exp.readLine();
                if (sexp != null) {
                    sexp = sexp.replace("\r\n", "\n");
                    sexp = JmlTestSuite.doReplacements(sexp);
                    sexp = sexp.replace('\\','/');
                    //hasVerify = sexp.contains("verify: ");
                }
                while (true) {
                    String sact = act.readLine();
                    if (sact != null) {
                        sact = sact.replace("\r\n", "\n");
                        sact = sact.replace('\\','/');
                        //if (!hasVerify) sact = sact.replace("verify:", "");
                    }
                    if (sexp == null && sact == null) return diff.isEmpty() ? null : diff;
                    if (sexp != null && sact == null) {
                        diff += ("Less actual output than expected: " + sexp + JmlTestSuite.eol);
                        return diff;
                    }
                    if (sact != null && !sact.equals(sexp)) {
                        if (sact.startsWith("Note: ") && ignoreNotes) continue;
                    }
                    if (sexp == null && sact != null) {
                        diff += ("More actual output than expected: " + actual + JmlTestSuite.eol);
                        return diff;
                    }
                    if (!sexp.equals(sact)) {
                        int k = sexp.indexOf('(');
                        if (k != -1 && sexp.contains("at java.") && sexp.substring(0,k).equals(sact.substring(0,k))) {
                            // OK
                        } else {         
                            if (sact.startsWith("Note: ") && ignoreNotes) continue;
                            diff += ("Lines differ at " + line + JmlTestSuite.eol)
                                    + ("EXP: " + sexp + JmlTestSuite.eol)
                                    + ("ACT: " + sact + JmlTestSuite.eol);
                        }
                    } 
                    break;
                }
            }
        } catch (FileNotFoundException e) {
            diff += ("No expected file found: " + expected + JmlTestSuite.eol);
        } catch (Exception e) {
            diff += ("Exception on file comparison" + JmlTestSuite.eol);
        } finally {
            try {
                if (exp != null) exp.close();
                if (act != null) act.close();
            } catch (Exception e) {}
        }
        return diff.isEmpty() ? null : diff;
    }
    
    /** Compare the content of 'actualFile' against the files dir + "/" + root and then with 1, 2, 3, etc.
     * appended. If none match, then returns the diffs against the last one.
     */
    public void compareFileToMultipleFiles(String actualFile, String dir, String root) {
        String diffs = "";
        for (String f: new File(dir).list()) {
            if (!f.contains(root)) continue;
            diffs = compareFiles(dir + "/" + f, actualFile);
            if (diffs == null) break;
        }
        if (diffs != null) {
            if (diffs.isEmpty()) {
                fail("No expected output file");
            } else {
                System.out.println(diffs);
                fail("Unexpected output: " + diffs);
            }
        } else {
            new File(actualFile).delete();
        }
    }

    public void compareTextToMultipleFiles(String output, String dir, String root, String actualLocation) {
        String diffs = "";
        for (String f: new File(dir).list()) {
            if (!f.contains(root)) continue;
            diffs = compareText(dir + "/" + f,output);
            if (diffs == null) break;
        }
        if (diffs != null) {
            try (BufferedWriter b = new BufferedWriter(new FileWriter(actualLocation));) {
                b.write(output);
            } catch (IOException e) {
                fail("Failure writing output");
            }
            if (diffs.isEmpty()) {
                fail("No expected output file");
            } else {
                System.out.println(diffs);
                fail("Unexpected output");
            }
        } else {
            new File(actualLocation).delete();
        }
    }

    /** Compares a file to an actual String (ignoring difference kinds of 
     * line separators); returns null if they are the same, returns the
     * explanation string if they are different.
     */
    public String compareText(String expectedFile, String actual) {
        //System.out.println("EFILE: " + new File(expectedFile).getAbsolutePath());
        String term = "\n|(\r(\n)?)"; // any of the kinds of line terminators
        BufferedReader exp = null;
        String[] lines = actual.split(term,-1); // -1 so we do not discard empty lines
        String diff = "";
        try {
            exp = new BufferedReader(new FileReader(expectedFile));
            
            boolean same = true;
            int line = 0;
            while (true) {
                line++;
                String sexp = exp.readLine();
                if (sexp == null) {
                    if (line == lines.length) return diff.isEmpty() ? null : diff;

                    else {
                        diff += ("More actual input than expected" + JmlTestSuite.eol);
                        return diff;
                    }
                }
                if (line > lines.length) {
                    diff += ("Less actual input than expected" + JmlTestSuite.eol);
                    return diff;
                }
                sexp = JmlTestSuite.doReplacements(sexp);
                String sact = lines[line-1];
                if (sexp.equals(sact)) {
                    // OK
                } else if (sexp.replace('\\','/').equals(sact.replace('\\','/'))) {
                    // OK
                } else {
                    int k = sexp.indexOf('(');
                    if (k != -1 && sexp.contains("at ") && sexp.substring(0,k).equals(sact.substring(0,k))) {
                        // OK
                    } else {         
                        diff += ("Lines differ at " + line + JmlTestSuite.eol)
                            + ("EXP: " + sexp + JmlTestSuite.eol)
                            + ("ACT: " + sact + JmlTestSuite.eol);
                    }
                }
            }
        } catch (FileNotFoundException e) {
            diff += ("No expected file found: " + expectedFile + JmlTestSuite.eol);
        } catch (Exception e) {
            diff += ("Exception on file comparison" + JmlTestSuite.eol);
        } finally {
            try {
                if (exp != null) exp.close();
            } catch (Exception e) {}
        }
        return diff.isEmpty() ? null : diff;
    }

}
