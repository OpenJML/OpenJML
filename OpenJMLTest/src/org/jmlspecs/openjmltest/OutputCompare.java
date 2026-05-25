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

/** This class compares a sequence of observed (actual) diagnostics to an array of expected diagnostics.
 * The expected set can be a flat array of messages and positions, but it can also include a nested 
 * structure of the special expected diagnostic containers implemented here.
 * 
 * In the array of expected output, sequences of objects are either
 * (a) one of the anyorder, options, oneof, or seq objects defined below
 * (b) one or more sequences that begins with a diagnostic message and is
 * followed by zero to four Integers designating 
 * (i) zero -- a column number of -1
 * (ii) one -- just a column number
 * (iii) two -- column number, preferred position
 * (iv) four -- column number, start position, preferred position, end position
 * 
 * Each thread using this functionality must use a separate instance; one instance can be used
 * (successively within a single thread.
 */
public class OutputCompare {
    
    public boolean print = false; // Set to true for some debugging

    /** This is the base class of special collections of expected diagnostics */
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
    
    /** This special diagnostic matches either by (a) not matching the next diagnostic
     * or (b) having the contained expected objects completely match diagnostic beginning at
     * the current value of diagListPos, and advancing diagListPos by 1.
     */
    protected static class Optional extends Special {
        public Object[] expected;
        public Optional(Object... expected) {
            this.expected = expected;
        }
        public String toString() {
            return toString("optional",expected);
        }
    }
    
    /** This special diagnostic matches by having the diagnostic at diagListPos
     * match one of the objects in the expected array, advancing diagListPos by one if successful.
     */
    protected static class OneOf extends Special {
        public Object[] expected;
        public OneOf(Object ... expected) {
            this.expected = expected;
        }
        public String toString() {
            return toString("oneof",expected);
        }
    }
    
    /** This special diagnostic matches by having the diagnostics beginning at diagListPos
     * match all of the content of the 'expected' array in turn, advancing diagListPos
     * as much as was matched.
     */
    protected static class Seq extends Special {
        public Object[] expected;
        public Seq(Object ... expected) {
            this.expected = expected;
        }
        public String toString() {
            return toString("seq",expected);
        }
    }
    
    /** This special diagnostic matches by having the diagnostics beginning at diagListPos
     * match all of the objects in the expected array, but in any order, advancing diagListPos
     * over all the diagnostics matched.
     */
    protected static class AnyOrder extends Special {
        public Object[] expected;
        public AnyOrder(Object ... expected) {
            this.expected = expected;
        }
        public String toString() {
            return toString("anyorder",expected);
        }
    }

    DiagnosticListenerX<JavaFileObject> collector;
    protected int nDiags;
    protected int diagListPos;
    protected int expectedUsed;
    protected int itemThatDiffers = -1;
    
    /** Compares actual diagnostics against the given list of expected results; this is the 
     * public entry point into this capability. The method either returns without error if the expected objects 
     * completely match all of the observed diagnostics in the diagnostic collector or throws an 
     * AssertionError with a message indicating the first diagnostic that does not match. */
    public int compareResults(Object[] expectedErrors, DiagnosticListenerX<JavaFileObject> collectorp, boolean compareAll) {
        collector = collectorp;
        nDiags = collector.getDiagnostics().size();
        diagListPos = 0;
        if (nDiags > 0) {
            var dd = collector.getDiagnostics().get(diagListPos);
            if (JmlTestSuite.diagnosticToString(dd).contains("is not yet sound")) diagListPos++;
        }
        if (print) System.out.println("START " + expectedErrors.length + " " + nDiags);
        if (!compareResultsX(expectedErrors)) {
            if (diagListPos < nDiags-diagListPos) {
                Diagnostic<? extends JavaFileObject> d = collector.getDiagnostics().get(diagListPos);
                String reason = switch (itemThatDiffers) { case 0 -> " (text)"; case 1 -> " (col)"; case 2 -> " (start)"; case 3 -> " (pos)"; case 4 -> " (end)"; default -> ""; };
                fail("Failed to match diagnostic " + diagListPos + reason+ ": " + JmlTestSuite.diagnosticToString(d));
            } else if (compareAll && expectedUsed < expectedErrors.length) {
                Assert.fail("Fewer errors observed (" + nDiags + ") than expected. First extra: " + expectedErrors[expectedUsed]);
            }
        } else {
            if (diagListPos < nDiags-diagListPos) {
                Diagnostic<? extends JavaFileObject> d = collector.getDiagnostics().get(diagListPos);
                Assert.fail("More errors observed (" + nDiags + ") than expected. First extra: " + JmlTestSuite.diagnosticToString(d));
            } else if (compareAll && expectedUsed < expectedErrors.length) {
                Assert.fail("Fewer errors observed (" + nDiags + ") than expected. First extra: " + expectedErrors[expectedUsed]);
            }
        }
        return expectedUsed;
    }
    
    /** Returns true if the expectedErrors are matched against the diagnostics beginning at diagListPos.
     * If result is false, then the diagnostic at diagListPos does not match the corresponding expected diagnostic
     * If result is true, diagListPos must be advanced and 
     * expectedUsed gives how much of the expectedDiags has been matched 
     *
     **/
    protected boolean compareResultsX(Object ... expectedDiags) {
        int i = 0;
        int initPos = diagListPos;
        while (i < expectedDiags.length) {
            if (print) System.out.println("TEST " + i + " " + expectedDiags.length + " " + diagListPos + " " + nDiags);
            if (!(expectedDiags[i] instanceof Special)) {
                int n = compareDiagnostic(expectedDiags,i);
                if (n > 0) {
                    i += n;
                } else {
                    return false;
                }
            } else if (expectedDiags[i] instanceof AnyOrder ao) {
                if (compareAnyOrder(ao.expected)) {
                    ++i;
                } else {
                    diagListPos = initPos;
                    itemThatDiffers = -1;
                    return false;
                }
            } else if (expectedDiags[i] instanceof OneOf oo) {
                if (compareOneOf(oo.expected)) {
                    ++i;
                } else {
                    diagListPos = initPos;
                    itemThatDiffers = -1;
                    return false;
                }
            } else if (expectedDiags[i] instanceof Optional op) {
                int initPos2 = diagListPos;
                if (!compareResultsX(op.expected)) {
                    diagListPos = initPos2;
                    if (print) System.out.println("COMPARING OPTIONAL NOMATCH");
                }
                ++i;
                // It is OK if the optional did not match
            } else if (expectedDiags[i] instanceof Seq sq) {
                if (compareResultsX(sq.expected)) {
                    ++i;
                } else {
                    diagListPos = initPos;
                    return false;
                }
            }
            expectedUsed = i;
        }
        return true;
    }
    
    /** Compare one expected diagnostic at position diagListPos to expected output beginning at position i in expected.
     * Return 0 if no match; if matched, return the number of array elements matched and advance diagListPos by 1.
     * The match will be of one String and 0-4 Integers.
     */
    protected int compareDiagnostic(Object[] list, int i) {
        int k = i;
        if (diagListPos == nDiags) return 0;
        var diag = collector.getDiagnostics().get(diagListPos);
        String act = JmlTestSuite.noSource(diag).replace('\\','/'); // FIXME - get rid of replace
        String exp = null;
        if (list[i] != null) { // FIXME - is this ever null?
            exp = JmlTestSuite.doReplacements(list[i].toString()).replace('\\','/'); // FIXME - get rid of replace
        }
        if (print) { System.out.println("COMPARING"); System.out.println(act);; System.out.println(exp); }
        
        x: {
            itemThatDiffers = 0;
            if (!act.equals(exp)) {
                if (!exp.contains("Precondition conjunct") || !act.contains("Precondition conjunct")) return 0; // Until fixed, Precondition conjuncts contain temporary variable names that are quite variable
            }
            {
                i++;
                if (i >= list.length) {
                    if (-1 == diag.getColumnNumber()) break x;
                    itemThatDiffers = 1;
                    return 0;
                }
                if (list[i] instanceof Integer i1) {
                    if ((int)i1 != diag.getColumnNumber()) {
                        itemThatDiffers = 1;
                        return 0;
                    }
                } else {
                    if (-1 != diag.getColumnNumber()) return 0;
                    break x;
                }
            }
            {
                i++;
                if (i >= list.length) break x;
                if (list[i] instanceof Integer i1) {
                    if (i+1 < list.length && list[i+1] instanceof Integer) {
                        if ((int)i1 != diag.getStartPosition()) {
                            itemThatDiffers = 2;
                            return 0;
                        }
                    } else {
                        if ((int)i1 != diag.getPosition()) {
                            itemThatDiffers = 3;
                            return 0;
                        }
                    }
                } else break x;
            }
            {
                i++;
                if (i >= list.length) break x;
                if (list[i] instanceof Integer i1) {
                    if ((int)i1 != diag.getPosition()) {
                        itemThatDiffers = 3;
                        return 0;
                    }
                } else break x;
            }
            {
                i++;
                if (i >= list.length) break x;
                if (list[i] instanceof Integer i1) {
                    if ((int)i1 != diag.getEndPosition()) {
                        itemThatDiffers = 4;
                        return 0;
                    }
                    i++;
                } break x;
            }
        }
        if (print) System.out.println("MATCHED AT " + k + " " + i + " " + diagListPos);
        diagListPos++;
        return i-k;
    }

    /** Compares the diagnostic at diagListPos to each of the Special objects in expected,
     * reporting a successful match (true output and diagListPos advancing by one) if one of the expected objects matches;
     * returns false if none of them do
     * @param expected
     * @return
     */
    protected boolean compareOneOf(Object[] expected) {
        // None of expected[i] may be null or empty; all of them must be Special objects
        int i = 0;
        while (i < expected.length) {
            if (compareResultsX(expected[i])) {
                // Matched
                if (print) System.out.println("COMPARING ONEOF MATCHED " + i);
                return true;
            }
            i++;
        }
        if (print) System.out.println("COMPARING ONEOF FAILED");
        return false;
    }


    /** Compares the diagnostics beginning at diagListPos to each of the Special objects in expected,
     * reporting a successful match (true output and diagListPos advancing by expected.length) if all of the expected objects match in some order;
     * returns false if there is no order that matches. */
    protected boolean compareAnyOrder(Object[] expected) {
        if (print) System.out.println("STARTING ANYORDER " + diagListPos + " " + expected.length);
        // None of expected[i] may be null or empty; all of them must be Special objects
        boolean[] used = new boolean[expected.length];
        for (int i=0; i<used.length; ++i) used[i] = false;
        int initPos = diagListPos;
        int toMatch = expected.length;
        more: while (toMatch > 0) {
            for (int i = 0; i < expected.length; ++i) {
                if (used[i]) continue;
                if (compareResultsX(expected[i])) {
                    // Matched
                    if (print) System.out.println("COMPARING ANYORDER MATCHED " + i);
                    used[i] = true;
                    toMatch--;
                    continue more;
                }
            }
            // No remaining entries match
            if (print) System.out.println("COMPARING ANYORDER NOMATCH ");
            diagListPos = initPos;
            return false;
        }
        // everything matched
        if (print) System.out.println("COMPARING ANYORDER ALL MATCHED");
        return true;
    }
    
    public boolean ignoreNotes = true;

    /** Compares the contents of two files, line by line, returning null if the same; returning a String of
     * explanation if they are different.
     */
    public String compareFiles(String expected, String actual) {
        String diff = "";
        try (BufferedReader exp = new BufferedReader(new FileReader(expected)); 
             BufferedReader act = new BufferedReader(new FileReader(actual)))
            {
            
            int line = 0;
            while (true) {
                line++;
                String sexp = exp.readLine();
                if (sexp != null) {
                    sexp = sexp.replace("\r\n", "\n");
                    sexp = JmlTestSuite.doReplacements(sexp);
                    sexp = sexp.replace('\\','/');
                }
                while (true) {
                    String sact = act.readLine();
                    if (sact != null) {
                        sact = sact.replace("\r\n", "\n");
                        sact = sact.replace('\\','/');
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
                        } else if (sexp.contains("Precondition conjunct") && sact.contains("Precondition conjunct")) {
                            // OK
                        } else {         
                            if (sact.startsWith("Note: ") && ignoreNotes) continue;
                            diff = ("Lines differ at " + line + JmlTestSuite.eol)
                                    + ("EXP: " + sexp + JmlTestSuite.eol)
                                    + ("ACT: " + sact + JmlTestSuite.eol);
                            return diff;
                        }
                    } 
                    break;
                }
            }
        } catch (FileNotFoundException e) {
            diff += ("No expected file found: " + expected + JmlTestSuite.eol);
        } catch (Exception e) {
            diff += ("Exception on file comparison" + JmlTestSuite.eol);
        }
        return diff.isEmpty() ? null : diff;
    }
    
    /** Compare the content of 'actualFile' against the files in folder dir that contain the string root within the filename.
     * Emits an AssertionError failure if no file matches; deletes the actualFile if a file does match.
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

    /** Compares the test in 'output' to one or more expected-output files determined by the given directory and root.
     * If there is no match the output text is written to a file with name given by 'actualLocation'.
     */
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
        String term = "\n|(\r(\n)?)"; // any of the kinds of line terminators
        String[] lines = actual.split(term,-1); // -1 so we do not discard empty lines
        String diff = "";
        try (BufferedReader exp = new BufferedReader(new FileReader(expectedFile))) {
            
            boolean same = true;
            int line = 0;
            while (true) {
                line++;
                String sexp = exp.readLine();
                if (sexp == null) {
                    if (line == lines.length) {
                        return diff.isEmpty() ? null : diff;
                    } else {
                        diff = ("More actual input than expected" + JmlTestSuite.eol);
                        return diff;
                    }
                }
                if (line > lines.length) {
                    diff = ("Less actual input than expected" + JmlTestSuite.eol);
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
                        diff = ("Lines differ at " + line + JmlTestSuite.eol)
                            + ("EXP: " + sexp + JmlTestSuite.eol)
                            + ("ACT: " + sact + JmlTestSuite.eol);
                        return diff;
                    }
                }
            }
        } catch (FileNotFoundException e) {
            diff += ("No expected file found: " + expectedFile + JmlTestSuite.eol);
        } catch (Exception e) {
            diff += ("Exception on file comparison" + JmlTestSuite.eol);
        }
        return diff.isEmpty() ? null : diff;
    }
}
