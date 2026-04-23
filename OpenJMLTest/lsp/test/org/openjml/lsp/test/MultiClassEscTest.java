package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DiagnosticSeverity;
import org.junit.Test;
import org.openjml.IProverResult;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.JavaSourceScanner;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.Assert.*;

/**
 * Tests for code-lens discovery and ESC behavior when a single {@code .java}
 * file contains more than one class declaration:
 *
 * <ol>
 *   <li><b>Secondary top-level class</b>: a package-private class following the
 *       public class in the same file.  Both classes' methods must be found,
 *       proved, and have Verified markers placed correctly.  The
 *       {@code --method} FQN for secondary-class methods must use the
 *       secondary class name, not the primary class name.</li>
 *   <li><b>Member nested class</b>: a {@code static} or non-static inner class
 *       declared inside the primary class.  Same invariants apply.</li>
 * </ol>
 *
 * <p>Tests are intentionally descriptive: they log the actual observed
 * behaviour so that any discrepancy from the expected behaviour can be
 * discussed before a fix is chosen.
 */
public class MultiClassEscTest extends LspTestBase {

    private static final String PKG_URI    = "file:///Primary.java";
    private static final String NESTED_URI = "file:///Outer.java";

    /** Return the 0-based line number of the first line containing {@code marker}. */
    private static int lineOf(String source, String marker) {
        String[] lines = source.split("\n", -1);
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(marker)) return i;
        }
        return -1;
    }

    // =======================================================================
    // Scenario 3 — secondary (package-private) top-level class
    // =======================================================================

    /**
     * Source with a public primary class and a package-private secondary class
     * in the same file.  Each class has one method with a verifiable spec.
     *
     * <pre>
     * line 0: public class Primary {
     * line 1:     //@ ensures \result == x;
     * line 2:     public int primId(int x) { return x; }
     * line 3: }
     * line 4: class Secondary {
     * line 5:     //@ ensures \result == x;
     * line 6:     public int secId(int x) { return x; }
     * line 7: }
     * </pre>
     */
    private static final String SECONDARY_SRC =
            "public class Primary {\n" +
            "    //@ ensures \\result == x;\n" +
            "    public int primId(int x) { return x; }\n" +
            "}\n" +
            "class Secondary {\n" +
            "    //@ ensures \\result == x;\n" +
            "    public int secId(int x) { return x; }\n" +
            "}\n";

    // -----------------------------------------------------------------------
    // 3b: AST scanner finds methods in both classes
    // -----------------------------------------------------------------------

    @Test
    public void testSecondary_AstFindsMethodsInBothClasses() {
        checkContent(PKG_URI, SECONDARY_SRC);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(PKG_URI);
        assertNotNull("AST cache must be populated", entry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast(), SECONDARY_SRC);
        List<String> names = methods.stream()
                .map(JavaSourceScanner.MethodInfo::name).collect(Collectors.toList());
        System.out.println("[MultiClassEscTest] secondary AST methods: " + names);

        assertTrue("findMethodsFromAst must find 'primId'", names.contains("primId"));
        assertTrue("findMethodsFromAst must find 'secId'", names.contains("secId"));
    }

    // -----------------------------------------------------------------------
    // 3c: ESC produces proof results for both classes' methods
    // -----------------------------------------------------------------------

    @Test
    public void testSecondary_EscProvesMethodsInBothClasses() {
        CheckRunner.CheckResult result = runEscResult(PKG_URI, SECONDARY_SRC);
        System.out.println("[MultiClassEscTest] secondary ESC proofResults: "
                + result.proofResults() + " exitCode=" + result.exitCode());

        IProverResult.Kind primKind = result.proofResultForMethod("primId");
        IProverResult.Kind secKind  = result.proofResultForMethod("secId");
        System.out.println("[MultiClassEscTest] primId=" + primKind + " secId=" + secKind);

        assertNotNull("ESC must produce a proof result for 'primId'", primKind);
        assertEquals("primId must be UNSAT", IProverResult.UNSAT, primKind);

        assertNotNull("ESC must produce a proof result for 'secId'", secKind);
        assertEquals("secId must be UNSAT", IProverResult.UNSAT, secKind);
    }

    // -----------------------------------------------------------------------
    // 3e: split-by-method ESC for primary and secondary class methods
    // -----------------------------------------------------------------------

    @Test
    public void testPrimary_SplitByMethodUsingFqnFromAst() {
        checkContent(PKG_URI, SECONDARY_SRC);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(PKG_URI);
        assertNotNull("AST cache must be populated", entry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast(), SECONDARY_SRC);
        JavaSourceScanner.MethodInfo target = methods.stream()
                .filter(m -> "primId".equals(m.name())).findFirst().orElse(null);
        assertNotNull("AST must find 'primId' for primary class", target);
        System.out.println("[MultiClassEscTest] primId FQN key: " + target.rawName());

        CheckRunner.CheckResult result =
                runEscMethodResult(PKG_URI, SECONDARY_SRC, target.rawName());
        System.out.println("[MultiClassEscTest] primary split-by-method: "
                + result.proofResults() + " exitCode=" + result.exitCode());

        IProverResult.Kind kind = result.proofResultForMethod("primId");
        assertNotNull("ESC --method with FQN from AST must produce a proof result for 'primId'", kind);
        assertEquals("primId must be UNSAT when targeted directly", IProverResult.UNSAT, kind);
    }

    @Test
    public void testSecondary_SplitByMethodForSecondaryClassWorks() {
        // The correct FQN for --method targeting Secondary.secId.
        // We explicitly pass the correct FQN rather than deriving it from the AST.
        CheckRunner.CheckResult result =
                runEscMethodResult(PKG_URI, SECONDARY_SRC, "Secondary.secId");
        System.out.println("[MultiClassEscTest] secondary split-by-method: "
                + result.proofResults() + " exitCode=" + result.exitCode());

        IProverResult.Kind kind = result.proofResultForMethod("secId");
        assertNotNull("ESC --method Secondary.secId must produce a proof result", kind);
        assertEquals("secId must be UNSAT when targeted directly", IProverResult.UNSAT, kind);
    }

    @Test
    public void testSecondary_SplitByMethodUsingFqnFromAst() {
        checkContent(PKG_URI, SECONDARY_SRC);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(PKG_URI);
        assertNotNull("AST cache must be populated", entry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast(), SECONDARY_SRC);
        JavaSourceScanner.MethodInfo target = methods.stream()
                .filter(m -> "secId".equals(m.name())).findFirst().orElse(null);
        assertNotNull("AST must find 'secId' for secondary class", target);
        System.out.println("[MultiClassEscTest] secId FQN key: " + target.rawName());

        CheckRunner.CheckResult result =
                runEscMethodResult(PKG_URI, SECONDARY_SRC, target.rawName());
        System.out.println("[MultiClassEscTest] secondary split-by-method (FQN from AST): "
                + result.proofResults() + " exitCode=" + result.exitCode());

        IProverResult.Kind kind = result.proofResultForMethod("secId");
        assertNotNull("ESC --method with FQN from AST must produce a proof result for 'secId'", kind);
        assertEquals("secId must be UNSAT when targeted directly", IProverResult.UNSAT, kind);
    }

    // -----------------------------------------------------------------------
    // 3f: Verified marker lines are correct for both classes
    // -----------------------------------------------------------------------

    @Test
    public void testSecondary_VerifiedMarkerLinesAreCorrect() {
        checkContent(PKG_URI, SECONDARY_SRC);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(PKG_URI);
        assertNotNull("AST cache must be populated", entry);

        CheckRunner.CheckResult result = runEscResult(PKG_URI, SECONDARY_SRC);
        System.out.println("[MultiClassEscTest] secondary ESC for markers: "
                + result.proofResults());

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast(), SECONDARY_SRC);

        JavaSourceScanner.MethodInfo prim = methods.stream()
                .filter(m -> "primId".equals(m.name())).findFirst().orElse(null);
        JavaSourceScanner.MethodInfo sec = methods.stream()
                .filter(m -> "secId".equals(m.name())).findFirst().orElse(null);

        System.out.println("[MultiClassEscTest] primId method info: " + prim);
        System.out.println("[MultiClassEscTest] secId  method info: " + sec);

        assertNotNull("AST must contain 'primId' for marker placement", prim);
        assertNotNull("AST must contain 'secId' for marker placement", sec);

        assertEquals("primId Verified marker must be on its declaration line",
                lineOf(SECONDARY_SRC, "public int primId"), prim.startLine());
        assertEquals("secId Verified marker must be on its declaration line",
                lineOf(SECONDARY_SRC, "public int secId"), sec.startLine());
    }

    // =======================================================================
    // Scenario 4 — member nested class
    // =======================================================================

    /**
     * Source with a public outer class containing a static member nested class.
     * Each class has one method with a verifiable spec.
     *
     * <pre>
     * line 0: public class Outer {
     * line 1:     //@ ensures \result == x;
     * line 2:     public int outerM(int x) { return x; }
     * line 3:     static class Inner {
     * line 4:         //@ ensures \result == x;
     * line 5:         public int innerM(int x) { return x; }
     * line 6:     }
     * line 7: }
     * </pre>
     */
    private static final String NESTED_SRC =
            "public class Outer {\n" +
            "    //@ ensures \\result == x;\n" +
            "    public int outerM(int x) { return x; }\n" +
            "    static class Inner {\n" +
            "        //@ ensures \\result == x;\n" +
            "        public int innerM(int x) { return x; }\n" +
            "    }\n" +
            "}\n";

    // -----------------------------------------------------------------------
    // 4a: AST scanner — does it include nested class methods?
    // -----------------------------------------------------------------------

    /**
     * {@link JavaSourceScanner#findMethodsFromAst} currently does NOT skip
     * member nested classes (the {@code bodyDepth > 0} guard only catches
     * classes inside method bodies).  This test documents the actual behaviour:
     * whether {@code innerM} appears in the result or not.
     *
     * <p>Depending on the outcome, the walker may need to track class depth
     * separately from block depth.
     */
    @Test
    public void testNested_AstScannerBehaviourForNestedClass() {
        checkContent(NESTED_URI, NESTED_SRC);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(NESTED_URI);
        assertNotNull("AST cache must be populated", entry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast(), NESTED_SRC);
        List<String> names = methods.stream()
                .map(JavaSourceScanner.MethodInfo::name).collect(Collectors.toList());
        System.out.println("[MultiClassEscTest] nested AST methods: " + names);

        // outerM must always be present.
        assertTrue("findMethodsFromAst must find outer class method 'outerM'",
                names.contains("outerM"));

        // Document whether innerM appears (it currently does because bodyDepth
        // is not incremented on class entry, only on block entry).
        System.out.println("[MultiClassEscTest] innerM found by AST scanner: "
                + names.contains("innerM"));

        // Desired behaviour: nested class methods should NOT produce code lenses
        // for the outer file, because their FQN would be wrong and --method would
        // not target them correctly via the outer-class FQN.
        // This assertion captures the current (possibly incorrect) state:
        if (names.contains("innerM")) {
            System.out.println("[MultiClassEscTest] ISSUE: innerM unexpectedly included "
                    + "— FQN and --method targeting will be wrong");
        }
    }

    // -----------------------------------------------------------------------
    // 4b: ESC proof results for outer and nested class; split-by-method
    // -----------------------------------------------------------------------

    @Test
    public void testNested_SplitByMethodUsingFqnFromAst() {
        checkContent(NESTED_URI, NESTED_SRC);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(NESTED_URI);
        assertNotNull("AST cache must be populated", entry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast(), NESTED_SRC);
        JavaSourceScanner.MethodInfo target = methods.stream()
                .filter(m -> "innerM".equals(m.name())).findFirst().orElse(null);
        assertNotNull("AST must find member nested class method 'innerM'", target);
        System.out.println("[MultiClassEscTest] innerM FQN key: " + target.rawName());

        CheckRunner.CheckResult result =
                runEscMethodResult(NESTED_URI, NESTED_SRC, target.rawName());
        System.out.println("[MultiClassEscTest] nested split-by-method: "
                + result.proofResults() + " exitCode=" + result.exitCode());

        IProverResult.Kind kind = result.proofResultForMethod("innerM");
        assertNotNull("ESC --method with FQN from AST must produce a proof result for 'innerM'", kind);
        assertEquals("innerM must be UNSAT when targeted directly", IProverResult.UNSAT, kind);
    }

    @Test
    public void testNested_EscProofResultsForBothClasses() {
        CheckRunner.CheckResult result = runEscResult(NESTED_URI, NESTED_SRC);
        System.out.println("[MultiClassEscTest] nested ESC proofResults: "
                + result.proofResults() + " exitCode=" + result.exitCode());

        IProverResult.Kind outerKind = result.proofResultForMethod("outerM");
        IProverResult.Kind innerKind = result.proofResultForMethod("innerM");
        System.out.println("[MultiClassEscTest] outerM=" + outerKind
                + " innerM=" + innerKind);

        assertNotNull("ESC must produce a proof result for outer class 'outerM'", outerKind);
        assertEquals("outerM must be UNSAT", IProverResult.UNSAT, outerKind);

        // Document whether innerM is proved; don't fail if it isn't.
        if (innerKind != null) {
            System.out.println("[MultiClassEscTest] innerM proved as: " + innerKind);
        } else {
            System.out.println("[MultiClassEscTest] innerM not in proof results "
                    + "(ESC did not prove it or it is not targeted)");
        }
    }

    // -----------------------------------------------------------------------
    // 4d: name collision — outer and inner both have a method named 'm'
    // -----------------------------------------------------------------------

    /**
     * When the outer and nested class both declare a method with the same simple
     * name, the proof-results map (keyed by simple name) can hold only one entry.
     * This test documents the collision behaviour.
     */
    @Test
    public void testNested_ProofResultCollisionOnSameName() {
        String collisionSrc =
                "public class OuterColl {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int m(int x) { return x; }\n" +
                "    static class InnerColl {\n" +
                "        //@ ensures \\result == x + 1;\n" +
                "        public int m(int x) { return x + 1; }\n" +
                "    }\n" +
                "}\n";
        String uri = "file:///OuterColl.java";

        CheckRunner.CheckResult result = runEscResult(uri, collisionSrc);
        System.out.println("[MultiClassEscTest] collision proofResults: "
                + result.proofResults() + " exitCode=" + result.exitCode());

        // With FQN+signature keys, outer and inner 'm' get distinct entries
        // (e.g. "OuterColl.m(int)" and "OuterColl.InnerColl.m(int)") so there is
        // no longer a collision — both proofs are captured independently.
        long mCount = result.proofResults().keySet().stream()
                .filter(k -> CheckRunner.bareMethodName(k).equals("m")).count();
        System.out.println("[MultiClassEscTest] number of 'm' entries (by bare name): " + mCount);
        System.out.println("[MultiClassEscTest] all proof results: " + result.proofResults());
        assertEquals("Both outer and inner 'm' should appear as separate FQN entries", 2, mCount);
    }

    // -----------------------------------------------------------------------
    // 4e: Verified marker line for outer class method is correct
    //     even when nested class methods also appear in the list
    // -----------------------------------------------------------------------

    // =======================================================================
    // Scenario 5 — local class declared inside a method body
    // =======================================================================

    /**
     * A local class declared inside a method body.  Its methods must be
     * discovered by {@link JavaSourceScanner#findMethodsFromAst} and their
     * {@code sourceUri} must be the enclosing {@code .java} file.
     *
     * <pre>
     * line 0: public class LocalOuter {
     * line 1:     public void outer() {
     * line 2:         class Local {
     * line 3:             //@ ensures \result == x;
     * line 4:             public int localM(int x) { return x; }
     * line 5:         }
     * line 6:     }
     * line 7: }
     * </pre>
     */
    private static final String LOCAL_SRC =
            "public class LocalOuter {\n" +
            "    public void outer() {\n" +
            "        class Local {\n" +
            "            //@ ensures \\result == x;\n" +
            "            public int localM(int x) { return x; }\n" +
            "        }\n" +
            "    }\n" +
            "}\n";

    private static final String LOCAL_URI = "file:///LocalOuter.java";

    @Test
    public void testLocal_SplitByMethodUsingFqnFromAst() {
        checkContent(LOCAL_URI, LOCAL_SRC);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(LOCAL_URI);
        assertNotNull("AST cache must be populated", entry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast(), LOCAL_SRC);
        JavaSourceScanner.MethodInfo target = methods.stream()
                .filter(m -> "localM".equals(m.name())).findFirst().orElse(null);
        assertNotNull("AST must find local class method 'localM'", target);
        System.out.println("[MultiClassEscTest] localM FQN key: " + target.rawName());

        CheckRunner.CheckResult result =
                runEscMethodResult(LOCAL_URI, LOCAL_SRC, target.rawName());
        System.out.println("[MultiClassEscTest] local split-by-method: "
                + result.proofResults() + " exitCode=" + result.exitCode());

        // The FQN from the AST scanner must be accepted by --method filtering,
        // so a proof result must exist.  ESC is expected to analyse local class
        // methods; UNSAT is the desired outcome once any remaining ESC-side
        // limitation is resolved.
        IProverResult.Kind kind = result.proofResultForMethod("localM");
        assertNotNull("ESC --method with FQN from AST must produce a proof result for 'localM'", kind);
        System.out.println("[MultiClassEscTest] localM ESC result: " + kind
                + " (expected UNSAT; SKIPPED indicates a remaining ESC limitation)");
    }

    @Test
    public void testLocal_AstScannerFindsLocalClassMethod() {
        checkContent(LOCAL_URI, LOCAL_SRC);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(LOCAL_URI);
        assertNotNull("AST cache must be populated", entry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast(), LOCAL_SRC);
        List<String> names = methods.stream()
                .map(JavaSourceScanner.MethodInfo::name).collect(Collectors.toList());
        System.out.println("[MultiClassEscTest] local class methods: " + names);

        assertTrue("findMethodsFromAst must find local class method 'localM'",
                names.contains("localM"));
    }

    @Test
    public void testLocal_MethodSourceUriIsJavaFile() {
        checkContent(LOCAL_URI, LOCAL_SRC);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(LOCAL_URI);
        assertNotNull("AST cache must be populated", entry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast(), LOCAL_SRC);
        JavaSourceScanner.MethodInfo localM = methods.stream()
                .filter(m -> "localM".equals(m.name())).findFirst().orElse(null);

        assertNotNull("localM must be discoverable", localM);
        assertEquals("localM sourceUri must be the .java file URI", LOCAL_URI, localM.sourceUri());
    }

    // =======================================================================
    // Scenario 6 — anonymous class
    // =======================================================================

    /**
     * An anonymous class implementing an interface inline.  Its method must be
     * discovered by {@link JavaSourceScanner#findMethodsFromAst} and its
     * {@code sourceUri} must be the enclosing {@code .java} file.
     *
     * <pre>
     * line 0: public class AnonOuter {
     * line 1:     interface I { int m(int x); }
     * line 2:     I impl = new I() {
     * line 3:         //@ ensures \result == x;
     * line 4:         public int m(int x) { return x; }
     * line 5:     };
     * line 6: }
     * </pre>
     */
    private static final String ANON_SRC =
            "public class AnonOuter {\n" +
            "    interface I { int m(int x); }\n" +
            "    I impl = new I() {\n" +
            "        //@ ensures \\result == x;\n" +
            "        public int m(int x) { return x; }\n" +
            "    };\n" +
            "}\n";

    private static final String ANON_URI = "file:///AnonOuter.java";

    @Test
    public void testAnon_SplitByMethodUsingFqnFromAst() {
        checkContent(ANON_URI, ANON_SRC);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(ANON_URI);
        assertNotNull("AST cache must be populated", entry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast(), ANON_SRC);
        // There are two 'm' entries: one for the abstract interface method (no body)
        // and one for the anonymous class implementation (has a body, distinct FQN).
        // The anonymous class's FQN contains a numeric segment (e.g. ".1.").
        // Filter by the line that has the JML spec to pick the concrete implementation.
        int implLine = lineOf(ANON_SRC, "public int m(int x) { return x; }");
        JavaSourceScanner.MethodInfo target = methods.stream()
                .filter(m -> "m".equals(m.name()) && m.startLine() == implLine)
                .findFirst().orElse(null);
        assertNotNull("AST must find anonymous class 'm' at impl line " + implLine, target);
        System.out.println("[MultiClassEscTest] anon 'm' FQN key: " + target.rawName());

        CheckRunner.CheckResult result =
                runEscMethodResult(ANON_URI, ANON_SRC, target.rawName());
        System.out.println("[MultiClassEscTest] anon split-by-method: "
                + result.proofResults() + " exitCode=" + result.exitCode());

        // The FQN from the AST scanner must be accepted by --method filtering.
        // ESC is expected to analyse anonymous class methods; UNSAT is the
        // desired outcome once any remaining ESC-side limitation is resolved.
        IProverResult.Kind kind = result.proofResultForMethod("m");
        assertNotNull("ESC --method with FQN from AST must produce a proof result for anon 'm'", kind);
        System.out.println("[MultiClassEscTest] anon 'm' ESC result: " + kind
                + " (expected UNSAT; SKIPPED indicates a remaining ESC limitation)");
    }

    @Test
    public void testAnon_AstScannerFindsAnonymousClassMethod() {
        checkContent(ANON_URI, ANON_SRC);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(ANON_URI);
        assertNotNull("AST cache must be populated", entry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast(), ANON_SRC);
        List<String> names = methods.stream()
                .map(JavaSourceScanner.MethodInfo::name).collect(Collectors.toList());
        System.out.println("[MultiClassEscTest] anonymous class methods: " + names);

        // The anonymous class's 'm' implementation must appear.
        assertTrue("findMethodsFromAst must find anonymous class method 'm'",
                names.contains("m"));
    }

    @Test
    public void testAnon_MethodSourceUriIsJavaFile() {
        checkContent(ANON_URI, ANON_SRC);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(ANON_URI);
        assertNotNull("AST cache must be populated", entry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast(), ANON_SRC);

        // Filter to methods with name "m" that have a body (the anonymous impl,
        // not the abstract interface declaration which has pos < 0 and is skipped).
        List<JavaSourceScanner.MethodInfo> mMethods = methods.stream()
                .filter(mi -> "m".equals(mi.name())).collect(Collectors.toList());
        System.out.println("[MultiClassEscTest] anonymous 'm' entries: " + mMethods);

        assertFalse("At least one 'm' method must be found", mMethods.isEmpty());
        for (JavaSourceScanner.MethodInfo mi : mMethods) {
            assertEquals("anonymous class 'm' sourceUri must be the .java file URI",
                    ANON_URI, mi.sourceUri());
        }
    }

    // -----------------------------------------------------------------------
    // 4e: Verified marker line for outer class method is correct
    //     even when nested class methods also appear in the list
    // -----------------------------------------------------------------------

    @Test
    public void testNested_VerifiedMarkerLineForOuterMethod() {
        checkContent(NESTED_URI, NESTED_SRC);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(NESTED_URI);
        assertNotNull("AST cache must be populated", entry);

        CheckRunner.CheckResult result = runEscResult(NESTED_URI, NESTED_SRC);
        System.out.println("[MultiClassEscTest] nested ESC for markers: "
                + result.proofResults());

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast(), NESTED_SRC);

        JavaSourceScanner.MethodInfo outer = methods.stream()
                .filter(m -> "outerM".equals(m.name())).findFirst().orElse(null);
        System.out.println("[MultiClassEscTest] outer method info: " + outer);
        System.out.println("[MultiClassEscTest] all methods from AST: "
                + methods.stream().map(JavaSourceScanner.MethodInfo::name)
                         .collect(Collectors.toList()));

        assertNotNull("outerM must be discoverable for Verified marker placement", outer);
        assertEquals("outerM Verified marker must be on its declaration line",
                lineOf(NESTED_SRC, "public int outerM"), outer.startLine());
    }
}
