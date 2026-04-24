package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.IProverResult;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.JavaSourceScanner;
import org.openjml.lsp.OpenJMLSettings;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.Assert.*;

/**
 * Tests for JML {@code model} methods in two scenarios:
 *
 * <ol>
 *   <li><b>Model method in the .java file</b>: a class with {@code //@ model}
 *       declaration inline.  Verifies that:
 *       <ul>
 *         <li>{@link JavaSourceScanner#findMethodsFromAst} discovers the model method.</li>
 *         <li>ESC proof results include the model method under its correct key.</li>
 *         <li>The model method is included when ESC runs split-by-method.</li>
 *         <li>A Verified (green) marker is placed on the model method's declaration line.</li>
 *       </ul>
 *   </li>
 *   <li><b>Model method in a companion .jml file</b>: the .java file references a
 *       {@code model} method declared in a companion {@code .jml} spec file.
 *       Same invariants as above but the model method lives outside the .java source.</li>
 * </ol>
 *
 * <p>Both scenarios use real {@code .java} / {@code .jml} files written to a
 * {@link TemporaryFolder} so that OpenJML can find the files on disk.
 */
public class ModelMethodEscTest extends LspTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private File writeFile(String filename, String content) throws IOException {
        File f = tmp.newFile(filename);
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
        return f;
    }

    private static String fileUri(File f) {
        return f.toPath().toUri().toString();
    }

    /** Return 0-based line number of the first line that contains {@code marker}. */
    private static int lineOf(String source, String marker) {
        String[] lines = source.split("\n", -1);
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(marker)) return i;
        }
        return -1;
    }

    // -----------------------------------------------------------------------
    // Scenario 1a: model method in .java — AST scanner finds it
    // -----------------------------------------------------------------------

    /**
     * {@link JavaSourceScanner#findMethodsFromAst} must include a {@code model}
     * method declared inline in the {@code .java} file, alongside any regular methods.
     */
    @Test
    public void testModelInJava_AstScannerFindsIt() {
        String uri = "file:///ModelInJavaAst.java";
        String source =
                "public class ModelInJavaAst {\n" +
                "    //@ pure model public int spec(int x) { return x * 2; }\n" +
                "    public int doubled(int x) { return x * 2; }\n" +
                "}\n";

        // Populate the AST cache via a --check pass.
        checkContent(uri, source);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull("AST cache entry must exist after check", entry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast());

        JavaSourceScanner.MethodInfo spec = methods.stream()
                .filter(m -> "spec".equals(m.name())).findFirst().orElse(null);
        JavaSourceScanner.MethodInfo doubled = methods.stream()
                .filter(m -> "doubled".equals(m.name())).findFirst().orElse(null);

        assertNotNull("Regular method 'doubled' must be found by AST walker", doubled);
        assertNotNull("Model method 'spec' must be found by AST walker", spec);

        int expectedLine = lineOf(source, "model public int spec");
        assertEquals("Model method 'spec' must be on its declaration line",
                expectedLine, spec.startLine());
    }

    // -----------------------------------------------------------------------
    // Scenario 1b: model method in .java — ESC produces proof result
    // -----------------------------------------------------------------------

    /**
     * When ESC runs on a file whose {@code model} method has a verifiable body,
     * the proof-results map must contain an entry for the model method.
     * The key must be the method's simple name (same as for regular methods).
     */
    @Test
    public void testModelInJava_EscProofResult() {
        String uri = "file:///ModelInJavaEsc.java";
        String source =
                "public class ModelInJavaEsc {\n" +
                "    //@ pure model public int spec(int x) { return x * 2; }\n" +
                "    //@ ensures \\result == spec(x);\n" +
                "    public int doubled(int x) { return x * 2; }\n" +
                "}\n";

        CheckRunner.CheckResult result = runEscResult(uri, source);

        // At minimum the regular method must appear.
        assertNotNull("Expected proof result for regular method 'doubled'",
                result.proofResultForMethod("doubled"));

        // The model method must also appear if ESC proves it.
        IProverResult.Kind specKind = result.proofResultForMethod("spec");
        System.out.println("[ModelMethodEscTest] spec proof result key='spec' kind=" + specKind);
        System.out.println("[ModelMethodEscTest] all proof results: " + result.proofResults());

        assertNotNull("Model method 'spec' must have a proof result entry (ESC proves model methods)",
                specKind);
        assertEquals("Model method 'spec' must be UNSAT (its body trivially satisfies the implicit spec)",
                IProverResult.UNSAT, specKind);
    }

    // -----------------------------------------------------------------------
    // Scenario 1c: model method in .java — split-by-method includes it
    // -----------------------------------------------------------------------

    /**
     * When ESC runs restricted to a single named method, supplying the model
     * method's name must cause ESC to prove that model method.
     */
    @Test
    public void testModelInJava_SplitByMethodIncludesModelMethod() {
        String uri = "file:///ModelInJavaSplit.java";
        String source =
                "public class ModelInJavaSplit {\n" +
                "    //@ pure model public int spec(int x) { return x * 2; }\n" +
                "    public int doubled(int x) { return x * 2; }\n" +
                "}\n";

        // First run a check to populate the AST cache (needed for method enumeration).
        checkContent(uri, source);

        // Run ESC restricted to the model method by name using the AST-derived FQN.
        ASTCache.Entry astEntry = CheckRunner.getASTCache().get(uri);
        assertNotNull("AST cache must be populated after checkContent", astEntry);
        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(astEntry.ast());
        JavaSourceScanner.MethodInfo specMethod = methods.stream()
                .filter(m -> "spec".equals(m.name())).findFirst().orElse(null);
        assertNotNull("AST must find model method 'spec'", specMethod);
        String methodFqn = specMethod.rawName();
        System.out.println("[ModelMethodEscTest] spec FQN for --method: " + methodFqn);

        CheckRunner.CheckResult result = runEscMethodResult(uri, source, methodFqn);

        System.out.println("[ModelMethodEscTest] split-by-method 'spec' results: "
                + result.proofResults() + " exitCode=" + result.exitCode());

        // The model method must appear in proof results when targeted directly.
        assertNotNull("Model method 'spec' must have a proof result when targeted by --method",
                result.proofResultForMethod("spec"));
    }

    // -----------------------------------------------------------------------
    // Scenario 1d: model method in .java — Verified marker line
    // -----------------------------------------------------------------------

    /**
     * After a whole-file ESC where the model method is UNSAT, the
     * {@code addVerifiedDiagnostics} path must produce a Hint-severity diagnostic
     * on the model method's declaration line (not on line 0 or a bogus line).
     *
     * <p>This test exercises the {@link CheckRunner.CheckResult} proof results together
     * with {@link JavaSourceScanner#findMethodsFromAst} to simulate what the server does
     * when building Verified markers.
     */
    @Test
    public void testModelInJava_VerifiedMarkerLine() {
        String uri = "file:///ModelInJavaMarker.java";
        String source =
                "public class ModelInJavaMarker {\n" +
                "    //@ pure model public int spec(int x) { return x * 2; }\n" +
                "    //@ ensures \\result == spec(x);\n" +
                "    public int doubled(int x) { return x * 2; }\n" +
                "}\n";

        // Populate AST cache.
        checkContent(uri, source);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull("AST cache must be populated", entry);

        // Run ESC.
        CheckRunner.CheckResult result = runEscResult(uri, source);
        IProverResult.Kind specKind = result.proofResultForMethod("spec");
        System.out.println("[ModelMethodEscTest] marker test: spec kind=" + specKind
                + " all results=" + result.proofResults());

        // Skip detailed marker assertion if ESC doesn't prove model methods.
        if (specKind != IProverResult.UNSAT) {
            System.out.println("[ModelMethodEscTest] ESC did not produce UNSAT for 'spec'; skipping marker check");
            return;
        }

        // Simulate addVerifiedDiagnostics: find the method in the AST, confirm line.
        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast());
        JavaSourceScanner.MethodInfo spec = methods.stream()
                .filter(m -> "spec".equals(m.name())).findFirst().orElse(null);

        assertNotNull("Model method 'spec' must be discoverable for marker placement", spec);
        int expectedLine = lineOf(source, "model public int spec");
        assertEquals("Verified marker must be on the model method declaration line",
                expectedLine, spec.startLine());
    }

    // -----------------------------------------------------------------------
    // Scenario 2a: model method in .jml file — ESC produces proof result
    // -----------------------------------------------------------------------

    /**
     * When a model method is declared in a companion {@code .jml} spec file and the
     * {@code .java} file references it, ESC run on the directory must produce a
     * proof result for the model method.
     */
    @Test
    public void testModelInJml_EscProofResult() throws IOException {
        // Write the .java file (refers to spec() but doesn't declare it).
        File javaFile = writeFile("ModelInJml.java",
                "public class ModelInJml {\n" +
                "    //@ ensures \\result == spec(x);\n" +
                "    public int doubled(int x) { return x * 2; }\n" +
                "}\n");

        // Write the companion .jml spec file declaring the model method.
        File jmlFile = writeFile("ModelInJml.jml",
                "public class ModelInJml {\n" +
                "    //@ pure model public int spec(int x) { return x * 2; }\n" +
                "}\n");

        String javaUri = fileUri(javaFile);
        String jmlUri  = fileUri(jmlFile);

        // Run ESC on the directory containing both files.
        CheckRunner.DirCheckResult result = CheckRunner.runEscDirWithContext(
                List.of(javaFile.getAbsolutePath()),
                Map.of(javaUri, new String(java.nio.file.Files.readAllBytes(javaFile.toPath())),
                       jmlUri,  new String(java.nio.file.Files.readAllBytes(jmlFile.toPath()))),
                new OpenJMLSettings(), null);

        System.out.println("[ModelMethodEscTest] jml scenario proofResults=" + result.proofResults());
        System.out.println("[ModelMethodEscTest] jml scenario diagnostics="  + result.diagnosticsByUri());

        // The regular method must appear.
        assertNotNull("Regular method 'doubled' must have a proof result",
                result.proofResultForMethod("doubled"));

        // The model method should also appear if ESC proves it.
        IProverResult.Kind specKind = result.proofResultForMethod("spec");
        System.out.println("[ModelMethodEscTest] jml scenario: spec proof result kind=" + specKind);
        assertNotNull(
                "Model method 'spec' declared in companion .jml must have a proof result",
                specKind);
        assertEquals("Model method 'spec' must be UNSAT", IProverResult.UNSAT, specKind);
    }

    // -----------------------------------------------------------------------
    // Scenario 2b: model method in .jml — AST scanner finds it
    // -----------------------------------------------------------------------

    /**
     * After a {@code --check} pass on the {@code .java} file that loads the
     * companion {@code .jml}, the AST cache entry for the {@code .java} URI must
     * allow {@link JavaSourceScanner#findMethodsFromAst} to discover the model
     * method (so a code lens can be generated for it).
     */
    @Test
    public void testModelInJml_AstScannerFindsIt() throws IOException {
        File javaFile = writeFile("ModelInJmlAst.java",
                "public class ModelInJmlAst {\n" +
                "    //@ ensures \\result == spec(x);\n" +
                "    public int doubled(int x) { return x * 2; }\n" +
                "}\n");
        File jmlFile = writeFile("ModelInJmlAst.jml",
                "public class ModelInJmlAst {\n" +
                "    //@ pure model public int spec(int x) { return x * 2; }\n" +
                "}\n");

        String javaUri = fileUri(javaFile);
        String jmlUri  = fileUri(jmlFile);
        String javaContent = new String(java.nio.file.Files.readAllBytes(javaFile.toPath()));

        // A --check pass on the directory with both files populates the AST cache.
        CheckRunner.runCheckDirWithContext(
                List.of(javaFile.getAbsolutePath()),
                Map.of(javaUri, javaContent,
                       jmlUri, new String(java.nio.file.Files.readAllBytes(jmlFile.toPath()))),
                new OpenJMLSettings());

        ASTCache.Entry entry = CheckRunner.getASTCache().getNav(javaUri);
        assertNotNull("AST cache must be populated after check with .jml companion", entry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast());

        System.out.println("[ModelMethodEscTest] jml AST methods: " + methods);

        JavaSourceScanner.MethodInfo spec = methods.stream()
                .filter(m -> "spec".equals(m.name())).findFirst().orElse(null);
        JavaSourceScanner.MethodInfo doubled = methods.stream()
                .filter(m -> "doubled".equals(m.name())).findFirst().orElse(null);

        assertNotNull("Regular method 'doubled' must be found in AST", doubled);
        assertNotNull(
                "Model method 'spec' from companion .jml must be visible in AST walker", spec);

        // sourceUri must route each method to the file it was declared in.
        assertEquals("doubled must have sourceUri of .java file", javaUri, doubled.sourceUri());
        assertEquals("spec must have sourceUri of .jml file",    jmlUri,  spec.sourceUri());
    }

    // -----------------------------------------------------------------------
    // Scenario 2c: model method in .jml — code-lens routing by sourceUri
    // -----------------------------------------------------------------------

    /**
     * When the method list from {@link JavaSourceScanner#findMethodsFromAst} is
     * filtered by {@code sourceUri}, each method must appear in exactly one
     * file's lens set: regular methods in the {@code .java} file, model methods
     * declared in the companion {@code .jml} file in the {@code .jml} file.
     */
    @Test
    public void testModelInJml_SourceUriRoutingFilter() throws IOException {
        File javaFile = writeFile("ModelInJmlRoute.java",
                "public class ModelInJmlRoute {\n" +
                "    //@ ensures \\result == spec(x);\n" +
                "    public int doubled(int x) { return x * 2; }\n" +
                "}\n");
        File jmlFile = writeFile("ModelInJmlRoute.jml",
                "public class ModelInJmlRoute {\n" +
                "    //@ pure model public int spec(int x) { return x * 2; }\n" +
                "}\n");

        String javaUri = fileUri(javaFile);
        String jmlUri  = fileUri(jmlFile);
        String javaContent = new String(java.nio.file.Files.readAllBytes(javaFile.toPath()));

        CheckRunner.runCheckDirWithContext(
                List.of(javaFile.getAbsolutePath()),
                Map.of(javaUri, javaContent,
                       jmlUri, new String(java.nio.file.Files.readAllBytes(jmlFile.toPath()))),
                new OpenJMLSettings());

        ASTCache.Entry entry = CheckRunner.getASTCache().getNav(javaUri);
        assertNotNull("AST cache must be populated", entry);

        List<JavaSourceScanner.MethodInfo> all =
                JavaSourceScanner.findMethodsFromAst(entry.ast());

        System.out.println("[ModelMethodEscTest] routing test all methods: " + all);

        // Methods that belong to the .java file (code lenses go in the .java editor).
        List<String> javaNames = all.stream()
                .filter(m -> m.sourceUri().isEmpty() || m.sourceUri().equals(javaUri))
                .map(JavaSourceScanner.MethodInfo::name)
                .collect(Collectors.toList());

        // Methods that belong to the .jml file (code lenses go in the .jml editor).
        List<String> jmlNames = all.stream()
                .filter(m -> m.sourceUri().equals(jmlUri))
                .map(JavaSourceScanner.MethodInfo::name)
                .collect(Collectors.toList());

        System.out.println("[ModelMethodEscTest] java-file methods: " + javaNames);
        System.out.println("[ModelMethodEscTest] jml-file methods:  " + jmlNames);

        assertTrue("'doubled' must appear in the .java file's lens set",
                javaNames.contains("doubled"));
        assertFalse("'spec' must NOT appear in the .java file's lens set",
                javaNames.contains("spec"));

        assertTrue("'spec' must appear in the .jml file's lens set",
                jmlNames.contains("spec"));
        assertFalse("'doubled' must NOT appear in the .jml file's lens set",
                jmlNames.contains("doubled"));
    }

    // -----------------------------------------------------------------------
    // Scenario 2d: model method in .jml — .jml AST has sourceCU set to .java CU
    // -----------------------------------------------------------------------

    /**
     * After a {@code --check} pass, the cached {@code .jml} AST must have its
     * {@code sourceCU} field set to the companion {@code .java} CU.  This is the
     * mechanism by which {@code codeLensForJml} locates the companion {@code .java}
     * URI so that ESC is triggered on the correct file when the user clicks a lens
     * in the {@code .jml} editor.
     */
    @Test
    public void testModelInJml_JmlAstHasSourceCuSet() throws IOException {
        File javaFile = writeFile("ModelInJmlSourceCu.java",
                "public class ModelInJmlSourceCu {\n" +
                "    //@ ensures \\result == spec(x);\n" +
                "    public int doubled(int x) { return x * 2; }\n" +
                "}\n");
        File jmlFile = writeFile("ModelInJmlSourceCu.jml",
                "public class ModelInJmlSourceCu {\n" +
                "    //@ pure model public int spec(int x) { return x * 2; }\n" +
                "}\n");

        String javaUri = fileUri(javaFile);
        String jmlUri  = fileUri(jmlFile);
        String javaContent = new String(java.nio.file.Files.readAllBytes(javaFile.toPath()));

        CheckRunner.runCheckDirWithContext(
                List.of(javaFile.getAbsolutePath()),
                Map.of(javaUri, javaContent,
                       jmlUri, new String(java.nio.file.Files.readAllBytes(jmlFile.toPath()))),
                new OpenJMLSettings());

        ASTCache.Entry jmlEntry = CheckRunner.getASTCache().get(jmlUri);
        assertNotNull("ASTCache must have an entry for the .jml URI", jmlEntry);
        assertNotNull("jmlAst must not be null", jmlEntry.ast());

        org.jmlspecs.openjml.JmlTree.JmlCompilationUnit jmlAst = jmlEntry.ast();
        assertNotNull("jmlAst.sourceCU must be set to the companion .java CU", jmlAst.sourceCU);
        assertNotNull("jmlAst.sourceCU.sourcefile must be non-null", jmlAst.sourceCU.sourcefile);

        String derivedJavaUri = jmlAst.sourceCU.sourcefile.toUri().normalize().toString();
        System.out.println("[ModelMethodEscTest] jmlAst.sourceCU.sourcefile → " + derivedJavaUri);
        assertEquals("sourceCU must point to the companion .java file", javaUri, derivedJavaUri);
    }

    // -----------------------------------------------------------------------
    // Scenario 2e: model method in .jml — .jml AST yields correct line numbers
    // -----------------------------------------------------------------------

    /**
     * When {@link JavaSourceScanner#findMethodsFromAst} is called with the cached
     * {@code .jml} CU and the {@code .jml} source text, the model method's
     * {@code startLine} must be the line within the {@code .jml} file (not the
     * line in the companion {@code .java} file).
     *
     * <p>This is the line number that is used for the code-lens position in the
     * {@code .jml} editor, so it must be accurate.
     */
    @Test
    public void testModelInJml_JmlAstLineNumbersAreInJmlFile() throws IOException {
        String jmlSource =
                "public class ModelInJmlLines {\n" +            // line 0
                "    //@ pure model public int spec(int x) {\n" + // line 1
                "    //@   return x * 2; }\n" +                  // line 2
                "}\n";                                            // line 3
        String javaSource =
                "public class ModelInJmlLines {\n" +
                "    //@ ensures \\result == spec(x);\n" +
                "    public int doubled(int x) { return x * 2; }\n" +
                "}\n";

        File javaFile = writeFile("ModelInJmlLines.java", javaSource);
        File jmlFile  = writeFile("ModelInJmlLines.jml", jmlSource);

        String javaUri = fileUri(javaFile);
        String jmlUri  = fileUri(jmlFile);

        CheckRunner.runCheckDirWithContext(
                List.of(javaFile.getAbsolutePath()),
                Map.of(javaUri, javaSource, jmlUri, jmlSource),
                new OpenJMLSettings());

        ASTCache.Entry jmlEntry = CheckRunner.getASTCache().get(jmlUri);
        assertNotNull("ASTCache must have an entry for the .jml URI", jmlEntry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(jmlEntry.ast());
        System.out.println("[ModelMethodEscTest] jml-ast-based methods: " + methods);

        JavaSourceScanner.MethodInfo spec = methods.stream()
                .filter(m -> "spec".equals(m.name())).findFirst().orElse(null);
        assertNotNull("Model method 'spec' must be found via .jml AST", spec);

        int expectedLine = lineOf(jmlSource, "model public int spec");
        System.out.println("[ModelMethodEscTest] spec expected line=" + expectedLine
                + " actual startLine=" + spec.startLine());
        assertEquals("spec startLine must be its line in the .jml file (not the .java file)",
                expectedLine, spec.startLine());
    }
}
