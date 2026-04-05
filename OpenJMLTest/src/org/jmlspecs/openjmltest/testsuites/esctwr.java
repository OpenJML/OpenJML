package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.assertFalse;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.MockJavaFileObject;
import org.openjml.runners.ParameterizedWithNames;

import com.sun.tools.javac.util.List;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class esctwr extends EscBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--check-feasibility=none");
        expectedExit = 0;
    }

    /**
     * Compiles the given source and asserts that no internal JML/OpenJML error
     * occurred.  Accepts a clean exit (0) or the known missing-prover message
     * when z3 is unavailable in the test environment.
     */
    private void assertNoInternalError(String filename, String source) throws Exception {
        assertNoInternalError(filename, source, null);
    }

    private void assertNoInternalError(String filename, String source, String method) throws Exception {
        if (method != null) addOptions("--method=" + method);
        JavaFileObject f = new MockJavaFileObject(filename, source);
        main.compile(new String[]{}, List.of(f));
        String diags = diagnosticsToString(collector.getDiagnostics());
        assertFalse("Did not expect a catastrophic internal error:\n" + diags,
                diags.contains("A catastrophic JML internal error occurred"));
        assertFalse("Did not expect an internal JML error:\n" + diags,
                diags.contains("An internal JML error occurred"));
        assertFalse("Did not expect a ClassCastException (JCIdent to JCVariableDecl):\n" + diags,
                diags.contains("JCIdent cannot be cast to") && diags.contains("JCVariableDecl"));
        assertFalse("Did not expect a ClassCastException (TypeVariableSymbol to ClassSymbol):\n" + diags,
                diags.contains("TypeVariableSymbol cannot be cast to") && diags.contains("ClassSymbol"));
        assertFalse("Did not expect a ClassCastException (JCFieldAccess to JCVariableDecl):\n" + diags,
                diags.contains("JCFieldAccess cannot be cast to") && diags.contains("JCVariableDecl"));
        // We do NOT assert on exit code: verification warnings (ExceptionList,
        // InvariantEntrance, etc.) produce a non-zero exit, which is fine.
        // The point of these tests is that no ClassCastException / internal
        // error occurs — normal verification output is acceptable.
    }

    // -----------------------------------------------------------------------
    //  Bug A: expression resource (JCIdent) — Java 9+ try-with-resources
    //  Previously crashed with: JCIdent cannot be cast to JCVariableDecl
    // -----------------------------------------------------------------------

    /** Expression resource with a concrete AutoCloseable type. */
    @Test
    public void testTwrExpressionResource() throws Exception {
        assertNoInternalError("A.java", """
                import java.io.*;
                class A {
                    void process(BufferedReader br) throws IOException {
                        try (br) {
                            System.out.println(br.readLine());
                        }
                    }
                }
                """);
    }

    /** Expression resource with a concrete type implementing Closeable. */
    @Test
    public void testTwrExpressionResourceCloseable() throws Exception {
        assertNoInternalError("A.java", """
                import java.io.*;
                class A {
                    void process(InputStream in) throws IOException {
                        try (in) {
                            in.read();
                        }
                    }
                }
                """);
    }

    /** Multiple expression resources in one try statement. */
    @Test
    public void testTwrMultipleExpressionResources() throws Exception {
        assertNoInternalError("A.java", """
                import java.io.*;
                class A {
                    void copy(InputStream in, OutputStream out) throws IOException {
                        try (in; out) {
                            out.write(in.read());
                        }
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    //  Bug B: generic resource type (TypeVariableSymbol)
    //  Previously crashed with: TypeVariableSymbol cannot be cast to ClassSymbol
    // -----------------------------------------------------------------------

    /** Traditional declaration with a Closeable-bounded type variable. */
    @Test
    public void testTwrGenericResourceCloseable() throws Exception {
        assertNoInternalError("A.java", """
                import java.io.*;
                class A {
                    static <R extends Closeable> void use(R resource) throws IOException {
                        try (R r = resource) {
                            System.out.println(r);
                        }
                    }
                }
                """);
    }

    /** Traditional declaration with an AutoCloseable-bounded type variable. */
    @Test
    public void testTwrGenericResourceAutoCloseable() throws Exception {
        assertNoInternalError("A.java", """
                class A {
                    static <R extends AutoCloseable> void use(R resource) throws Exception {
                        try (R r = resource) {
                            System.out.println(r);
                        }
                    }
                }
                """);
    }

    /** Multiple type parameters, one is the resource type. */
    @Test
    public void testTwrGenericResourceMultipleTypeParams() throws Exception {
        assertNoInternalError("A.java", """
                import java.io.*;
                class A {
                    static <T, R extends Closeable> void process(T data, R resource) throws IOException {
                        try (R r = resource) {
                            System.out.println(data);
                        }
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    //  Bug A + Bug B combined: expression resource with generic type
    //  Triggers both bugs simultaneously
    // -----------------------------------------------------------------------

    /** Expression resource with a generic type variable. */
    @Test
    public void testTwrExpressionGenericResource() throws Exception {
        assertNoInternalError("A.java", """
                import java.io.*;
                class A {
                    static <R extends Closeable> void use(R resource) throws IOException {
                        try (resource) {
                            System.out.println(resource);
                        }
                    }
                }
                """);
    }

    /** Expression resource with AutoCloseable-bounded generic type. */
    @Test
    public void testTwrExpressionGenericAutoCloseable() throws Exception {
        assertNoInternalError("A.java", """
                class A {
                    static <R extends AutoCloseable> void use(R resource) throws Exception {
                        try (resource) {
                            System.out.println(resource);
                        }
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    //  Field access resources (JCFieldAccess variant of Bug A)
    // -----------------------------------------------------------------------

    /** Expression resource via field access: this.resource. */
    @Test
    public void testTwrFieldAccessResource() throws Exception {
        assertNoInternalError("A.java", """
                import java.io.*;
                class A {
                    final InputStream stream;
                    A(InputStream s) { this.stream = s; }
                    void process() throws IOException {
                        try (this.stream) {
                            stream.read();
                        }
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    //  Mixed resources: declaration + expression in one try
    // -----------------------------------------------------------------------

    /** Mixed declaration and expression resources in one try statement. */
    @Test
    public void testTwrMixedResources() throws Exception {
        assertNoInternalError("A.java", """
                import java.io.*;
                class A {
                    void process(InputStream existing) throws IOException {
                        try (existing;
                             BufferedReader br = new BufferedReader(new InputStreamReader(existing))) {
                            System.out.println(br.readLine());
                        }
                    }
                }
                """);
    }

    /** Mixed expression and generic declaration resources. */
    @Test
    public void testTwrMixedGenericResources() throws Exception {
        assertNoInternalError("A.java", """
                import java.io.*;
                class A {
                    static <R extends Closeable> void process(R resource, InputStream extra) throws IOException {
                        try (R r = resource;
                             extra) {
                            System.out.println(r);
                        }
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    //  Regression: traditional try-with-resources (should still work)
    // -----------------------------------------------------------------------

    /** Traditional try-with-resources with a concrete type. */
    @Test
    public void testTwrTraditionalResource() throws Exception {
        assertNoInternalError("A.java", """
                import java.io.*;
                class A {
                    void process(String path) throws IOException {
                        try (BufferedReader br = new BufferedReader(new FileReader(path))) {
                            System.out.println(br.readLine());
                        }
                    }
                }
                """);
    }

    /** Traditional try-with-resources with multiple resources. */
    @Test
    public void testTwrTraditionalMultipleResources() throws Exception {
        assertNoInternalError("A.java", """
                import java.io.*;
                class A {
                    void copy(String src, String dst) throws IOException {
                        try (FileInputStream in = new FileInputStream(src);
                             FileOutputStream out = new FileOutputStream(dst)) {
                            out.write(in.read());
                        }
                    }
                }
                """);
    }

    /** Traditional try-with-resources with inner AutoCloseable class. */
    @Test
    public void testTwrTraditionalAutoCloseable() throws Exception {
        assertNoInternalError("A.java", """
                class A {
                    static class MyResource implements AutoCloseable {
                        public void close() {}
                    }
                    void use() {
                        try (MyResource r = new MyResource()) {
                            System.out.println(r);
                        }
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    //  Edge cases
    // -----------------------------------------------------------------------

    /** Try-with-resources inside a try-catch. */
    @Test
    public void testTwrNestedInTryCatch() throws Exception {
        assertNoInternalError("A.java", """
                import java.io.*;
                class A {
                    void process(InputStream in) {
                        try {
                            try (in) {
                                in.read();
                            }
                        } catch (IOException e) {
                            // handled
                        }
                    }
                }
                """);
    }

    /** Nested try-with-resources. */
    @Test
    public void testTwrNestedTryWithResources() throws Exception {
        assertNoInternalError("A.java", """
                import java.io.*;
                class A {
                    void process(String path) throws IOException {
                        try (FileInputStream fis = new FileInputStream(path)) {
                            try (BufferedInputStream bis = new BufferedInputStream(fis)) {
                                bis.read();
                            }
                        }
                    }
                }
                """);
    }

    // NOTE: intersection type bounds (e.g. <R extends Closeable & Serializable>)
    // trigger a pre-existing "Mismatched decls" bug in JmlAttr.visitTypeParameter,
    // which is unrelated to the try-with-resources fixes.  Intersection bound
    // tests are intentionally omitted.
}
