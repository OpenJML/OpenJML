package org.openjml.lsp.test;

import org.junit.Test;
import org.openjml.lsp.DiagnosticConverter;

import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;

import static org.junit.Assert.*;

/**
 * Unit tests for {@link DiagnosticConverter}.
 *
 * <p>Focuses on the two pure utility methods:
 * <ul>
 *   <li>{@link DiagnosticConverter#buildLineStartOffsets} — hand-coded CRLF/CR/LF
 *       logic; errors here produce wrong line numbers in all diagnostics.</li>
 *   <li>{@link DiagnosticConverter#matchesSourcePath} — basename comparison used
 *       to filter diagnostics to the correct file.</li>
 * </ul>
 */
public class DiagnosticConverterTest {

    // -----------------------------------------------------------------------
    // buildLineStartOffsets
    // -----------------------------------------------------------------------

    @Test
    public void testLineOffsetsEmptyString() {
        int[] offsets = DiagnosticConverter.buildLineStartOffsets("");
        assertEquals("Empty content: one line, offset 0", 1, offsets.length);
        assertEquals(0, offsets[0]);
    }

    @Test
    public void testLineOffsetsSingleLineNoNewline() {
        // "hello" — one line, no newline at end
        int[] offsets = DiagnosticConverter.buildLineStartOffsets("hello");
        assertEquals(1, offsets.length);
        assertEquals(0, offsets[0]);
    }

    @Test
    public void testLineOffsetsUnixLf() {
        // "a\nb\nc" — 3 lines
        int[] offsets = DiagnosticConverter.buildLineStartOffsets("a\nb\nc");
        assertEquals(3, offsets.length);
        assertEquals(0, offsets[0]);
        assertEquals(2, offsets[1]);  // 'b' starts at offset 2
        assertEquals(4, offsets[2]);  // 'c' starts at offset 4
    }

    @Test
    public void testLineOffsetsCrLf() {
        // "a\r\nb\r\nc" — CRLF pairs each count as one line break
        int[] offsets = DiagnosticConverter.buildLineStartOffsets("a\r\nb\r\nc");
        assertEquals(3, offsets.length);
        assertEquals(0, offsets[0]);
        assertEquals(3, offsets[1]);  // 'b' starts at offset 3 (past "a\r\n")
        assertEquals(6, offsets[2]);  // 'c' starts at offset 6
    }

    @Test
    public void testLineOffsetsCrOnly() {
        // "a\rb\rc" — bare CR (old Mac); each CR counts as a line break
        int[] offsets = DiagnosticConverter.buildLineStartOffsets("a\rb\rc");
        assertEquals(3, offsets.length);
        assertEquals(0, offsets[0]);
        assertEquals(2, offsets[1]);
        assertEquals(4, offsets[2]);
    }

    @Test
    public void testLineOffsetsMixedEndings() {
        // "a\nb\r\nc\rd" — three different line endings in one file
        int[] offsets = DiagnosticConverter.buildLineStartOffsets("a\nb\r\nc\rd");
        assertEquals(4, offsets.length);
        assertEquals(0, offsets[0]);
        assertEquals(2, offsets[1]);  // after "a\n"
        assertEquals(5, offsets[2]);  // after "b\r\n"
        assertEquals(7, offsets[3]);  // after "c\r"
    }

    @Test
    public void testLineOffsetsTrailingNewline() {
        // "a\nb\n" — trailing newline creates an extra (empty) line entry
        int[] offsets = DiagnosticConverter.buildLineStartOffsets("a\nb\n");
        assertEquals(3, offsets.length);
        assertEquals(0, offsets[0]);
        assertEquals(2, offsets[1]);
        assertEquals(4, offsets[2]);
    }

    // -----------------------------------------------------------------------
    // matchesSourcePath
    // -----------------------------------------------------------------------

    /** When sourcePath is null the filter is vacuously true. */
    @Test
    public void testMatchesSourcePathNullSourcePath() {
        Diagnostic<? extends JavaFileObject> d = makeDiagnostic("Foo.java");
        assertTrue(DiagnosticConverter.matchesSourcePath(d, null));
    }

    /** When the diagnostic has no source, any path matches (file-level diagnostic). */
    @Test
    public void testMatchesSourcePathNullDiagnosticSource() {
        Diagnostic<? extends JavaFileObject> d = makeDiagnostic(null);
        assertTrue(DiagnosticConverter.matchesSourcePath(d, "/some/path/Foo.java"));
    }

    /** Same basename in a different directory must match. */
    @Test
    public void testMatchesSourcePathSameBasename() {
        Diagnostic<? extends JavaFileObject> d = makeDiagnostic("/build/tmp/Foo.java");
        assertTrue(DiagnosticConverter.matchesSourcePath(d, "/project/src/Foo.java"));
    }

    /** Different basename must not match. */
    @Test
    public void testMatchesSourcePathDifferentBasename() {
        Diagnostic<? extends JavaFileObject> d = makeDiagnostic("/src/Bar.java");
        assertFalse(DiagnosticConverter.matchesSourcePath(d, "/src/Foo.java"));
    }

    /** Basename comparison must work for Windows-style backslash paths. */
    @Test
    public void testMatchesSourcePathWindowsPath() {
        Diagnostic<? extends JavaFileObject> d = makeDiagnostic("C:\\build\\Foo.java");
        assertTrue(DiagnosticConverter.matchesSourcePath(d, "C:\\src\\Foo.java"));
    }

    // -----------------------------------------------------------------------
    // Helper: make a minimal diagnostic with a given source name
    // -----------------------------------------------------------------------

    private static Diagnostic<JavaFileObject> makeDiagnostic(String sourceName) {
        return new Diagnostic<>() {
            @Override public Kind getKind()       { return Kind.ERROR; }
            @Override public JavaFileObject getSource() {
                if (sourceName == null) return null;
                return new javax.tools.SimpleJavaFileObject(
                        java.net.URI.create("file:///" + sourceName.replace('\\', '/')),
                        JavaFileObject.Kind.SOURCE) {
                    @Override public String getName() { return sourceName; }
                };
            }
            @Override public long getPosition()      { return Diagnostic.NOPOS; }
            @Override public long getStartPosition() { return Diagnostic.NOPOS; }
            @Override public long getEndPosition()   { return Diagnostic.NOPOS; }
            @Override public long getLineNumber()    { return Diagnostic.NOPOS; }
            @Override public long getColumnNumber()  { return Diagnostic.NOPOS; }
            @Override public String getCode()        { return ""; }
            @Override public String getMessage(java.util.Locale l) { return "test"; }
        };
    }
}
