package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;
import org.eclipse.jface.text.source.projection.ProjectionAnnotationModel;
import org.eclipse.swt.widgets.Display;

/**
 * Manages JML annotation folding for a single editor by directly manipulating
 * the editor's {@link ProjectionAnnotationModel}.
 *
 * <p>Works alongside Eclipse JDT's built-in Java folding (class bodies, methods,
 * imports, Javadoc) without replacing it.  Ours are plain {@link ProjectionAnnotation}
 * instances; JDT's are {@code JavaProjectionAnnotation} instances — they coexist
 * in the same model without interfering.
 *
 * <h3>Algorithm</h3>
 * <p>On each document change the full text is scanned character by character.
 * The algorithm is identical to {@code FoldingRangeProvider.fromSource()} in
 * the LSP server:
 * <ol>
 *   <li>Advance to the next fold start — a JML line comment, a JML block
 *       comment, or a text block ({@code """}).  String literals, character
 *       literals, and non-JML Java comments are skipped.</li>
 *   <li>For a text block: record {@code startLine}, skip to {@code """}, emit
 *       a fold if multi-line.  No extension.</li>
 *   <li>For a JML comment: record {@code startLine} and consume the opening
 *       comment.</li>
 *   <li>Extension loop: skip horizontal whitespace; cross one newline (stopping
 *       on a blank line); if the next non-whitespace starts any {@code //} or
 *       {@code /*} comment, consume it and continue.  Program text backs up
 *       {@code endLine} to the previous line and stops.</li>
 *   <li>Emit a fold when {@code endLine > startLine}.</li>
 * </ol>
 *
 * <p>Usage:
 * <pre>
 *   JmlFoldingManager mgr = JmlFoldingManager.install(projectionViewer);
 *   // later, on editor close:
 *   mgr.dispose();
 * </pre>
 */
public class JmlFoldingManager {

    /** JML line-comment marker: {@code //} + optional spaces/keys + {@code @}. */
    private static final Pattern JML_LINE =
            Pattern.compile("^//[ \\t]*([+-][a-zA-Z][a-zA-Z0-9_]*)*@");

    /** JML block-comment start marker: {@code /*} + optional spaces/keys + {@code @}. */
    private static final Pattern JML_BLOCK =
            Pattern.compile("^/\\*[ \\t]*([+-][a-zA-Z][a-zA-Z0-9_]*)*@");

    private final ProjectionAnnotationModel model;
    private final IDocument document;
    /** Our own fold annotations — tracked so we can remove them on the next update. */
    private final List<ProjectionAnnotation> ourAnnotations = new ArrayList<>();
    private final IDocumentListener listener;

    private JmlFoldingManager(ProjectionAnnotationModel model, IDocument document) {
        this.model    = model;
        this.document = document;
        this.listener = new IDocumentListener() {
            @Override public void documentAboutToBeChanged(org.eclipse.jface.text.DocumentEvent e) {}
            @Override public void documentChanged(org.eclipse.jface.text.DocumentEvent e) { scheduleUpdate(); }
        };
        document.addDocumentListener(listener);
        scheduleUpdate();   // initial scan
    }

    /**
     * Installs JML folding on {@code viewer}.  Returns {@code null} if the
     * viewer has no projection annotation model (projection not enabled).
     */
    public static JmlFoldingManager install(
            org.eclipse.jface.text.source.projection.ProjectionViewer viewer) {
        if (viewer == null) return null;
        ProjectionAnnotationModel m = viewer.getProjectionAnnotationModel();
        IDocument doc = viewer.getDocument();
        if (m == null || doc == null) return null;
        return new JmlFoldingManager(m, doc);
    }

    /** Remove the document listener and clear our fold annotations. */
    public void dispose() {
        document.removeDocumentListener(listener);
        if (!ourAnnotations.isEmpty()) {
            Annotation[] toRemove = ourAnnotations.toArray(new Annotation[0]);
            ourAnnotations.clear();
            Display.getDefault().asyncExec(() ->
                    model.modifyAnnotations(toRemove, null, null));
        }
    }

    // -----------------------------------------------------------------------

    private void scheduleUpdate() {
        Display.getDefault().asyncExec(this::updateFolds);
    }

    // NOTE: This algorithm must be kept in sync with FoldingRangeProvider.fromSource()
    // in the OpenJMLlsp server.  Both implement the identical character-scan;
    // any bug fix or behavioral change must be applied to both.
    private void updateFolds() {
        String source;
        try {
            source = document.get();
        } catch (Exception e) {
            return;
        }

        Map<ProjectionAnnotation, Position> toAdd = new LinkedHashMap<>();
        int n    = source.length();
        int pos  = 0;
        int line = 0;

        while (pos < n) {
            // ---- Phase 1: find the next fold start ----
            int[] foldStart = findFoldStart(source, n, pos, line);
            if (foldStart == null) break;

            pos  = foldStart[0];
            line = foldStart[1];
            int type      = foldStart[2];
            int startLine = line;
            int endLine   = startLine;

            if (type == 2) {
                // ---- Text block: fold from """ to closing """ ----
                int[] after = skipTextBlock(source, n, pos, line);
                pos     = after[0];
                line    = after[1];
                endLine = line;
                addRegion(toAdd, startLine, endLine);
                continue;
            }

            // ---- Phase 2: consume the initial JML comment ----
            if (type == 0) {                        // line comment
                pos = skipToNewline(source, n, pos);
            } else {                                 // block comment
                int[] after = skipBlockComment(source, n, pos, line);
                pos     = after[0];
                line    = after[1];
                endLine = line;
            }

            // ---- Phase 3: extension loop ----
            while (true) {
                // Skip trailing spaces/tabs on current line.
                while (pos < n && isSpaceOrTab(source.charAt(pos))) pos++;

                if (pos >= n) break;

                char c = source.charAt(pos);

                if (c == '\n' || c == '\r') {
                    // Consume newline and advance to the next line.
                    if (c == '\r' && pos + 1 < n && source.charAt(pos + 1) == '\n') pos++;
                    pos++; line++;

                    // Skip leading spaces/tabs on the new line.
                    while (pos < n && isSpaceOrTab(source.charAt(pos))) pos++;

                    if (pos >= n) break; // EOF
                    c = source.charAt(pos);
                    if (c == '\n' || c == '\r') break; // blank line: stop

                    // Fall through: c is the first non-space-tab char of the new line.
                }

                // Is c the start of a comment?
                if (c == '/' && pos + 1 < n) {
                    char c2 = source.charAt(pos + 1);
                    if (c2 == '/') {
                        endLine = line;
                        pos = skipToNewline(source, n, pos);
                        continue;
                    }
                    if (c2 == '*') {
                        int[] after = skipBlockComment(source, n, pos, line);
                        endLine = after[1];
                        pos     = after[0];
                        line    = after[1];
                        continue;
                    }
                }

                // Not a comment: program text — fold ends on the previous line.
                endLine = line - 1;
                break;
            }

            addRegion(toAdd, startLine, endLine);
            // Outer loop continues from current pos/line.
        }

        Annotation[] toRemove = ourAnnotations.toArray(new Annotation[0]);
        ourAnnotations.clear();
        ourAnnotations.addAll(toAdd.keySet());
        model.modifyAnnotations(toRemove, toAdd, null);
    }

    // -----------------------------------------------------------------------
    // Helpers — identical in structure to FoldingRangeProvider
    // -----------------------------------------------------------------------

    /**
     * Scans forward from {@code pos} to find the next fold start:
     * a JML line comment (type 0), a JML block comment (type 1), or a text
     * block (type 2).  String literals, character literals, and non-JML Java
     * comments are skipped.
     *
     * @return {@code [pos, line, type]}, or {@code null} if none remains.
     */
    private static int[] findFoldStart(String source, int n, int pos, int line) {
        while (pos < n) {
            char c = source.charAt(pos);
            if (c == '\n') { pos++; line++; continue; }
            if (c == '\r') {
                pos++;
                if (pos < n && source.charAt(pos) == '\n') pos++;
                line++;
                continue;
            }
            if (c == '\'') { pos = skipCharLiteral(source, n, pos); continue; }
            if (c == '"') {
                if (pos + 2 < n && source.charAt(pos + 1) == '"' && source.charAt(pos + 2) == '"')
                    return new int[]{pos, line, 2};   // text block
                pos = skipStringLiteral(source, n, pos);
                continue;
            }
            if (c == '/' && pos + 1 < n) {
                char c2 = source.charAt(pos + 1);
                if (c2 == '/') {
                    if (isJmlLineStart(source, n, pos)) return new int[]{pos, line, 0};
                    pos = skipToNewline(source, n, pos);
                    continue;
                }
                if (c2 == '*') {
                    if (isJmlBlockStart(source, n, pos)) return new int[]{pos, line, 1};
                    int[] after = skipBlockComment(source, n, pos, line);
                    pos = after[0]; line = after[1];
                    continue;
                }
            }
            pos++;
        }
        return null;
    }

    /** Returns true if {@code //} at {@code pos} starts a JML line comment. */
    private static boolean isJmlLineStart(String source, int n, int pos) {
        return JML_LINE.matcher(source).region(pos, n).lookingAt();
    }

    /** Returns true if {@code /*} at {@code pos} starts a JML block comment. */
    private static boolean isJmlBlockStart(String source, int n, int pos) {
        return JML_BLOCK.matcher(source).region(pos, n).lookingAt();
    }

    /** Advances to just before the next newline (or EOF), without consuming it. */
    private static int skipToNewline(String source, int n, int pos) {
        while (pos < n && source.charAt(pos) != '\n' && source.charAt(pos) != '\r') pos++;
        return pos;
    }

    /**
     * Skips a block comment starting at {@code pos} (which must be at
     * {@code /*}).  Handles unclosed comments by returning EOF.
     *
     * @return {@code [newPos, newLine]}.
     */
    private static int[] skipBlockComment(String source, int n, int pos, int line) {
        pos += 2; // skip /*
        while (pos < n) {
            char c = source.charAt(pos);
            if (c == '\n') { pos++; line++; continue; }
            if (c == '\r') { pos++; if (pos < n && source.charAt(pos) == '\n') pos++; line++; continue; }
            if (c == '*' && pos + 1 < n && source.charAt(pos + 1) == '/') {
                return new int[]{pos + 2, line};
            }
            pos++;
        }
        return new int[]{n, line}; // unclosed
    }

    /**
     * Skips a text block starting at {@code pos} (which must be at the opening
     * {@code """}).  Handles unclosed text blocks by returning EOF.
     *
     * @return {@code [newPos, newLine]}.
     */
    private static int[] skipTextBlock(String source, int n, int pos, int line) {
        pos += 3; // skip opening """
        while (pos < n) {
            char c = source.charAt(pos);
            if (c == '\n') { pos++; line++; continue; }
            if (c == '\r') { pos++; if (pos < n && source.charAt(pos) == '\n') pos++; line++; continue; }
            if (c == '"' && pos + 2 < n
                    && source.charAt(pos + 1) == '"' && source.charAt(pos + 2) == '"') {
                return new int[]{pos + 3, line};
            }
            pos++;
        }
        return new int[]{n, line}; // unclosed
    }

    /**
     * Skips a string literal starting at {@code pos} (which must be at
     * {@code "}).  Stops at the closing {@code "}, or at a newline if the
     * literal is unterminated.
     */
    private static int skipStringLiteral(String source, int n, int pos) {
        pos++; // skip opening "
        while (pos < n) {
            char c = source.charAt(pos);
            if (c == '"')              { pos++; break; } // closing quote
            if (c == '\n' || c == '\r') break;           // unterminated
            if (c == '\\')             pos++;            // skip escape character
            pos++;
        }
        return pos;
    }

    /**
     * Skips a character literal starting at {@code pos} (which must be at
     * {@code '}).  Stops at the closing {@code '}, or at a newline if the
     * literal is unterminated.
     */
    private static int skipCharLiteral(String source, int n, int pos) {
        pos++; // skip opening '
        while (pos < n) {
            char c = source.charAt(pos);
            if (c == '\'')             { pos++; break; } // closing quote
            if (c == '\n' || c == '\r') break;           // unterminated
            if (c == '\\')             pos++;            // skip escape character
            pos++;
        }
        return pos;
    }

    private static boolean isSpaceOrTab(char c) { return c == ' ' || c == '\t'; }

    private void addRegion(Map<ProjectionAnnotation, Position> out, int startLine, int endLine) {
        if (endLine <= startLine) return;
        try {
            int startOffset = document.getLineOffset(startLine);
            int endOffset   = document.getLineOffset(endLine) + document.getLineLength(endLine);
            out.put(new ProjectionAnnotation(), new Position(startOffset, endOffset - startOffset));
        } catch (BadLocationException e) {
            // skip
        }
    }
}
