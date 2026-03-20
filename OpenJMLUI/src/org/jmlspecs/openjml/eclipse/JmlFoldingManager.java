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
 * <p>Usage:
 * <pre>
 *   JmlFoldingManager mgr = JmlFoldingManager.install(projectionViewer);
 *   // later, on editor close:
 *   mgr.dispose();
 * </pre>
 */
public class JmlFoldingManager {

    /** JML line comment: {@code //@}, {@code // @}, {@code //+ESC@}, etc. */
    private static final Pattern JML_LINE =
            Pattern.compile("^[ \\t]*//[ \\t]*([+-][a-zA-Z][a-zA-Z0-9_]*)*@");

    /** JML block comment start anchored to line beginning: {@code /*@}, {@code /* @}, etc. */
    private static final Pattern JML_BLOCK_START =
            Pattern.compile("^[ \\t]*/\\*[ \\t]*([+-][a-zA-Z][a-zA-Z0-9_]*)*@");

    /** Same pattern unanchored — used to find a new JML block opening mid-line. */
    private static final Pattern JML_BLOCK_OPEN =
            Pattern.compile("/\\*[ \\t]*([+-][a-zA-Z][a-zA-Z0-9_]*)*@");

    private final ProjectionAnnotationModel model;
    private final IDocument document;
    /** Our own fold annotations — tracked so we can remove them on the next update. */
    private final List<ProjectionAnnotation> ourAnnotations = new ArrayList<>();
    private final IDocumentListener listener;

    private JmlFoldingManager(ProjectionAnnotationModel model, IDocument document) {
        this.model    = model;
        this.document = document;
        this.listener = new IDocumentListener() {
            @Override public void documentAboutToBeChanged(
                    org.eclipse.jface.text.DocumentEvent e) {}
            @Override public void documentChanged(
                    org.eclipse.jface.text.DocumentEvent e) { scheduleUpdate(); }
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

    private void updateFolds() {
        String content;
        try {
            content = document.get();
        } catch (Exception e) {
            return;
        }

        String[] lines = content.split("\\r?\\n", -1);
        Map<ProjectionAnnotation, Position> toAdd = new LinkedHashMap<>();

        int regionStart = -1, regionEnd = -1;
        boolean inBlock = false;

        for (int i = 0; i < lines.length; i++) {
            String line = lines[i];
            if (inBlock) {
                regionEnd = i;
                inBlock = scanBlockThroughLine(line);
            } else if (JML_LINE.matcher(line).find()) {
                if (regionStart == -1) regionStart = i;
                regionEnd = i;
            } else if (JML_BLOCK_START.matcher(line).find()) {
                if (regionStart == -1) regionStart = i;
                regionEnd = i;
                inBlock = scanBlockThroughLine(line);
            } else if (regionStart != -1) {
                addRegion(toAdd, regionStart, regionEnd);
                regionStart = -1;
                regionEnd   = -1;
            }
        }
        if (regionStart != -1) addRegion(toAdd, regionStart, regionEnd);

        Annotation[] toRemove = ourAnnotations.toArray(new Annotation[0]);
        ourAnnotations.clear();
        ourAnnotations.addAll(toAdd.keySet());
        model.modifyAnnotations(toRemove, toAdd, null);
    }

    /**
     * Scans {@code line} for {@code */} … {@code /*@} pairs, starting from the
     * assumption that we are inside a JML block comment.  Returns {@code true}
     * if we are still inside a (possibly different) block comment at the end of
     * the line.
     */
    private boolean scanBlockThroughLine(String line) {
        boolean inBlock = true;
        String rest = line;
        int k = 0;
        while (inBlock && (k=rest.indexOf("*/", k)) >= 0) {
            inBlock = false;
            k = k + 2;
            if (JML_BLOCK_OPEN.matcher(rest).find(k)) {
                inBlock = true;
                k = k + 2;
            }
        }
        return inBlock;
    }

    private void addRegion(Map<ProjectionAnnotation, Position> out, int startLine, int endLine) {
        if (startLine < 0 || endLine <= startLine) return; // No one-line folding regions; startLine should never be negative
        try {
            int startOffset = document.getLineOffset(startLine);
            int endOffset   = document.getLineOffset(endLine) + document.getLineLength(endLine);
            out.put(new ProjectionAnnotation(), new Position(startOffset, endOffset - startOffset));
        } catch (BadLocationException e) {
            // skip
        }
    }
}
