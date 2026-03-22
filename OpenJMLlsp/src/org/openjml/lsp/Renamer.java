package org.openjml.lsp;

import com.sun.tools.javac.code.Symbol;
import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.Range;
import org.eclipse.lsp4j.TextEdit;
import org.eclipse.lsp4j.WorkspaceEdit;
import org.eclipse.lsp4j.jsonrpc.ResponseErrorException;
import org.eclipse.lsp4j.jsonrpc.messages.ResponseError;
import org.eclipse.lsp4j.jsonrpc.messages.ResponseErrorCode;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Computes and validates workspace edits for renaming a symbol in OpenJML/JML source.
 *
 * <p>Algorithm:
 * <ol>
 *   <li>Validate that {@code newName} is a legal Java identifier.</li>
 *   <li>Find all references (including the declaration) via {@link ReferenceFinder}.</li>
 *   <li>Group reference locations by URI, sort each group in descending order by
 *       (line, character) so that applying edits from the end of the file toward
 *       the beginning does not shift the offsets of earlier edits.</li>
 *   <li>Apply the edits to the in-memory sources and validate with
 *       {@link CheckRunner#checkModifiedFiles} — any compilation errors mean the
 *       rename is rejected.</li>
 *   <li>Return the {@link WorkspaceEdit} that the LSP client should apply.</li>
 * </ol>
 */
public class Renamer {

    private Renamer() {}

    // Java keywords forbidden as rename targets — defined in JmlKeywords.
    private static final java.util.Set<String> JAVA_KEYWORDS = JmlKeywords.JAVA_KEYWORDS;

    /**
     * Compute a map of URI → list-of-TextEdits for renaming the symbol at the
     * given cursor position to {@code newName}.  Each list is sorted in descending
     * order by line then character so that applying the edits in order does not
     * shift the positions of earlier edits.
     *
     * @return the edit map, possibly empty if no symbol is found at the cursor
     */
    public static Map<String, List<TextEdit>> computeEdits(
            String uri, int line, int col, String newName,
            Map<String, String> openContent, ASTCache cache) {

        List<Location> refs = ReferenceFinder.findReferences(
                uri, line, col, openContent, cache, /* includeDeclaration= */ true);

        Map<String, List<TextEdit>> edits = new HashMap<>();
        for (Location loc : refs) {
            Range r = loc.getRange();
            TextEdit edit = new TextEdit(r, newName);
            edits.computeIfAbsent(loc.getUri(), k -> new ArrayList<>()).add(edit);
        }

        // Sort each list descending: higher line first, then higher character first.
        Comparator<TextEdit> descending = Comparator
                .<TextEdit, Integer>comparing(e -> e.getRange().getStart().getLine())
                .thenComparingInt(e -> e.getRange().getStart().getCharacter())
                .reversed();
        for (List<TextEdit> list : edits.values()) {
            list.sort(descending);
        }

        return edits;
    }

    /**
     * Apply a list of text edits (sorted in descending position order) to a
     * source string.
     *
     * <p>Resolves all offsets up front, then applies edits in ascending position
     * order with a single-pass {@link StringBuilder}: unchanged regions are copied
     * once; each edit's range is replaced with its new text.  This is O(n) in the
     * source length regardless of the number of edits.
     *
     * @param source                  original source text
     * @param sortedEditsDescending   edits sorted so that later positions in the
     *                                file come first
     * @return the modified source text
     */
    public static String applyEdits(String source, List<TextEdit> sortedEditsDescending) {
        // Resolve all offsets first (against the original, unmodified source).
        record Replacement(int start, int end, String text) {}
        List<Replacement> replacements = new ArrayList<>(sortedEditsDescending.size());
        for (TextEdit edit : sortedEditsDescending) {
            Range r = edit.getRange();
            int startOffset = DefinitionFinder.lineColToOffset(
                    source, r.getStart().getLine(), r.getStart().getCharacter());
            int endOffset = DefinitionFinder.lineColToOffset(
                    source, r.getEnd().getLine(), r.getEnd().getCharacter());
            replacements.add(new Replacement(startOffset, endOffset, edit.getNewText()));
        }

        // Apply in ascending order (reverse of the descending input).
        StringBuilder sb = new StringBuilder(source.length());
        int pos = 0;
        for (int i = replacements.size() - 1; i >= 0; i--) {
            Replacement rep = replacements.get(i);
            sb.append(source, pos, rep.start());
            sb.append(rep.text());
            pos = rep.end();
        }
        sb.append(source, pos, source.length());
        return sb.toString();
    }

    /**
     * Rename the symbol at ({@code line}, {@code col}) in {@code uri} to
     * {@code newName}, validate the result, and return the workspace edit.
     *
     * @throws ResponseErrorException if {@code newName} is not a valid Java
     *         identifier, no renameable symbol is found at the cursor, or the
     *         rename would introduce compilation errors
     */
    public static WorkspaceEdit rename(
            String uri, int line, int col, String newName,
            Map<String, String> openContent, ASTCache cache,
            OpenJMLSettings settings) {

        // 1. Validate new name.
        if (!isValidJavaIdentifier(newName)) {
            throw new ResponseErrorException(new ResponseError(
                    ResponseErrorCode.InvalidParams,
                    "Not a valid Java identifier: " + newName,
                    null));
        }

        // 2. Compute edits.
        Map<String, List<TextEdit>> editsByUri = computeEdits(uri, line, col, newName, openContent, cache);
        if (editsByUri.isEmpty()) {
            throw new ResponseErrorException(new ResponseError(
                    ResponseErrorCode.InvalidParams,
                    "No renameable symbol at cursor",
                    null));
        }

        // 3. Apply edits to build modified sources.
        Map<String, String> modifiedSources = new HashMap<>();
        for (Map.Entry<String, List<TextEdit>> entry : editsByUri.entrySet()) {
            String fileUri = entry.getKey();
            String originalSource = openContent.get(fileUri);
            if (originalSource == null) continue;
            String modified = applyEdits(originalSource, entry.getValue());
            modifiedSources.put(fileUri, modified);
        }

        // 4. Validate: check that the rename does not INTRODUCE new errors.
        // Compare only ERROR-severity diagnostics (not warnings).  JML style warnings
        // (e.g. "specification should begin with 'also'") are present in both the
        // baseline and modified compilations and must not inflate the baseline count,
        // which would mask real errors introduced by the rename.
        long baselineErrors = countErrors(CheckRunner.checkModifiedFiles(openContent, settings));
        Map<String, String> allSources = new HashMap<>(openContent);
        allSources.putAll(modifiedSources);
        List<org.eclipse.lsp4j.Diagnostic> modifiedDiags =
                CheckRunner.checkModifiedFiles(allSources, settings);
        long modifiedErrors = countErrors(modifiedDiags);
        if (modifiedErrors > baselineErrors) {
            // Find the first ERROR-severity diagnostic for the message.
            org.eclipse.lsp4j.Diagnostic d = modifiedDiags.stream()
                    .filter(x -> x.getSeverity() == org.eclipse.lsp4j.DiagnosticSeverity.Error)
                    .findFirst().orElse(modifiedDiags.get(0));
            var msg = d.getMessage();
            String firstMsg = msg.isLeft() ? msg.getLeft() : msg.getRight().getValue();
            throw new ResponseErrorException(new ResponseError(
                    ResponseErrorCode.InvalidParams,
                    "Rename would introduce errors: " + firstMsg,
                    null));
        }

        // 5. Build and return WorkspaceEdit.
        WorkspaceEdit wsEdit = new WorkspaceEdit();
        Map<String, List<TextEdit>> lsp4jEdits = new HashMap<>();
        for (Map.Entry<String, List<TextEdit>> entry : editsByUri.entrySet()) {
            lsp4jEdits.put(entry.getKey(), entry.getValue());
        }
        wsEdit.setChanges(lsp4jEdits);
        return wsEdit;
    }

    private static long countErrors(List<org.eclipse.lsp4j.Diagnostic> diags) {
        return diags.stream()
                .filter(d -> d.getSeverity() == org.eclipse.lsp4j.DiagnosticSeverity.Error)
                .count();
    }

    // -----------------------------------------------------------------------
    // Identifier validation
    // -----------------------------------------------------------------------

    /**
     * Returns {@code true} if {@code name} is a non-empty Java identifier that
     * is not a keyword or boolean/null literal.
     */
    private static boolean isValidJavaIdentifier(String name) {
        if (name == null || name.isEmpty()) return false;
        if (JAVA_KEYWORDS.contains(name)) return false;
        if (!Character.isJavaIdentifierStart(name.charAt(0))) return false;
        for (int i = 1; i < name.length(); i++) {
            if (!Character.isJavaIdentifierPart(name.charAt(i))) return false;
        }
        return true;
    }
}
