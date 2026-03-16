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

    // Set of Java keywords — renaming to any of these must be rejected.
    private static final java.util.Set<String> JAVA_KEYWORDS = java.util.Set.of(
            "abstract", "assert", "boolean", "break", "byte", "case", "catch", "char",
            "class", "const", "continue", "default", "do", "double", "else", "enum",
            "extends", "final", "finally", "float", "for", "goto", "if", "implements",
            "import", "instanceof", "int", "interface", "long", "native", "new",
            "package", "private", "protected", "public", "return", "short", "static",
            "strictfp", "super", "switch", "synchronized", "this", "throw", "throws",
            "transient", "try", "void", "volatile", "while",
            // boolean/null literals are not keywords but also forbidden as identifiers
            "true", "false", "null");

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
     * <p>Each edit's range is converted from 0-indexed (line, character) to a
     * character offset using {@link DefinitionFinder#lineColToOffset}, then the
     * substring between start and end offsets is replaced with the edit's new text.
     *
     * @param source                  original source text
     * @param sortedEditsDescending   edits sorted so that later positions in the
     *                                file come first; applying them in this order
     *                                preserves the validity of earlier positions
     * @return the modified source text
     */
    public static String applyEdits(String source, List<TextEdit> sortedEditsDescending) {
        for (TextEdit edit : sortedEditsDescending) {
            Range r = edit.getRange();
            int startOffset = DefinitionFinder.lineColToOffset(
                    source, r.getStart().getLine(), r.getStart().getCharacter());
            int endOffset = DefinitionFinder.lineColToOffset(
                    source, r.getEnd().getLine(), r.getEnd().getCharacter());
            source = source.substring(0, startOffset)
                    + edit.getNewText()
                    + source.substring(endOffset);
        }
        return source;
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
        // We compare the error count of the original sources against the modified
        // sources.  Pre-existing errors are not a reason to reject the rename;
        // only newly added errors are.
        int baselineErrors = CheckRunner.checkModifiedFiles(openContent, settings).size();
        Map<String, String> allSources = new HashMap<>(openContent);
        allSources.putAll(modifiedSources);
        List<org.eclipse.lsp4j.Diagnostic> modifiedDiags =
                CheckRunner.checkModifiedFiles(allSources, settings);
        if (modifiedDiags.size() > baselineErrors) {
            org.eclipse.lsp4j.Diagnostic d = modifiedDiags.get(0);
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
