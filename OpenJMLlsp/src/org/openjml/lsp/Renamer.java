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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
        return computeRefsAndEdits(uri, line, col, newName, openContent, cache).editsByUri();
    }

    /**
     * Holds both the reference locations (for stability checks) and the derived
     * TextEdits (for applying the rename) in a single pass over the AST cache.
     */
    private record RefsAndEdits(List<Location> refs, Map<String, List<TextEdit>> editsByUri) {}

    /**
     * Find all references to the symbol at ({@code line}, {@code col}) in {@code uri},
     * build TextEdits that replace each reference with {@code newName}, and return both.
     *
     * <p>Computing both in one pass avoids a second {@code findReferences} call in
     * {@link #rename} when the stability check also needs the reference list.
     */
    private static RefsAndEdits computeRefsAndEdits(
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

        return new RefsAndEdits(refs, edits);
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

        // 2. Find all references and build TextEdits in one pass.
        RefsAndEdits refsAndEdits = computeRefsAndEdits(uri, line, col, newName, openContent, cache);
        List<Location> beforeRefs = refsAndEdits.refs();
        Map<String, List<TextEdit>> editsByUri = refsAndEdits.editsByUri();
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
        // We compare the ERROR-severity diagnostic count of the original sources
        // against the modified sources.  Pre-existing warnings/errors are not a
        // reason to reject the rename; only newly added ERROR-severity diagnostics
        // are.  Using error-only counts prevents false rejections when warnings
        // disappear (e.g., "overrides without 'also'") while new errors appear at
        // the same time (keeping total count equal but hiding a real problem).
        // We also reuse the fresh AST produced here for the stability check below.
        long baselineErrors = CheckRunner.checkModifiedFiles(openContent, settings).stream()
                .filter(d -> d.getSeverity() == org.eclipse.lsp4j.DiagnosticSeverity.Error)
                .count();
        Map<String, String> allSources = new HashMap<>(openContent);
        allSources.putAll(modifiedSources);
        CheckRunner.CheckAndCacheResult checkResult =
                CheckRunner.checkModifiedFilesAndGetCache(allSources, settings);
        long afterErrors = checkResult.diagnostics().stream()
                .filter(d -> d.getSeverity() == org.eclipse.lsp4j.DiagnosticSeverity.Error)
                .count();
        if (afterErrors > baselineErrors) {
            org.eclipse.lsp4j.Diagnostic d = checkResult.diagnostics().stream()
                    .filter(di -> di.getSeverity() == org.eclipse.lsp4j.DiagnosticSeverity.Error)
                    .findFirst().orElse(checkResult.diagnostics().get(0));
            var msg = d.getMessage();
            String firstMsg = msg.isLeft() ? msg.getLeft() : msg.getRight().getValue();
            throw new ResponseErrorException(new ResponseError(
                    ResponseErrorCode.InvalidParams,
                    "Rename would introduce errors: " + firstMsg,
                    null));
        }

        // 4.5. Reference stability check: the set of positions that reference the
        // renamed symbol must not change (modulo the expected position shifts from
        // the rename itself).  This catches "reference capture" — cases where the
        // renamed symbol silently takes over a reference that previously resolved
        // to a different symbol with the same new name, or loses a reference because
        // another symbol of the same name is now in scope and shadows it.
        //
        // A fast-fail size comparison is done first; set equality is checked only
        // when the counts match (to catch the rarer equal-count / different-position
        // case that size alone cannot detect).
        if (!beforeRefs.isEmpty()) {
            int oldNameLen = beforeRefs.get(0).getRange().getEnd().getCharacter()
                           - beforeRefs.get(0).getRange().getStart().getCharacter();
            verifyReferenceStability(uri, line, col,
                    beforeRefs, oldNameLen, newName,
                    editsByUri, allSources, checkResult);
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
    // Reference stability check
    // -----------------------------------------------------------------------

    /**
     * Verify that the renamed symbol has exactly the same set of reference
     * positions in the modified sources as it had in the original sources
     * (after accounting for the column shift introduced by the rename itself).
     *
     * <p>The check has two stages:
     * <ol>
     *   <li><b>Fast-fail size check</b>: if the number of references to the
     *       renamed symbol in the modified compilation differs from the number
     *       in the original compilation, the rename captured or lost references
     *       and is rejected immediately.</li>
     *   <li><b>Position-set equality</b>: each original reference position is
     *       shifted forward by {@code (newName.length − oldNameLen) × numberOfEditsOnSameLineBefore}
     *       to compute the expected position in the modified source.  The set of
     *       expected positions must equal the set of actual positions returned by
     *       {@link ReferenceFinder#findReferences} on the modified AST.</li>
     * </ol>
     *
     * <p>Example: renaming parameter {@code yy} to {@code xx} in a class that
     * already has a field {@code xx} causes the body reference {@code int j = xx}
     * (which previously resolved to the field) to now resolve to the parameter.
     * The {@code afterRefs} count for the renamed parameter grows from 1 to 2,
     * which triggers the fast-fail.
     *
     * @throws ResponseErrorException if the stability check fails
     */
    private static void verifyReferenceStability(
            String uri, int line, int col,
            List<Location> beforeRefs,
            int oldNameLen,
            String newName,
            Map<String, List<TextEdit>> editsByUri,
            Map<String, String> allSources,
            CheckRunner.CheckAndCacheResult checkResult) {

        // The stability check operates only on plain Java (.java) files.
        //
        // JML companion (.jml) spec files are loaded by OpenJML as side inputs when
        // a .java file is compiled — they do NOT produce their own top-level AST
        // cache entries in a fresh compilation.  Therefore:
        //   • If the cursor is inside a .jml file, we cannot locate the renamed
        //     symbol in the fresh cache → skip the check to avoid a false rejection.
        //   • References reported in .jml files are excluded from both the expected
        //     and actual sets, so that .jml-only references (ghost/model fields used
        //     in spec clauses) do not trigger a spurious mismatch.
        if (uri.endsWith(".jml")) return;

        ASTCache freshCache = checkResult.cache();
        Map<String, String> tempPathToRealUri = checkResult.tempPathToRealUri();

        // Build reverse map: real URI → temp absolute path.
        Map<String, String> realUriToTempPath = new HashMap<>();
        for (Map.Entry<String, String> e : tempPathToRealUri.entrySet()) {
            realUriToTempPath.put(e.getValue(), e.getKey());
        }

        // Build content map keyed by temp absolute path (for findReferences).
        // allSources is keyed by real URIs; we need temp-path keys to match
        // the fresh cache entries.
        Map<String, String> tempContentMap = new HashMap<>();
        for (Map.Entry<String, String> e : allSources.entrySet()) {
            String tempPath = realUriToTempPath.get(e.getKey());
            if (tempPath != null) tempContentMap.put(tempPath, e.getValue());
        }

        // Locate the cursor's temp path.
        String tempCursorPath = realUriToTempPath.get(uri);
        if (tempCursorPath == null) return; // no cache entry — skip check

        // Compute the shifted cursor position: renames don't add newlines, so
        // only the column shifts for each edit on the same line before the cursor.
        int delta = newName.length() - oldNameLen;
        int shiftedLine = line;
        int shiftedCol  = col;
        if (delta != 0) {
            List<TextEdit> cursorEdits = editsByUri.get(uri);
            if (cursorEdits != null) {
                int k = 0;
                for (TextEdit e : cursorEdits) {
                    int el = e.getRange().getStart().getLine();
                    int ec = e.getRange().getStart().getCharacter();
                    if (el == line && ec < col) k++;
                }
                shiftedCol = col + k * delta;
            }
        }

        // Find references to the renamed symbol in the modified compilation.
        List<Location> afterRefs = ReferenceFinder.findReferences(
                tempCursorPath, shiftedLine, shiftedCol,
                tempContentMap, freshCache, /* includeDeclaration= */ true);

        // Count only .java references on each side for the fast-fail comparison.
        // .jml companion files are excluded (see comment above).
        long beforeJavaCount = beforeRefs.stream()
                .filter(l -> !l.getUri().endsWith(".jml")).count();
        long afterJavaCount  = afterRefs.stream()
                .filter(l -> {
                    String real = tempPathToRealUri.getOrDefault(l.getUri(), l.getUri());
                    return !real.endsWith(".jml");
                }).count();

        // Fast-fail: different reference count → capture or loss detected.
        if (afterJavaCount != beforeJavaCount) {
            throw new ResponseErrorException(new ResponseError(
                    ResponseErrorCode.InvalidParams,
                    "Rename would capture or lose references: "
                    + beforeJavaCount + " reference(s) before, "
                    + afterJavaCount + " reference(s) after",
                    null));
        }

        // Build expected position set: each beforeRef position shifted through the edits.
        // Skip .jml refs — they come from companion spec files not compiled in the
        // fresh pass, so they would produce a spurious count mismatch.
        Set<String> expectedKeys = new HashSet<>();
        for (Location loc : beforeRefs) {
            String realUri = loc.getUri();
            if (realUri.endsWith(".jml")) continue;
            int refLine = loc.getRange().getStart().getLine();
            int refCol  = loc.getRange().getStart().getCharacter();

            int shift = 0;
            if (delta != 0) {
                List<TextEdit> editsForUri = editsByUri.get(realUri);
                if (editsForUri != null) {
                    int k = 0;
                    for (TextEdit e : editsForUri) {
                        if (e.getRange().getStart().getLine() == refLine
                                && e.getRange().getStart().getCharacter() < refCol) k++;
                    }
                    shift = k * delta;
                }
            }
            expectedKeys.add(realUri + ":" + refLine + ":" + (refCol + shift));
        }

        // Build actual position set: afterRef positions mapped to real URIs.
        // Skip .jml refs (see comment above).
        Set<String> afterKeys = new HashSet<>();
        for (Location loc : afterRefs) {
            // loc.getUri() is a temp absolute path (matching tempPathToRealUri keys).
            String realUri = tempPathToRealUri.getOrDefault(loc.getUri(), loc.getUri());
            if (realUri.endsWith(".jml")) continue;
            int refLine = loc.getRange().getStart().getLine();
            int refCol  = loc.getRange().getStart().getCharacter();
            afterKeys.add(realUri + ":" + refLine + ":" + refCol);
        }

        if (!afterKeys.equals(expectedKeys)) {
            throw new ResponseErrorException(new ResponseError(
                    ResponseErrorCode.InvalidParams,
                    "Rename would capture or lose references: "
                    + "reference positions in .java files differ after rename",
                    null));
        }
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
