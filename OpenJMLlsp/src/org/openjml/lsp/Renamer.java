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

        System.err.println("[Renamer.computeRefsAndEdits] refs found (" + refs.size() + "):");
        refs.forEach(loc -> System.err.println("[Renamer]   ref: " + loc.getUri()
                + " " + loc.getRange().getStart().getLine()
                + ":" + loc.getRange().getStart().getCharacter()));

        Map<String, List<TextEdit>> edits = new HashMap<>();
        for (Location loc : refs) {
            Range r = loc.getRange();
            TextEdit edit = new TextEdit(r, newName);
            edits.computeIfAbsent(loc.getUri(), k -> new ArrayList<>()).add(edit);
        }

        System.err.println("[Renamer.computeRefsAndEdits] edits by URI (" + edits.size() + "):");
        edits.forEach((u, list) -> System.err.println("[Renamer]   edits: " + u + " (" + list.size() + ")"));

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
    /** Convenience wrapper for logging: convert LSP (line, character) to a source offset. */
    public static int offsetOf(String source, int line, int col) {
        return DefinitionFinder.lineColToOffset(source, line, col);
    }

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

        // 3. Build a complete project content map: all files in the nav cache that
        // belong to the same project as the cursor (scoped by project roots), reading
        // non-open files from disk.  Open/in-memory content takes precedence.
        List<String> projectRoots = OpenJMLTextDocumentService.rootsForUri(
                uri, settings.effectiveRoots());
        Map<String, String> completeContent = new HashMap<>();
        cache.forEachNav((navUri, navEntry) -> {
            // Always include files that carry rename edits (cross-project references).
            // For other files, apply the project root filter if one is set.
            if (!projectRoots.isEmpty()
                    && !isUnderRoots(navUri, projectRoots)
                    && !editsByUri.containsKey(navUri)) return;
            String content = openContent.get(navUri);
            if (content == null) {
                String path = CheckRunner.uriToPath(navUri);
                if (path != null) {
                    try { content = java.nio.file.Files.readString(java.nio.file.Path.of(path)); }
                    catch (Exception ignored) {}
                }
            }
            if (content != null) completeContent.put(navUri, content);
        });
        // Also include any open files in the project not covered by the nav cache,
        // and any open files that carry rename edits (cross-project references).
        openContent.forEach((openUri, openSrc) -> {
            if (projectRoots.isEmpty() || isUnderRoots(openUri, projectRoots)
                    || editsByUri.containsKey(openUri))
                completeContent.put(openUri, openSrc);
        });

        // Apply edits to build modified sources (over the complete content map).
        // If a file has edits but is not in completeContent (e.g. a companion .jml
        // that is not a nav cache entry and not currently open), read it from disk.
        Map<String, String> modifiedSources = new HashMap<>();
        for (Map.Entry<String, List<TextEdit>> entry : editsByUri.entrySet()) {
            String fileUri = entry.getKey();
            String originalSource = completeContent.get(fileUri);
            if (originalSource == null) {
                String path = CheckRunner.uriToPath(fileUri);
                if (path != null) {
                    try { originalSource = java.nio.file.Files.readString(java.nio.file.Path.of(path)); }
                    catch (Exception ignored) {}
                }
                if (originalSource == null) continue;
                completeContent.put(fileUri, originalSource);
            }
            modifiedSources.put(fileUri, applyEdits(originalSource, entry.getValue()));
        }

        // 4. Validate: check that the rename does not INTRODUCE new errors.
        // We compare the ERROR-severity diagnostic count of the original sources
        // against the modified sources.  Pre-existing warnings/errors are not a
        // reason to reject the rename; only newly added ERROR-severity diagnostics
        // are.  Using error-only counts prevents false rejections when warnings
        // disappear (e.g., "overrides without 'also'") while new errors appear at
        // the same time (keeping total count equal but hiding a real problem).
        // We also reuse the fresh AST produced here for the stability check below.
        System.err.println("[Renamer] completeContent files (" + completeContent.size() + "):");
        completeContent.forEach((k, v) -> System.err.println("[Renamer]   BEFORE " + k + " (" + v.length() + " chars)"));
        System.err.println("[Renamer] modifiedSources files (" + modifiedSources.size() + "):");
        modifiedSources.forEach((k, v) -> System.err.println("[Renamer]   AFTER " + k + " (" + v.length() + " chars)"));

        List<org.eclipse.lsp4j.Diagnostic> baselineDiags =
                CheckRunner.checkModifiedFiles(completeContent, settings);
        long baselineErrors = baselineDiags.stream()
                .filter(d -> d.getSeverity() == org.eclipse.lsp4j.DiagnosticSeverity.Error)
                .count();
        System.err.println("[Renamer] baseline errors: " + baselineErrors);
        baselineDiags.stream()
                .filter(d -> d.getSeverity() == org.eclipse.lsp4j.DiagnosticSeverity.Error)
                .forEach(d -> {
                    var m = d.getMessage();
                    System.err.println("[Renamer]   baseline error: "
                            + (m.isLeft() ? m.getLeft() : m.getRight().getValue())
                            + " source=" + d.getSource());
                });

        Map<String, String> allSources = new HashMap<>(completeContent);
        allSources.putAll(modifiedSources);
        CheckRunner.CheckAndCacheResult checkResult =
                CheckRunner.checkModifiedFilesAndGetCache(allSources, settings);
        long afterErrors = checkResult.diagnostics().stream()
                .filter(d -> d.getSeverity() == org.eclipse.lsp4j.DiagnosticSeverity.Error)
                .count();
        System.err.println("[Renamer] after-rename errors: " + afterErrors);
        checkResult.diagnostics().stream()
                .filter(d -> d.getSeverity() == org.eclipse.lsp4j.DiagnosticSeverity.Error)
                .forEach(d -> {
                    var m = d.getMessage();
                    System.err.println("[Renamer]   after error: "
                            + (m.isLeft() ? m.getLeft() : m.getRight().getValue())
                            + " source=" + d.getSource());
                });

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
        // freshCache and allSources are both keyed by real URIs, so use uri directly.
        System.err.println("[Renamer.verifyReferenceStability] uri=" + uri
                + " shiftedLine=" + shiftedLine + " shiftedCol=" + shiftedCol
                + " delta=" + delta + " newName=" + newName);
        System.err.println("[Renamer.verifyReferenceStability] freshCache nav keys:");
        freshCache.forEachNav((k, v) -> System.err.println("[Renamer]   navKey=" + k));
        System.err.println("[Renamer.verifyReferenceStability] allSources keys:");
        allSources.forEach((k, v) -> System.err.println("[Renamer]   srcKey=" + k + " (" + v.length() + " chars)"));
        // Log what text appears near the shifted cursor in the modified source.
        String cursorSrc = allSources.get(uri);
        if (cursorSrc != null) {
            int cursorOffset = DefinitionFinder.lineColToOffset(cursorSrc, shiftedLine, shiftedCol);
            int from = Math.max(0, cursorOffset - 20);
            int to   = Math.min(cursorSrc.length(), cursorOffset + 20);
            System.err.println("[Renamer.verifyReferenceStability] text near cursor: '"
                    + cursorSrc.substring(from, to).replace("\n", "\\n") + "' (offset=" + cursorOffset + ")");
        } else {
            System.err.println("[Renamer.verifyReferenceStability] uri not found in allSources");
        }
        List<Location> afterRefs = ReferenceFinder.findReferences(
                uri, shiftedLine, shiftedCol,
                allSources, freshCache, /* includeDeclaration= */ true);

        System.err.println("[Renamer.verifyReferenceStability] afterRefs (" + afterRefs.size() + "):");
        afterRefs.forEach(loc -> System.err.println("[Renamer]   afterRef: " + loc.getUri()
                + " " + loc.getRange().getStart().getLine()
                + ":" + loc.getRange().getStart().getCharacter()));

        // Count only .java references on each side for the fast-fail comparison.
        // .jml companion files are excluded (see comment above).
        long beforeJavaCount = beforeRefs.stream()
                .filter(l -> !l.getUri().endsWith(".jml")).count();
        long afterJavaCount  = afterRefs.stream()
                .filter(l -> !l.getUri().endsWith(".jml")).count();

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
            String refUri = loc.getUri();
            if (refUri.endsWith(".jml")) continue;
            int refLine = loc.getRange().getStart().getLine();
            int refCol  = loc.getRange().getStart().getCharacter();

            int shift = 0;
            if (delta != 0) {
                List<TextEdit> editsForUri = editsByUri.get(refUri);
                if (editsForUri != null) {
                    int k = 0;
                    for (TextEdit e : editsForUri) {
                        if (e.getRange().getStart().getLine() == refLine
                                && e.getRange().getStart().getCharacter() < refCol) k++;
                    }
                    shift = k * delta;
                }
            }
            expectedKeys.add(refUri + ":" + refLine + ":" + (refCol + shift));
        }

        // Build actual position set from afterRefs.
        // afterRefs locations use real URIs (freshCache is keyed by real URIs).
        // Skip .jml refs (see comment above).
        Set<String> afterKeys = new HashSet<>();
        for (Location loc : afterRefs) {
            if (loc.getUri().endsWith(".jml")) continue;
            int refLine = loc.getRange().getStart().getLine();
            int refCol  = loc.getRange().getStart().getCharacter();
            afterKeys.add(loc.getUri() + ":" + refLine + ":" + refCol);
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
    /** Returns true if the given URI falls under any of the given OS-path roots. */
    private static boolean isUnderRoots(String uri, List<String> roots) {
        String filePath;
        try { filePath = java.net.URI.create(uri).getPath(); }
        catch (Exception e) { return false; }
        String sep = java.io.File.separator;
        for (String root : roots) {
            String r = root.endsWith(sep) ? root : root + sep;
            if (filePath.startsWith(r)) return true;
        }
        return false;
    }

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
