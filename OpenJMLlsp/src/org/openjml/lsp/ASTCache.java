package org.openjml.lsp;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.openjml.IAPI;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Caches the latest type-attributed AST for each open document URI.
 *
 * <p>Maintains two tiers:
 * <ul>
 *   <li><b>Nav tier</b> — populated by a project-wide {@code --check --dirs} pass.
 *       All entries within one project share a single IAPI compilation context, so
 *       symbol identity ({@code ==}) holds across files and cross-file navigation
 *       works reliably.  Takes highest precedence for navigation operations.
 *       Partitioned per project: each project has its own {@link NavSection}
 *       containing an independent AST cache and declaration index.</li>
 *   <li><b>Live tier</b> — populated by user-triggered {@code --check} / {@code --esc}
 *       runs on individual files.  Used when the nav tier has no entry for a URI
 *       (e.g. the user opened a file before a project-wide check completed).</li>
 * </ul>
 *
 * <p>Populated by {@link CheckRunner} via the {@code IAPI.IASTListener} callback
 * after each {@code --check} or {@code --esc} run.
 *
 * <p>Because {@code JmlCompiler.attribute()} fires one notification <em>per
 * class</em> (not per compilation unit), files containing multiple classes
 * receive multiple notifications.  Only the <em>last</em> notification for a
 * given source file has fully-resolved symbols for the whole compilation unit.
 * {@link #put} always overwrites, so the cache converges to the correct state.
 *
 * <p>Also maintains a cross-file declaration index ({@code Symbol → URI + charOffset})
 * built by scanning each cached AST.  Go-to-definition uses this index to
 * locate declarations.  Cross-file resolution works when both the use site and
 * the declaration were checked in the same {@code IAPI} invocation (same
 * compilation context), because javac reuses the same {@code Symbol} objects
 * for declarations and all their use sites within a single context.
 */
public class ASTCache {

    /** Declaration location: LSP URI and character offset of the declaration keyword. */
    public record SymbolLocation(String uri, int charOffset) {}

    /**
     * Cached entry for one source file.
     *
     * <p>The {@code api}, {@code diagListener}, {@code sourcePath}, and {@code escLock}
     * fields are non-null only when the entry was produced by a successful
     * {@code --check} run (exit code 0) on in-memory or on-disk content.
     * They are used by the in-process {@code doESC} path ({@code escEngine=concurrent}).
     * Nav-tier entries (project-wide check) always have them null.
     *
     * <p>{@link IAPI#doESC} is NOT thread-safe on the same IAPI instance; concurrent
     * calls for the same URI are serialized via {@code escLock}.  Calls on different
     * URIs use different IAPI instances and proceed in parallel, bounded by
     * the {@code escThreads} pool size.
     */
    public record Entry(JmlCompilationUnit ast, Context context,
                        IAPI api,
                        LspDiagnosticListener diagListener,
                        String sourcePath,
                        java.util.concurrent.locks.ReentrantLock escLock) {

        /** Create a basic entry without IAPI (for init-tier or failed checks). */
        static Entry basic(JmlCompilationUnit ast, Context ctx) {
            return new Entry(ast, ctx, null, null, null, null);
        }

        /** Create an entry with a stored IAPI for in-process doESC (successful checks only). */
        static Entry withApi(JmlCompilationUnit ast, Context ctx,
                             IAPI api, LspDiagnosticListener listener, String sourcePath) {
            return new Entry(ast, ctx, api, listener, sourcePath,
                             new java.util.concurrent.locks.ReentrantLock());
        }

        /** Returns true if this entry supports in-process doESC via {@link IAPI#doESC}. */
        public boolean supportsDoEsc() { return api != null; }
    }

    // -----------------------------------------------------------------------
    // Nav tier — one NavSection per project, keyed by canonical root-path set
    // -----------------------------------------------------------------------

    /**
     * Per-project container for the nav AST cache and its declaration index.
     *
     * <p>All entries in one {@code NavSection} were produced by a single
     * {@code --check --dirs} pass on the same set of source directories, so they
     * share one IAPI compilation context and symbol identity ({@code ==}) holds
     * across all files in the section.
     *
     * <p>A section is identified by the set of source-directory paths passed to
     * {@link CheckRunner#runCheckDir}.  {@link #coversProjectRoot(String)} is used
     * at query time to match a section against the Eclipse project root supplied by
     * the client.
     */
    private static class NavSection {
        /** Canonical source-directory paths that populate this section. */
        final List<String> rootPaths;
        /** URI → attributed AST for each file in this project's nav pass. */
        final Map<String, Entry> navCache = new ConcurrentHashMap<>();
        /** Symbol → declaration location, rebuilt by {@link #rebuildNavIndex()}. */
        final Map<Symbol, SymbolLocation> declarationIndex = new ConcurrentHashMap<>();

        NavSection(List<String> rootPaths) {
            this.rootPaths = List.copyOf(rootPaths);
        }

        /**
         * Returns {@code true} if this section covers source files under
         * {@code projectRoot}.
         *
         * <p>The heuristic: any configured root path that is <em>equal to</em> or
         * <em>under</em> {@code projectRoot} means the section belongs to that
         * project.  The trailing separator prevents {@code /ProjectA} from
         * matching {@code /ProjectABC}.
         */
        boolean coversProjectRoot(String projectRoot) {
            if (projectRoot == null) return true;
            String prWithSep = projectRoot.endsWith(java.io.File.separator)
                    ? projectRoot : projectRoot + java.io.File.separator;
            for (String root : rootPaths) {
                // root is under projectRoot (e.g., root = .../ProjectA/src, projectRoot = .../ProjectA)
                if (root.startsWith(prWithSep) || root.equals(projectRoot)) return true;
                // projectRoot is at or under root (e.g., both point to the same directory)
                String rootWithSep = root.endsWith(java.io.File.separator)
                        ? root : root + java.io.File.separator;
                if (projectRoot.startsWith(rootWithSep)) return true;
            }
            return false;
        }
    }

    /**
     * Project → its {@link NavSection}.
     *
     * <p>The key is the project ID when one is known (supplied by the caller via
     * {@link #putNav}), or a normalized, sorted, newline-joined concatenation of
     * the source-directory paths otherwise.  Using the project ID is preferred:
     * it is stable, human-readable, and does not depend on resolving symlinks.
     */
    private final Map<String, NavSection> navSections = new ConcurrentHashMap<>();

    // -----------------------------------------------------------------------
    // Live tier — user-triggered --check / --esc runs
    // -----------------------------------------------------------------------

    /** URI → latest attributed AST from a user-triggered check. */
    private final Map<String, Entry> liveCache = new ConcurrentHashMap<>();

    /**
     * Cross-file Symbol → declaration location from user-triggered checks.
     * Uses object identity (Symbol does not override equals/hashCode), which is
     * correct: within one IAPI invocation, declaration and use-site nodes share
     * the same Symbol instances.
     */
    private final Map<Symbol, SymbolLocation> liveDeclarationIndex = new ConcurrentHashMap<>();

    // -----------------------------------------------------------------------
    // Nav-tier writes
    // -----------------------------------------------------------------------

    /**
     * Remove nav-cache entries for the section identified by {@code rootPaths}.
     * Called before a project-wide check so that stale entries from the previous
     * run for <em>this project</em> do not linger, while other project sections
     * are left intact.
     *
     * <p>The declaration index is NOT cleaned here; it is fully rebuilt by
     * {@link #rebuildNavIndex()} after the check completes.
     */
    public void clearNavForRoots(List<String> rootPaths) {
        clearNavForRoots(rootPaths, null);
    }

    /**
     * Remove stale nav-cache entries for the section identified by {@code projectId}
     * (preferred) or by {@code rootPaths} (fallback when {@code projectId} is null).
     */
    public void clearNavForRoots(List<String> rootPaths, String projectId) {
        String key = (projectId != null && !projectId.isEmpty())
                ? projectId : OpenJMLSettings.WORKSPACE_PROJECT_ID;
        NavSection section = navSections.get(key);
        if (section != null) section.navCache.clear();
    }

    /** Clear all nav sections. Used by {@link #clear()} on full reset. */
    public void clearNav() {
        navSections.clear();
    }

    /**
     * Store an AST into the nav section for this project.
     *
     * <p>When {@code projectId} is non-null the section is keyed and looked up
     * by project ID; otherwise the key is derived from {@code projectRoots}.
     * All entries from one {@code --check --dirs} pass share one IAPI context,
     * so symbol identity holds across files.
     *
     * @param projectId    project identifier, or {@code null} for generic clients
     * @param projectRoots source-directory paths (used as fallback key and stored
     *                     in the section for {@code coversProjectRoot} matching)
     */
    public void putNav(String uri, Context ctx, JmlCompilationUnit ast,
                       List<String> projectRoots, String projectId) {
        String key = (projectId != null && !projectId.isEmpty())
                ? projectId : OpenJMLSettings.WORKSPACE_PROJECT_ID;
        navSections.computeIfAbsent(key, k -> new NavSection(projectRoots))
                   .navCache.put(uri, Entry.basic(ast, ctx));
    }

    /** Overload for callers without a project ID — uses the workspace sentinel key. */
    public void putNav(String uri, Context ctx, JmlCompilationUnit ast,
                       List<String> projectRoots) {
        putNav(uri, ctx, ast, projectRoots, null);
    }

    /**
     * Return the nav-tier entry for {@code uri}, searching all sections and
     * falling back to the live cache if absent.
     */
    public Entry getNav(String uri) {
        for (NavSection s : navSections.values()) {
            Entry e = s.navCache.get(uri);
            if (e != null) return e;
        }
        return liveCache.get(uri);
    }

    /**
     * Iterate over nav-cache entries (URI → Entry) for cross-file navigation
     * (find-references, rename).  Falls back to the live cache if no nav
     * sections have been populated yet.
     */
    public void forEachNav(java.util.function.BiConsumer<String, Entry> action) {
        if (!navSections.isEmpty()) {
            navSections.values().forEach(s -> s.navCache.forEach(action));
        } else {
            liveCache.forEach(action);
        }
    }

    /**
     * Returns {@code true} if {@code uri} has an entry in whichever tier
     * {@link #forEachNav} iterates (nav sections if non-empty, else live).
     * Used by {@link org.openjml.lsp.ReferenceFinder} to avoid scanning a
     * companion {@code .jml} file twice.
     */
    public boolean containsNav(String uri) {
        if (!navSections.isEmpty()) {
            return navSections.values().stream().anyMatch(s -> s.navCache.containsKey(uri));
        }
        return liveCache.containsKey(uri);
    }

    // -----------------------------------------------------------------------
    // Live-tier writes
    // -----------------------------------------------------------------------

    /**
     * Store (or overwrite) the AST for {@code uri} in the <em>live</em> tier,
     * without a stored IAPI (init-tier, failed check, or workspace-index).
     */
    public void put(String uri, Context ctx, JmlCompilationUnit ast) {
        storeInLive(uri, Entry.basic(ast, ctx));
    }

    /**
     * Store (or overwrite) the AST for {@code uri} in the <em>live</em> tier,
     * including the IAPI instance for in-process doESC (successful check only).
     */
    public void put(String uri, Context ctx, JmlCompilationUnit ast,
                    IAPI api, LspDiagnosticListener listener, String sourcePath) {
        storeInLive(uri, Entry.withApi(ast, ctx, api, listener, sourcePath));
    }

    private void storeInLive(String uri, Entry entry) {
        removeLiveDeclarationsForUri(uri);
        liveCache.put(uri, entry);
        new DeclarationIndexer(liveDeclarationIndex, uri).scan(entry.ast());
    }

    // -----------------------------------------------------------------------
    // Reads
    // -----------------------------------------------------------------------

    /**
     * Return the cached entry for {@code uri} from the live tier,
     * or {@code null} if absent.
     */
    public Entry get(String uri) {
        return liveCache.get(uri);
    }

    /**
     * Rebuild every nav section's declaration index from its AST cache.
     *
     * <p>Called by {@code runProjectCheck()} after a project-wide
     * {@code --check --dirs} pass.  Each section's entries were produced by the
     * same IAPI invocation, so all symbol objects within a section are
     * identity-compatible.
     */
    public void rebuildNavIndex() {
        int totalDecls = 0;
        for (NavSection section : navSections.values()) {
            section.declarationIndex.clear();
            section.navCache.forEach((uri, entry) ->
                    new DeclarationIndexer(section.declarationIndex, uri).scan(entry.ast()));
            totalDecls += section.declarationIndex.size();
        }
        System.err.println("[ASTCache] nav index rebuilt: " + navSections.size()
                + " section(s), " + totalDecls + " total declarations");
    }

    /** Return the declaration location for {@code sym}, or {@code null} if unknown. */
    public SymbolLocation getDeclarationLocation(Symbol sym) {
        // Nav sections are built from project-wide IAPI passes — check them first.
        for (NavSection s : navSections.values()) {
            SymbolLocation loc = s.declarationIndex.get(sym);
            if (loc != null) return loc;
        }
        SymbolLocation live = liveDeclarationIndex.get(sym);
        if (live != null) return live;

        // Identity lookup failed: the cursor symbol comes from a different IAPI
        // invocation than the nav index (e.g. a per-file check ran after the
        // project-wide check that built the index).  Fall back to a name-based
        // match in the nav index using qualified name + owner + symbol kind.
        // If exactly one entry matches, use it.  Ambiguous matches (e.g. two
        // overloads with the same name) are skipped to avoid returning the wrong
        // declaration.
        String qn      = sym.getQualifiedName().toString();
        String ownerQn = sym.owner != null ? sym.owner.getQualifiedName().toString() : "";
        String kind    = sym.getClass().getSimpleName();
        if (!qn.isEmpty() && !navSections.isEmpty()) {
            SymbolLocation match = null;
            boolean ambiguous = false;
            outer:
            for (NavSection s : navSections.values()) {
                for (Map.Entry<Symbol, SymbolLocation> e : s.declarationIndex.entrySet()) {
                    Symbol candidate = e.getKey();
                    if (qn.equals(candidate.getQualifiedName().toString())
                            && kind.equals(candidate.getClass().getSimpleName())
                            && ownerQn.equals(candidate.owner != null
                                    ? candidate.owner.getQualifiedName().toString() : "")) {
                        if (match != null) { ambiguous = true; break outer; }
                        match = e.getValue();
                    }
                }
            }
            if (!ambiguous && match != null) return match;
        }
        return null;
    }

    // -----------------------------------------------------------------------
    // Removals
    // -----------------------------------------------------------------------

    /** Remove the cached entry and its indexed declarations from all tiers (e.g. on didClose). */
    public void remove(String uri) {
        navSections.values().forEach(s -> {
            s.navCache.remove(uri);
            s.declarationIndex.entrySet().removeIf(e -> uri.equals(e.getValue().uri()));
        });
        liveCache.remove(uri);
        removeLiveDeclarationsForUri(uri);
    }

    /**
     * Clear all cached entries and declaration indexes from all tiers.
     * Called by the clear-and-reindex command.
     */
    public void clear() {
        navSections.clear();
        liveCache.clear();
        liveDeclarationIndex.clear();
    }

    // -----------------------------------------------------------------------
    // Iteration
    // -----------------------------------------------------------------------

    /**
     * Iterate over live-tier entries (URI → Entry).
     * Used for operations that require a shared IAPI context (go-to-definition,
     * cross-file references).
     */
    public void forEach(java.util.function.BiConsumer<String, Entry> action) {
        liveCache.forEach(action);
    }

    /**
     * Iterate over all indexed declarations from all nav sections and the live tier.
     *
     * <p>Equivalent to {@link #forEachDeclaration(String, java.util.function.BiConsumer)}
     * with a {@code null} project-root filter (returns everything).
     */
    public void forEachDeclaration(java.util.function.BiConsumer<Symbol, SymbolLocation> action) {
        forEachDeclaration(null, action);
    }

    /**
     * Iterate over indexed declarations, optionally restricted to one project.
     *
     * <p>When {@code projectRoot} is non-null, only nav sections that
     * {@linkplain NavSection#coversProjectRoot cover} that root and live-tier
     * entries whose URI falls under that root are included.  When
     * {@code projectRoot} is {@code null}, all sections and all live entries
     * are included.
     *
     * <p>Used by {@code workspace/symbol} and the {@code openjml.symbolsForProject}
     * command to search within a specific project.
     *
     * @param projectRoot file-system path of the Eclipse project root, or
     *                    {@code null} to return all projects
     */
    /**
     * Iterate over indexed declarations, optionally restricted to one project.
     *
     * <p>When {@code projectRoot} is non-null, only nav sections that
     * {@linkplain NavSection#coversProjectRoot cover} that root and live-tier
     * entries whose URI falls under that root are included.  When
     * {@code projectRoot} is {@code null}, all sections and all live entries
     * are included.
     *
     * <p>Used by {@code workspace/symbol} and the {@code openjml.symbolsForProject}
     * command to search within a specific project.
     *
     * @param projectRoot file-system path of the Eclipse project root, or
     *                    {@code null} to return all projects
     */
    public void forEachDeclaration(String projectRoot,
            java.util.function.BiConsumer<Symbol, SymbolLocation> action) {
        // Collect the set of URIs covered by the nav sections we will iterate,
        // so the live fallback can skip files already in the nav index.
        Set<String> navCoveredUris = ConcurrentHashMap.newKeySet();

        for (NavSection section : navSections.values()) {
            navCoveredUris.addAll(section.navCache.keySet());
            if (projectRoot == null || section.coversProjectRoot(projectRoot)) {
                section.declarationIndex.forEach((sym, loc) -> {
                    // Even when the section covers the project root, individual
                    // declarations must also be under that root.  This matters
                    // when multiple projects were indexed together into one section
                    // (e.g. the startup indexProject(null) call).
                    if (projectRoot == null || uriUnderRoot(loc.uri(), projectRoot))
                        action.accept(sym, loc);
                });
            }
        }

        // Live index covers files checked individually since the last project-wide check.
        // Skip URIs already in a nav section; apply the project filter to URIs.
        liveDeclarationIndex.forEach((sym, loc) -> {
            if (navCoveredUris.contains(loc.uri())) return;
            if (projectRoot != null && !uriUnderRoot(loc.uri(), projectRoot)) return;
            action.accept(sym, loc);
        });
    }

    /**
     * Iterate over all declarations belonging to the project with the given ID.
     *
     * <p>The nav section is looked up directly by project ID (O(1)).  All symbols
     * in that section are included — no per-symbol URI filtering — because the
     * section was built exclusively from this project's sources.  Live-tier entries
     * are included if they fall under any of the section's root paths.
     * When {@code projectId} is null or empty, delegates to
     * {@link #forEachDeclaration(String, java.util.function.BiConsumer)} with a
     * null filter (all projects).
     */
    public void forEachDeclarationForProject(String projectId,
            java.util.function.BiConsumer<Symbol, SymbolLocation> action) {
        if (projectId == null || projectId.isEmpty()) {
            forEachDeclaration((String) null, action);
            return;
        }
        NavSection section = navSections.get(projectId);
        Set<String> navCoveredUris = ConcurrentHashMap.newKeySet();
        if (section != null) {
            navCoveredUris.addAll(section.navCache.keySet());
            section.declarationIndex.forEach(action);
        }
        // Live-tier: include entries under any of this project's source roots.
        List<String> roots = section != null ? section.rootPaths : List.of();
        liveDeclarationIndex.forEach((sym, loc) -> {
            if (navCoveredUris.contains(loc.uri())) return;
            if (roots.stream().noneMatch(r -> uriUnderRoot(loc.uri(), r))) return;
            action.accept(sym, loc);
        });
    }

    // -----------------------------------------------------------------------
    // Private helpers
    // -----------------------------------------------------------------------

    private void removeLiveDeclarationsForUri(String uri) {
        liveDeclarationIndex.entrySet().removeIf(e -> uri.equals(e.getValue().uri()));
    }

    /**
     * Returns {@code true} if the file-system path extracted from {@code uri}
     * starts with {@code root} (with a separator to avoid prefix collisions).
     */
    private static boolean uriUnderRoot(String uri, String root) {
        try {
            String path = java.net.URI.create(uri).getPath();
            if (path == null) return false;
            String rootWithSep = root.endsWith(java.io.File.separator)
                    ? root : root + java.io.File.separator;
            return path.startsWith(rootWithSep) || path.equals(root);
        } catch (Exception e) {
            return false;
        }
    }

    private class DeclarationIndexer extends JmlTreeScanner {
        private final Map<Symbol, SymbolLocation> index;
        private final String uri;

        DeclarationIndexer(Map<Symbol, SymbolLocation> index, String uri) {
            this.index = index;
            this.uri   = uri;
        }

        @Override
        public void visitClassDef(JCClassDecl tree) {
            if (tree.sym != null && tree.pos >= 0 && !skipJmlNodeInJavaCu(tree))
                record(tree.sym, tree.pos);
            super.visitClassDef(tree);
        }

        @Override
        public void visitMethodDef(JCMethodDecl tree) {
            if (tree.sym != null && tree.pos >= 0 && !skipJmlNodeInJavaCu(tree))
                record(tree.sym, tree.pos);
            super.visitMethodDef(tree);
        }

        @Override
        public void visitVarDef(JCVariableDecl tree) {
            // Index all variable declarations: fields, parameters, locals, and
            // JML-bound variables (\forall, \exists, \let).  Go-to-definition
            // for formals and JML quantifier variables depends on these entries.
            if (tree.sym != null && tree.pos >= 0 && !skipJmlNodeInJavaCu(tree))
                record(tree.sym, tree.pos);
            super.visitVarDef(tree);
        }

        /**
         * Returns {@code true} when a JML declaration node (ghost/model field,
         * model method, spec class) from a {@code .jml} companion file is
         * encountered while scanning a {@code .java} compilation unit.
         *
         * <p>Such nodes should be skipped here: they will be recorded under the
         * correct {@code .jml} URI when the companion {@code .jml} AST is scanned
         * by {@link #cacheSpecsCu}.  Recording them under {@code javaUri} here
         * would assign a wrong location and the merge rule would keep that wrong
         * entry over the later correct {@code .jml} entry.
         */
        private boolean skipJmlNodeInJavaCu(JCTree tree) {
            if (uri.endsWith(".jml")) return false;   // scanning .jml CU — always record
            javax.tools.JavaFileObject sf = null;
            if (tree instanceof JmlVariableDecl jv)  sf = jv.sourcefile;
            else if (tree instanceof JmlMethodDecl jm) sf = jm.sourcefile;
            else if (tree instanceof JmlClassDecl jc && jc.toplevel != null) sf = jc.toplevel.sourcefile;
            return sf != null && sf.toUri().toString().endsWith(".jml");
        }

        /**
         * Record {@code sym → (uri, pos)} in the index.
         *
         * <p>Preference rules:
         * <ul>
         *   <li><b>Ghost/model symbols</b> ({@code JMLBIT} set): the {@code .jml} URI is
         *       authoritative.  A {@code .jml} entry always wins over a {@code .java} entry.
         *       {@link #skipJmlNodeInJavaCu} normally prevents these symbols from being
         *       recorded under the {@code .java} URI in the first place; this rule is the
         *       safety net for the case where {@code sourcefile} is not set on the merged
         *       node.</li>
         *   <li><b>Regular Java symbols</b>: a {@code .java} declaration is never
         *       overwritten by a {@code .jml} spec stub for the same symbol.</li>
         * </ul>
         */
        private void record(Symbol sym, int pos) {
            SymbolLocation incoming = new SymbolLocation(uri, pos);
            boolean isJmlSym = org.jmlspecs.openjml.Utils.isJML(sym.flags());
            index.merge(sym, incoming, (existing, in) -> {
                if (isJmlSym) {
                    if (existing.uri().endsWith(".jml")) return existing;
                    if (in.uri().endsWith(".jml"))       return in;
                    return in;
                } else {
                    return !existing.uri().endsWith(".jml") && in.uri().endsWith(".jml")
                            ? existing : in;
                }
            });
        }
    }
}
