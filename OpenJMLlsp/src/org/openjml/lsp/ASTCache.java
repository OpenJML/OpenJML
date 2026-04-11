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

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Caches the latest type-attributed AST for each open document URI.
 *
 * <p>Maintains two tiers:
 * <ul>
 *   <li><b>Nav cache</b> — populated by a project-wide {@code --check --dirs} pass.
 *       All entries share a single IAPI compilation context, so symbol identity
 *       ({@code ==}) holds across files and cross-file navigation works reliably.
 *       Takes highest precedence for navigation operations.</li>
 *   <li><b>Live cache</b> — populated by user-triggered {@code --check} / {@code --esc}
 *       runs on individual files.  Used when the nav cache has no entry for a URI
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
    // Nav tier — project-wide check for navigation (go-to-declaration etc.)
    // -----------------------------------------------------------------------

    /**
     * URI → attributed AST from the most recent project-wide {@code --check --dirs} pass.
     * All entries share a single IAPI compilation context, so symbol identity ({@code ==})
     * holds across files and cross-file navigation works reliably.
     *
     * <p>Written only by {@link #putNav}; never touched by per-file checks so it is
     * immune to IAPI-context fragmentation.
     */
    private final Map<String, Entry> navCache = new ConcurrentHashMap<>();

    /**
     * Cross-file Symbol → declaration location built exclusively from the most
     * recent project-wide {@code --check --dirs} pass.  Because all files in
     * that pass share a single IAPI compilation context, symbol identity ({@code ==})
     * holds across files and navigation works reliably.
     *
     * <p>Populated only by {@link #rebuildNavIndex()}; never written by individual
     * file checks so it is immune to IAPI-context fragmentation.
     */
    private final Map<Symbol, SymbolLocation> navDeclarationIndex = new ConcurrentHashMap<>();

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
     * Remove nav-cache entries for files whose path starts with one of the
     * given {@code rootPaths}.  Called before a project-wide check so that
     * stale entries from the previous run for <em>this project</em> do not
     * linger, while entries from other projects are left intact.
     *
     * <p>The nav declaration index is <em>not</em> cleaned here; it is fully
     * rebuilt by {@link #rebuildNavIndex()} after the check completes.
     */
    public void clearNavForRoots(java.util.List<String> rootPaths) {
        navCache.keySet().removeIf(uri -> {
            try {
                String path = java.net.URI.create(uri).getPath();
                if (path == null) return false;
                for (String root : rootPaths) {
                    String r = root.endsWith(java.io.File.separator)
                            ? root : root + java.io.File.separator;
                    if (path.startsWith(r) || path.equals(root)) return true;
                }
            } catch (Exception ignored) {}
            return false;
        });
    }

    /** Clear the entire nav cache. Used by {@link #clear()} on full reset. */
    public void clearNav() {
        navCache.clear();
    }

    /**
     * Store an AST into the nav cache.  Called by the per-instance
     * {@code IASTListener} registered in {@link CheckRunner#runCheckDirWithContext}.
     * All entries stored by a single project-wide run share one IAPI compilation
     * context, so symbol identity holds across all of them.
     */
    public void putNav(String uri, Context ctx, JmlCompilationUnit ast) {
        navCache.put(uri, Entry.basic(ast, ctx));
    }

    /**
     * Return the nav-cache entry for {@code uri}, falling back to the live
     * cache if absent.
     */
    public Entry getNav(String uri) {
        Entry nav = navCache.get(uri);
        if (nav != null) return nav;
        return liveCache.get(uri);
    }

    /**
     * Iterate over nav-cache entries (URI → Entry) for cross-file navigation
     * operations (find-references, rename).  Falls back to the live cache if
     * the nav cache has not yet been populated.
     */
    public void forEachNav(java.util.function.BiConsumer<String, Entry> action) {
        if (!navCache.isEmpty()) {
            navCache.forEach(action);
        } else {
            liveCache.forEach(action);
        }
    }

    /**
     * Returns {@code true} if {@code uri} has an entry in whichever cache tier
     * {@link #forEachNav} iterates (nav if non-empty, otherwise live).
     * Used by {@link org.openjml.lsp.ReferenceFinder} to avoid scanning a
     * companion {@code .jml} file twice when it also appears as its own nav entry.
     */
    public boolean containsNav(String uri) {
        if (!navCache.isEmpty()) return navCache.containsKey(uri);
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
     * Rebuild the nav declaration index from all live-tier ASTs.
     *
     * <p>Called by {@code runProjectCheck()} after a project-wide
     * {@code --check --dirs} pass.  At that point every live-cache entry was
     * produced by the same IAPI invocation, so all symbol objects are identity-
     * compatible and cross-file navigation works reliably.
     *
     * <p>Individual file checks ({@code recheckUri}, {@code didSave}) never call
     * this method, so the nav index is only ever updated by project-wide checks.
     */
    public void rebuildNavIndex() {
        navDeclarationIndex.clear();
        navCache.forEach((uri, entry) ->
                new DeclarationIndexer(navDeclarationIndex, uri).scan(entry.ast()));
        System.err.println("[ASTCache] nav index rebuilt: " + navDeclarationIndex.size()
                + " declarations from " + navCache.size() + " files");
    }

    /** Return the declaration location for {@code sym}, or {@code null} if unknown. */
    public SymbolLocation getDeclarationLocation(Symbol sym) {
        // Nav index is built from a single project-wide IAPI — check it first.
        SymbolLocation nav = navDeclarationIndex.get(sym);
        if (nav != null) return nav;
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
        if (!qn.isEmpty() && !navDeclarationIndex.isEmpty()) {
            SymbolLocation match = null;
            boolean ambiguous = false;
            for (Map.Entry<Symbol, SymbolLocation> e : navDeclarationIndex.entrySet()) {
                Symbol s = e.getKey();
                if (qn.equals(s.getQualifiedName().toString())
                        && kind.equals(s.getClass().getSimpleName())
                        && ownerQn.equals(s.owner != null
                                ? s.owner.getQualifiedName().toString() : "")) {
                    if (match != null) { ambiguous = true; break; }
                    match = e.getValue();
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
        navCache.remove(uri);
        navDeclarationIndex.entrySet().removeIf(e -> uri.equals(e.getValue().uri()));
        liveCache.remove(uri);
        removeLiveDeclarationsForUri(uri);
    }

    /**
     * Clear all cached entries and declaration indexes from all tiers.
     * Called by the clear-and-reindex command.
     */
    public void clear() {
        navCache.clear();
        navDeclarationIndex.clear();
        liveCache.clear();
        liveDeclarationIndex.clear();
    }

    // -----------------------------------------------------------------------
    // Iteration
    // -----------------------------------------------------------------------

    /**
     * Iterate over live-tier entries (URI → Entry).
     * Used for operations that require a shared IAPI context (go-to-definition,
     * cross-file references).  Init-tier entries may have been produced by a
     * different IAPI invocation whose Symbol objects are not compatible.
     */
    public void forEach(java.util.function.BiConsumer<String, Entry> action) {
        liveCache.forEach(action);
    }

    /**
     * Iterate over all indexed declarations from both tiers.
     * Nav declarations (from the last project-wide check) take highest priority.
     * Live declarations are included for URIs not covered by the nav cache.
     *
     * <p>Used by {@code workspace/symbol} to search across the entire project.
     */
    public void forEachDeclaration(java.util.function.BiConsumer<Symbol, SymbolLocation> action) {
        // Nav index from project-wide check takes highest priority: consistent symbols.
        navDeclarationIndex.forEach(action);
        // Live index covers files checked individually since the last project-wide check.
        // Skip URIs already covered by the nav index (navCache has those).
        liveDeclarationIndex.forEach((sym, loc) -> {
            if (!navCache.containsKey(loc.uri())) action.accept(sym, loc);
        });
    }

    // -----------------------------------------------------------------------
    // Private helpers
    // -----------------------------------------------------------------------

    private void removeLiveDeclarationsForUri(String uri) {
        liveDeclarationIndex.entrySet().removeIf(e -> uri.equals(e.getValue().uri()));
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
            // Ghost/model symbols have the JML bit set — declared only in JML spec files.
            boolean isJmlSym = org.jmlspecs.openjml.Utils.isJML(sym.flags());
            index.merge(sym, incoming, (existing, in) -> {
                if (isJmlSym) {
                    // Ghost/model: .jml URI wins over .java URI.
                    if (existing.uri().endsWith(".jml")) return existing;
                    if (in.uri().endsWith(".jml"))       return in;
                    return in;  // both .java (inline ghost, no companion): take latest
                } else {
                    // Regular Java: .java wins over .jml spec stub.
                    return !existing.uri().endsWith(".jml") && in.uri().endsWith(".jml")
                            ? existing : in;
                }
            });
        }
    }
}
