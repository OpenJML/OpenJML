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
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * Caches the latest type-attributed AST for each open document URI.
 *
 * <p>Maintains two tiers:
 * <ul>
 *   <li><b>Live cache</b> — populated by user-triggered {@code --check} / {@code --esc} runs.
 *       Always takes precedence over the init cache.</li>
 *   <li><b>Init cache</b> — populated by the background workspace-index pass that runs
 *       once after the LSP {@code initialized} handshake.  An entry is skipped when the
 *       same URI already has a live entry.</li>
 * </ul>
 *
 * <p>Populated by {@link CheckRunner} via the {@code IAPI.IASTListener} callback
 * after each {@code --check} or {@code --esc} run.
 *
 * <p>Because {@code JmlCompiler.attribute()} fires one notification <em>per
 * class</em> (not per compilation unit), files containing multiple classes
 * receive multiple notifications.  Only the <em>last</em> notification for a
 * given source file has fully-resolved symbols for the whole compilation unit.
 * {@link #put} and {@link #putInit} always overwrite, so the cache converges
 * to the correct state.
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
     * Init-tier entries (background workspace index) always have them null.
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
    // Init tier — background workspace-index pass
    // -----------------------------------------------------------------------

    /** URI → attributed AST from the background workspace index. */
    private final Map<String, Entry> initCache = new ConcurrentHashMap<>();

    /** Cross-file Symbol → declaration location from the background index. */
    private final Map<Symbol, SymbolLocation> initDeclarationIndex = new ConcurrentHashMap<>();

    /** {@code true} while the background workspace index is running. */
    private final AtomicBoolean indexing = new AtomicBoolean(false);

    // -----------------------------------------------------------------------
    // Indexing state
    // -----------------------------------------------------------------------

    /** Set the indexing-in-progress flag (called by {@link CheckRunner}). */
    public void setIndexing(boolean value) { indexing.set(value); }

    /** Return {@code true} while the background workspace index is still running. */
    public boolean isIndexing() { return indexing.get(); }

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
        // Init-tier entries for this URI are now superseded by the live entry.
        initCache.remove(uri);
        removeInitDeclarationsForUri(uri);
    }

    // -----------------------------------------------------------------------
    // Init-tier writes
    // -----------------------------------------------------------------------

    /**
     * Store the AST for {@code uri} in the <em>init</em> tier.
     * Skipped if a live-tier entry already exists for {@code uri}.
     * Called from the background workspace-index pass.
     */
    public void putInit(String uri, Context ctx, JmlCompilationUnit ast) {
        if (liveCache.containsKey(uri)) return;   // live takes precedence
        removeInitDeclarationsForUri(uri);
        Entry entry = Entry.basic(ast, ctx);
        initCache.put(uri, entry);
        new DeclarationIndexer(initDeclarationIndex, uri).scan(ast);
    }

    // -----------------------------------------------------------------------
    // Reads
    // -----------------------------------------------------------------------

    /**
     * Return the cached entry for {@code uri}.
     * Live tier is checked first; init tier is used as fallback.
     * Returns {@code null} if absent from both tiers.
     */
    public Entry get(String uri) {
        Entry live = liveCache.get(uri);
        return live != null ? live : initCache.get(uri);
    }

    /** Return the declaration location for {@code sym}, or {@code null} if unknown. */
    public SymbolLocation getDeclarationLocation(Symbol sym) {
        SymbolLocation live = liveDeclarationIndex.get(sym);
        SymbolLocation result = live != null ? live : initDeclarationIndex.get(sym);
        System.err.println("[ASTCache.lookup] " + sym.getQualifiedName()
                + " -> " + (result == null ? "NOT FOUND (liveSize=" + liveDeclarationIndex.size()
                        + " initSize=" + initDeclarationIndex.size() + ")"
                        : result.uri().replaceAll(".*/", "") + "@" + result.charOffset()));
        return result;
    }

    // -----------------------------------------------------------------------
    // Removals
    // -----------------------------------------------------------------------

    /** Remove the cached entry and its indexed declarations from both tiers (e.g. on didClose). */
    public void remove(String uri) {
        liveCache.remove(uri);
        removeLiveDeclarationsForUri(uri);
        initCache.remove(uri);
        removeInitDeclarationsForUri(uri);
    }

    /**
     * Clear all cached entries and declaration indexes from both tiers.
     * Resets the indexing flag.  Called by the clear-and-reindex command.
     */
    public void clear() {
        liveCache.clear();
        liveDeclarationIndex.clear();
        initCache.clear();
        initDeclarationIndex.clear();
        indexing.set(false);
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
     * Live declarations are always included.  Init declarations are included only
     * for URIs that do not have a live cache entry (i.e. the user has not yet
     * opened or checked those files).
     *
     * <p>Used by {@code workspace/symbol} to search across the entire project.
     */
    public void forEachDeclaration(java.util.function.BiConsumer<Symbol, SymbolLocation> action) {
        liveDeclarationIndex.forEach(action);
        initDeclarationIndex.forEach((sym, loc) -> {
            // Skip init entries for URIs that have a live cache entry — the live
            // declaration index already covers those files.
            if (!liveCache.containsKey(loc.uri())) action.accept(sym, loc);
        });
    }

    // -----------------------------------------------------------------------
    // Private helpers
    // -----------------------------------------------------------------------

    private void removeLiveDeclarationsForUri(String uri) {
        liveDeclarationIndex.entrySet().removeIf(e -> uri.equals(e.getValue().uri()));
    }

    private void removeInitDeclarationsForUri(String uri) {
        initDeclarationIndex.entrySet().removeIf(e -> uri.equals(e.getValue().uri()));
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
         * <p>Preference rule: a {@code .java} declaration is never overwritten by
         * a {@code .jml} spec stub for the same symbol.  Ghost/model symbols never
         * reach this method for a {@code .java} CU (filtered by
         * {@link #skipJmlNodeInJavaCu}), so they are always recorded under the
         * real {@code .jml} URI from the companion AST scan.
         */
        private void record(Symbol sym, int pos) {
            SymbolLocation incoming = new SymbolLocation(uri, pos);
            index.merge(sym, incoming,
                    (existing, in) -> !existing.uri().endsWith(".jml") && in.uri().endsWith(".jml")
                            ? existing   // keep .java over .jml spec stub
                            : in);       // otherwise take the latest
            String stored = index.get(sym).uri();
            System.err.println("[ASTCache] " + sym.getQualifiedName() + "@" + pos
                    + " -> " + stored.replaceAll(".*/", ""));
        }
    }
}
