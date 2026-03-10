package org.openjml.lsp;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

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

    /** Cached entry for one source file. */
    public record Entry(JmlCompilationUnit ast, Context context) {}

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
     * and remove any init-tier entry for the same URI.
     * Called from the IAPI.IASTListener — may fire multiple times per source
     * file when the file contains multiple classes.
     */
    public void put(String uri, Context ctx, JmlCompilationUnit ast) {
        removeLiveDeclarationsForUri(uri);
        liveCache.put(uri, new Entry(ast, ctx));
        new DeclarationIndexer(liveDeclarationIndex, uri).scan(ast);

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
        initCache.put(uri, new Entry(ast, ctx));
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
        return live != null ? live : initDeclarationIndex.get(sym);
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
            if (tree.sym != null && tree.pos >= 0)
                index.put(tree.sym, new SymbolLocation(uri, tree.pos));
            super.visitClassDef(tree);
        }

        @Override
        public void visitMethodDef(JCMethodDecl tree) {
            if (tree.sym != null && tree.pos >= 0)
                index.put(tree.sym, new SymbolLocation(uri, tree.pos));
            super.visitMethodDef(tree);
        }

        @Override
        public void visitVarDef(JCVariableDecl tree) {
            if (tree.sym != null && tree.pos >= 0)
                index.put(tree.sym, new SymbolLocation(uri, tree.pos));
            super.visitVarDef(tree);
        }
    }
}
