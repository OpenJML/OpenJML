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

/**
 * Caches the latest type-attributed AST for each open document URI.
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

    /** Cached entry for one source file. */
    public record Entry(JmlCompilationUnit ast, Context context) {}

    /** URI → latest attributed AST entry. */
    private final Map<String, Entry> cache = new ConcurrentHashMap<>();

    /**
     * Cross-file Symbol → declaration location index.
     * Uses object identity (Symbol does not override equals/hashCode), which is
     * correct: within one IAPI invocation, declaration and use-site nodes share
     * the same Symbol instances.
     */
    private final Map<Symbol, SymbolLocation> declarationIndex = new ConcurrentHashMap<>();

    /**
     * Store (or overwrite) the AST for {@code uri} and re-index its declarations.
     * Called from the IAPI.IASTListener — may fire multiple times per source
     * file when the file contains multiple classes.
     */
    public void put(String uri, Context ctx, JmlCompilationUnit ast) {
        removeDeclarationsForUri(uri);
        cache.put(uri, new Entry(ast, ctx));
        new DeclarationIndexer(uri).scan(ast);
    }

    /** Return the cached entry for {@code uri}, or {@code null} if absent. */
    public Entry get(String uri) {
        return cache.get(uri);
    }

    /** Remove the cached entry and its indexed declarations (e.g. on didClose). */
    public void remove(String uri) {
        cache.remove(uri);
        removeDeclarationsForUri(uri);
    }

    /** Return the declaration location for {@code sym}, or {@code null} if unknown. */
    public SymbolLocation getDeclarationLocation(Symbol sym) {
        return declarationIndex.get(sym);
    }

    /** Iterate over all cached entries (URI → Entry). */
    public void forEach(java.util.function.BiConsumer<String, Entry> action) {
        cache.forEach(action);
    }

    // -----------------------------------------------------------------------
    // Private helpers
    // -----------------------------------------------------------------------

    private void removeDeclarationsForUri(String uri) {
        declarationIndex.entrySet().removeIf(e -> uri.equals(e.getValue().uri()));
    }

    private class DeclarationIndexer extends JmlTreeScanner {
        private final String uri;

        DeclarationIndexer(String uri) { this.uri = uri; }

        @Override
        public void visitClassDef(JCClassDecl tree) {
            if (tree.sym != null && tree.pos >= 0)
                declarationIndex.put(tree.sym, new SymbolLocation(uri, tree.pos));
            super.visitClassDef(tree);
        }

        @Override
        public void visitMethodDef(JCMethodDecl tree) {
            if (tree.sym != null && tree.pos >= 0)
                declarationIndex.put(tree.sym, new SymbolLocation(uri, tree.pos));
            super.visitMethodDef(tree);
        }

        @Override
        public void visitVarDef(JCVariableDecl tree) {
            if (tree.sym != null && tree.pos >= 0)
                declarationIndex.put(tree.sym, new SymbolLocation(uri, tree.pos));
            super.visitVarDef(tree);
        }
    }
}
