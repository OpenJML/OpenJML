package org.openjml.lsp.test;

import org.eclipse.lsp4j.FileChangeType;
import org.junit.Test;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;
import org.openjml.lsp.OpenJMLTextDocumentService;

import static org.junit.Assert.*;

/**
 * Tests for the watched-file handler methods in
 * {@link OpenJMLTextDocumentService}.
 *
 * <ul>
 *   <li>{@code handleWatchedJavaChange(DELETED)} clears the AST cache entry.</li>
 *   <li>{@code handleWatchedJmlChange(DELETED)} clears the spec AST cache entry.</li>
 * </ul>
 */
public class WatchedFilesHandlerTest {

    // -----------------------------------------------------------------------
    // handleWatchedJavaChange — Deleted clears AST cache
    // -----------------------------------------------------------------------

    @Test
    public void handleWatchedJavaChangeDeletedClearsAstCache() {
        String uri = "file:///WFH_JavaDeleted.java";

        // Populate the AST cache.
        CheckRunner.check(uri, "public class WFH_JavaDeleted {}");
        assertNotNull("Pre-condition: AST cache must have an entry after check",
                CheckRunner.getASTCache().get(uri));

        // No LSP client — service constructed without one; delete path does not need it.
        OpenJMLTextDocumentService svc =
                new OpenJMLTextDocumentService(new OpenJMLSettings(), null);

        svc.handleWatchedJavaChange(uri, FileChangeType.Deleted);

        assertNull("AST cache entry must be cleared after Deleted event",
                CheckRunner.getASTCache().get(uri));
    }

    // -----------------------------------------------------------------------
    // handleWatchedJmlChange — Deleted clears AST cache for spec file
    // -----------------------------------------------------------------------

    @Test
    public void handleWatchedJmlChangeDeletedClearsAstCache() {
        // Use a .java URI to populate the cache with a real AST, then re-key it
        // under a .jml URI to simulate a spec-file cache entry.
        String javaUri = "file:///WFH_JmlDeleted_helper.java";
        String jmlUri  = "file:///WFH_JmlDeleted.jml";

        CheckRunner.check(javaUri, "public class WFH_JmlDeleted_helper {}");
        ASTCache.Entry entry = CheckRunner.getASTCache().get(javaUri);
        assertNotNull("Pre-condition: helper .java entry must be in cache", entry);

        // Store a cache entry under the .jml URI (simulates spec-file indexing).
        ASTCache cache = CheckRunner.getASTCache();
        cache.put(jmlUri, entry.context(), entry.ast());
        assertNotNull("Pre-condition: .jml entry must be in cache after manual put",
                cache.get(jmlUri));

        // Service without a client; delete path does not publish diagnostics when
        // client is null.
        OpenJMLTextDocumentService svc =
                new OpenJMLTextDocumentService(new OpenJMLSettings(), null);

        svc.handleWatchedJmlChange(jmlUri, FileChangeType.Deleted);

        assertNull("AST cache entry for .jml must be cleared after Deleted event",
                cache.get(jmlUri));
    }
}
