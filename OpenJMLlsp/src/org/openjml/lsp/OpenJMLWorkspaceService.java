package org.openjml.lsp;

import org.eclipse.lsp4j.DidChangeConfigurationParams;
import org.eclipse.lsp4j.DidChangeWatchedFilesParams;
import org.eclipse.lsp4j.services.WorkspaceService;

/**
 * Handles LSP workspace-level notifications (configuration changes, watched-file
 * events).  No workspace features are implemented in the initial phase.
 *
 * Future additions: respond to {@code workspace/didChangeConfiguration} to
 * pick up user-configured specs-path, solvers-path, and ESC options.
 */
public class OpenJMLWorkspaceService implements WorkspaceService {

    @Override
    public void didChangeConfiguration(DidChangeConfigurationParams params) {}

    @Override
    public void didChangeWatchedFiles(DidChangeWatchedFilesParams params) {}
}
