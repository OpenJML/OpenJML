package org.openjml.lsp;

import java.util.List;

/**
 * Per-project configuration record sent by the Eclipse plugin inside the
 * {@code projects} list of {@link ClientSettings}.
 *
 * <p>All path fields use the OS path separator (colon on Unix, semicolon
 * on Windows).  The server builds a per-project {@link OpenJMLSettings}
 * copy from each entry via
 * {@link OpenJMLTextDocumentService#updateProjectSettings}.
 */
public class ProjectConfig {

    /** Eclipse {@code IProject.getName()} — used as the lookup key. */
    public String id;

    /**
     * This project's source folders plus its transitive dependency source
     * folders, passed as {@code -sourcepath}.
     */
    public String sourcePath;

    /**
     * Classpath: JAR libraries (Maven dependencies, external JARs) plus
     * transitive dependency output directories plus any user-configured
     * classpath preference.
     */
    public String classPath;

    /**
     * OpenJML specs path ({@code --specs-path}).  Per-project because the
     * default is derived from {@link #sourcePath}.
     */
    public String specsPath;

    /**
     * OpenJML RAC output directory ({@code -d}).  If empty, the server
     * defaults to {@link #javaOutputDir}.
     */
    public String racOutputDir;

    /**
     * The IDE's Java compiler output directory.  Goes on the classpath so
     * OpenJML can see already-compiled classes.  Also used as the default
     * {@code -d} when {@link #racOutputDir} is empty.
     */
    public String javaOutputDir;

    /**
     * This project's own source folders only (not dependency sources).
     * Used by the server to map a file URI to its owning project.
     */
    public List<String> rootPaths;
}
