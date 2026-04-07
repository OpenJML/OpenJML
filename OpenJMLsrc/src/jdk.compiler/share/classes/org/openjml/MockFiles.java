package org.openjml;

import java.io.*;

import com.sun.tools.javac.file.JavacFileManager;
import javax.tools.JavaFileObject;
import com.sun.tools.javac.file.RelativePath;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;
import java.util.*;
import com.sun.tools.javac.util.Context;


/** This class holds MockFiles. As it does not intend to hold very many, the
 * files are recorded in a Map that maps full (mock) path name to JavaFileObject.
 * Instances of the class org.openjml.MockJavaFileObject can be used as
 * mock files.
 * <p>
 * A second map keyed by normalized URI supports file-manager interception:
 * when a real filesystem path (on the javac command line) has a corresponding
 * mock URI entry, the file manager returns the mock instead of reading disk.
 */
public class MockFiles {

    Map<String, JavaFileObject> map = new HashMap<>();

    /** Secondary map keyed by normalized URI for file-manager interception.
     * Use {@link #addMockByUri} / {@link #getByUri} to populate and query. */
    private Map<java.net.URI, JavaFileObject> uriMap = new HashMap<>();

    public void addMockFile(String filename, JavaFileObject file) {
        map.put(filename, file);
    }

    public JavaFileObject get(String filename) {
        return map.get(filename);
    }

    /** Register a mock by its normalized real-file URI so that
     * {@link MockAwareFileManager} can intercept file-system reads for that path. */
    public void addMockByUri(java.net.URI normalizedUri, JavaFileObject file) {
        uriMap.put(normalizedUri, file);
    }

    /** Return the mock registered for {@code normalizedUri}, or {@code null}. */
    public JavaFileObject getByUri(java.net.URI normalizedUri) {
        return uriMap.get(normalizedUri);
    }

    /** True when at least one URI-keyed mock has been registered. */
    public boolean hasUriEntries() {
        return !uriMap.isEmpty();
    }

    public boolean isEmpty() {
        return map.isEmpty() && uriMap.isEmpty();
    }

    public void clear() {
        map.clear();
        uriMap.clear();
    }

    /** Creates a new MockFileTree that belongs to the given context;
     * a context may have more than one MockFileTree.
     */
    public MockFiles() {
    }

}
