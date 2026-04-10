package org.jmlspecs.openjml;

import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.util.Context;
import org.openjml.MockFiles;

import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

/**
 * A {@link JavacFileManager} subclass that serves in-memory mock content for
 * registered URIs instead of reading files from disk.
 *
 * <p>When {@code mockFiles} contains no URI-keyed entries the behaviour is
 * identical to the standard {@code JavacFileManager} - there is no overhead
 * for normal (non-mock) compilation.
 *
 * <p>Registration: call {@link #preRegister(Context)} in place of
 * {@code JavacFileManager.preRegister(context)}.  The factory lazily reads
 * {@code mockFiles} from the {@link Main} instance already stored in the
 * context, so mock content set before compilation begins is picked up
 * automatically.
 */
public class MockAwareFileManager extends JavacFileManager {

    private final MockFiles mockFiles;

    private MockAwareFileManager(Context context, MockFiles mockFiles) {
        super(context, true, null);
        this.mockFiles = mockFiles;
    }

    /**
     * Register a factory in the context that lazily reads {@code mockFiles}
     * from the {@link Main} stored in the context at file-manager instantiation
     * time.  Call this in place of {@code JavacFileManager.preRegister(context)}.
     */
    public static void preRegister(Context context) {
        context.put(JavaFileManager.class, (Context.Factory<JavaFileManager>) c -> {
            Main main = c.get(Main.key);
            if (main == null) throw new JmlInternalAbort(
                    "MockAwareFileManager: Main not found in context - internal error");
            return new MockAwareFileManager(c, main.mockFiles);
        });
    }

    /**
     * Override {@link JavacFileManager#getJavaFileObjectsFromPaths}: for each
     * path that has a matching URI-keyed mock, substitute the mock in place of
     * the disk-backed {@code PathFileObject}.  Paths without a mock are
     * handled by the parent implementation unchanged.
     */
    @Override
    public Iterable<? extends JavaFileObject> getJavaFileObjectsFromPaths(
            Collection<? extends Path> paths) {
        if (!mockFiles.hasUriEntries()) return super.getJavaFileObjectsFromPaths(paths);

        // Let the parent build disk-backed objects for all paths, then replace
        // those whose normalized URI has a registered mock.
        Iterable<? extends JavaFileObject> superResult =
                super.getJavaFileObjectsFromPaths(paths);
        List<JavaFileObject> result = new ArrayList<>();
        Iterator<? extends JavaFileObject> superIt = superResult.iterator();
        for (Path p : paths) {
            JavaFileObject superJfo = superIt.next();
            URI normalized = p.toUri().normalize();
            JavaFileObject mock = mockFiles.getByUri(normalized);
            result.add(mock != null ? mock : superJfo);
        }
        return result;
    }

    /**
     * Override {@link JavacFileManager#list}: for each file returned by the
     * parent implementation, substitute any registered mock whose normalized
     * URI matches.  This ensures that dirty in-memory files (registered via
     * {@link MockFiles#addMockByUri}) are served instead of their on-disk
     * counterparts when the compiler resolves cross-file references via the
     * source path (e.g., when compiling B.java that imports A, where A.java
     * is open in an editor with unsaved changes).
     */
    @Override
    public Iterable<JavaFileObject> list(Location location, String packageName,
                                         Set<JavaFileObject.Kind> kinds, boolean recurse)
            throws IOException {
        Iterable<JavaFileObject> superResult = super.list(location, packageName, kinds, recurse);
        if (!mockFiles.hasUriEntries()) return superResult;

        List<JavaFileObject> result = new ArrayList<>();
        for (JavaFileObject jfo : superResult) {
            URI normalized = jfo.toUri().normalize();
            JavaFileObject mock = mockFiles.getByUri(normalized);
            result.add(mock != null ? mock : jfo);
        }
        return result;
    }

    /**
     * Override {@link JavacFileManager#inferBinaryName}: handle
     * {@link org.openjml.MockJavaFileObject} instances returned by {@link #list}.
     * The parent implementation only handles its own {@code PathFileObject} type
     * and throws {@link IllegalArgumentException} for anything else.
     *
     * <p>The binary name is derived by finding the location root that is a
     * prefix of the mock's URI path, stripping that prefix, removing the file
     * extension, and replacing {@code '/'} with {@code '.'}.
     */
    /**
     * Override {@link JavacFileManager#inferBinaryName}: the parent only handles
     * its own {@code PathFileObject} type and throws {@link IllegalArgumentException}
     * for anything else.  The computation is purely name-based: strip the location
     * root prefix from the file's URI path, remove the extension, replace {@code '/'}
     * with {@code '.'}.  We delegate to the parent for its own types and do the
     * URI arithmetic ourselves for everything else (e.g. {@link org.openjml.MockJavaFileObject}).
     */
    @Override
    public String inferBinaryName(Location location, JavaFileObject file) {
        try {
            return super.inferBinaryName(location, file);
        } catch (IllegalArgumentException e) {
            // Parent can't handle this file type - compute from URI.
        }
        String filePath = file.toUri().normalize().getPath();
        Iterable<? extends Path> roots = getLocationAsPaths(location);
        if (roots != null) {
            for (Path root : roots) {
                String rootPath = root.toUri().normalize().getPath();
                if (!rootPath.endsWith("/")) rootPath += "/";
                if (filePath.startsWith(rootPath)) {
                    String relative = filePath.substring(rootPath.length());
                    int dot = relative.lastIndexOf('.');
                    if (dot >= 0) relative = relative.substring(0, dot);
                    return relative.replace('/', '.');
                }
            }
        }
        // Fallback: simple name without extension or path
        String name = file.getName();
        int slash = name.lastIndexOf('/');
        if (slash >= 0) name = name.substring(slash + 1);
        int dot = name.lastIndexOf('.');
        if (dot >= 0) name = name.substring(0, dot);
        return name;
    }
}
