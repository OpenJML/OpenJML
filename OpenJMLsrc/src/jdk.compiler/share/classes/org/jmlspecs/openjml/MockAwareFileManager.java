package org.jmlspecs.openjml;

import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.util.Context;
import org.openjml.MockFiles;

import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;
import java.net.URI;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

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
}
