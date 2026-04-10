package org.openjml;
import java.net.URI;
import java.nio.file.Path;

import javax.tools.JavaFileObject;
import javax.tools.SimpleJavaFileObject;

/** This class makes a mock JavaFileObject.  It holds a String as its content
 * and is given a pseudo-filename to use, but does not represent an actual file in 
 * the file system. 
 * <P>
 * Note that we use Kind.OTHER to designate specification (non-.java) files.
 * 
 * @author David Cok
 */
public class MockJavaFileObject extends SimpleJavaFileObject {
    
    /** The content of the mock file */
    //@ non_null
    protected String content;
    
    /** A fake file name, used when the user does not want to be bothered
     * supplying one.  We make and cache this because it is a pain to
     * deal with exceptions in constructors.
     */
    //@ non_null
    static final protected URI uritest = makeURI();
    
    /** A utility method to make the URI, so it can handle the exceptions;
     * only make one of these (as it has a fixed filename) per compilation context 
     * We don't try to recover gracefully if the exception occurs - this is
     * primarily used in testing anyway. */
    private static URI makeURI() {
        try {
            return new URI("file:///TEST.java");
        } catch (Exception e) {
            // If this exception is ever thrown, the TestJavaFileObject class will fail to be instantiated,
            // aborting tests and any execution of openjml on startup.
            throw new com.sun.tools.javac.util.PropagatedException(new org.jmlspecs.openjml.JmlInternalAbort("Failed to construct a mock URI in TestJavaFileObject.makeURI"));
        }
    }

    /** A utility method to make a URI, so it can handle the exceptions;
     * only make one of these for a given filename per compilation context.
     * For absolute paths, delegates to {@link Path#toUri()} which handles
     * spaces and the correct number of slashes.  For relative paths (typical
     * in test code), prepends {@code file:///} directly so that the resulting
     * URI path matches the filename string exactly (e.g. {@code /A.java}).
     */
    private static URI makeURI(String filename) {
        try {
            Path p = Path.of(filename);
            if (p.isAbsolute()) return p.toUri();
            return new URI("file:///" + filename).normalize();
        } catch (Exception e) {
            // If this exception is ever thrown, the TestJavaFileObject class will fail to be instantiated,
            // aborting tests and any execution of openjml on startup.
            throw new com.sun.tools.javac.util.PropagatedException(new org.jmlspecs.openjml.JmlInternalAbort("Failed to construct a mock URI in TestJavaFileObject.makeURI"));
        }
    }


    /** A constructor of a JavaFileObject of kind SOURCE,
     * with the given content and a made-up file name.
     * Only make one of these per compilation context, because it has a fixed filename
     * @param s The content of the file
     */
    public MockJavaFileObject(/*@ non_null */ String content) {
        super(uritest,Kind.SOURCE);
        this.content = content;
    }

    /** Constructs a new JavaFileObject of kind SOURCE or OTHER depending on the
     * filename extension
     * @param filename the filename to use (no leading slash) (null indicates to
     *          use the internal fabricated filename)
     * @param content the content of the pseudo file
     * @throws Exception if a URI cannot be created
     */
    public MockJavaFileObject(/*@ non_null */String filename, /*@ non_null */String content) {
        super(filename == null ? uritest : makeURI(filename),
                filename == null || filename.endsWith(".java") ? Kind.SOURCE : Kind.OTHER);
        this.content = content;
    }

    /** Constructs a new JavaFileObject
     * @param uri the URI to use
     * @param content the content of the pseudo file
     */
    public MockJavaFileObject(/*@ non_null */URI uri, /*@ non_null */String content) {
        super(uri.normalize(), uri.getPath().endsWith(".java") ? Kind.SOURCE : Kind.OTHER);
        this.content = content;
    }

    /** Overrides the parent to provide the content directly from the String
     * supplied at construction, rather than reading the file.  This is called
     * by the system.
     */
    @Override
    public CharSequence getCharContent(boolean ignoreEncodingErrors) {
        return content;
    }

    /**
     * Returns {@link Long#MAX_VALUE} so that this mock is always considered
     * newer than any on-disk class file ({@code .class}) the compiler might
     * find on the class path.
     *
     * <p>{@link javax.tools.SimpleJavaFileObject#getLastModified()} returns
     * {@code 0L}.  When javac resolves a type that has both a source file on
     * the source path and a compiled class file on the class path, it picks
     * whichever is newer.  A mock with modification time {@code 0} would
     * always lose to a real class file, causing javac to use the (possibly
     * stale) class file instead of the in-memory mock source - leading to
     * "symbol not found" errors after a rename when the class files have not
     * yet been recompiled.  Returning {@code Long.MAX_VALUE} ensures the mock
     * is always preferred.
     */
    @Override
    public long getLastModified() {
        return Long.MAX_VALUE;
    }
    
//    /** Overrides the parent method to allow name compatibility between 
//     * pseudo files of different kinds.  TODO _ better description of what the system uses this for
//     */
//    // Don't worry about whether the kinds match, just the file prefix
//    @Override
//    public boolean isNameCompatible(String simpleName, Kind kind) {
//        String s = uri.getPath();
//        if (kind == Kind.OTHER) {
//            int i = s.lastIndexOf('/');  // FIXME - is this branch ever used?
//            s = s.substring(i+1);
//            return s.startsWith(simpleName);
//        } else {
//            String baseName = simpleName + kind.extension;
//            return s.endsWith("/" + baseName);
//        }
//    }
    
    /** Returns true if the receiver and argument represent the same file.
     * The stored URI is always normalized (see constructors), so only the
     * other side needs normalizing to handle callers that do not normalize. */
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof JavaFileObject jfo)) return false;
        return toUri().equals(jfo.toUri().normalize());
    }

    /** Hash code consistent with {@link #equals}: the stored URI is normalized,
     * so no extra {@code normalize()} call is needed here. */
    @Override
    public int hashCode() {
        return toUri().hashCode();
    }
    
    public String toString() {
        // Notes that super.toString() produces something like file:///tt/TestJava.java from TestJavaFileObject
        return getName();  // Something like tt/TestJava.java
    }

}

