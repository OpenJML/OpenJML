package org.openjml;
import java.net.URI;

import javax.tools.JavaFileObject;
import javax.tools.SimpleJavaFileObject;

import org.jmlspecs.openjml.Utils;

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
     * only make one of these for a given filename per compilation context 
     * We don't try to recover gracefully if the exception occurs - this is
     * primarily used in testing anyway. */
    private static URI makeURI(String filename) {
        try {
            return new URI("file:///" + filename);
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
        super(uri,uri.getPath().endsWith(".java") ? Kind.SOURCE : Kind.OTHER);
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
    
    /** Returns true if the receiver and argument represent the same file */
    public boolean equals(Object o) {
        if (!(o instanceof JavaFileObject jfo)) return false;
        return Utils.ifFilepathsEqual(this, jfo);
    }
    
    /** A definition of hashCode, since we have a definition of equals */
    public int hashCode() {
        // Two things are equal if they have the same string, so we'll
        // use that for the hashCode
        return uri.normalize().getPath().hashCode();
        // FIXME -0 this is not right, since if one is a suffix of the other they are equal and should have the same hashCode
    }
    
    public String toString() {
        // Notes that super.toString() produces something like file:///tt/TestJava.java from TestJavaFileObject
        return getName();  // Something like tt/TestJava.java
    }

}

