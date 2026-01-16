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
 */
public class MockFiles {
    
    Map<String, JavaFileObject> map = new HashMap<>();

    public void addMockFile(String filename, JavaFileObject file) {
        map.put(filename, file);
    }
    
    public JavaFileObject get(String filename) {
        return map.get(filename);
    }
    
    public boolean isEmpty() {
        return map.isEmpty();
    }
    
    public void clear() {
        map.clear();
    }

    /** Creates a new MockFileTree that belongs to the given context;
     * a context may have more than one MockFileTree.
     */
    public MockFiles() {
    }

}
