package org.jmlspecs.openjml;

import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.file.RelativePath;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;
import com.sun.tools.javac.util.Context;

import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;
import java.io.*;

/** An abstract class representing a directory element of the specs path. */
// These classes are kept separate from JmlSpecs and from Context so that they
// can be used without problem by JmlTestSUite and the various test suites.
// For one thing, it helps prevent premature instantiation of JmlSpecs and
// any other context-dependent tool components.
abstract public class Dir {
    
    /** The human-readable name of the directory */
    protected String name;
    
    /** Returns the human-readable name of the directory
     * @return Returns the human-readable name of the directory
     */
    public String name() { return name; }

    
    /** Returns the human-readable name of the directory
     * @return Returns the human-readable name of the directory
     */
    public String toString() { return name; }
    
    /** Returns whether the directory actually exists
     * @return Returns whether the directory actually exists
     */
    abstract boolean exists();
    
    
    /** Finds a file with the given path (relative directory, name and
     * suffix) is present in this directory
     * @return a JavaFileObject for that file
     */
    abstract public /*@Nullable*/JavaFileObject findFile(String filePath, Context context);


    /** This class handles mock directories - data that appear to be files
     * within directories but do not actually exist in the file system.
     */
    public static class MockDir extends Dir {
        
        /** Constructs a mock directory object
         * @param dirName the path to use for the directory object 
         */
        public MockDir(String dirName) {
            this.name = dirName;
        }
        
        /** Mock directory objects always exist */
        @Override
        public boolean exists() {
            return true;
        }
        
        @Override
        public /*@Nullable*/JavaFileObject findFile(String filePath, Context context) { 
            String ss = name + "/" + filePath;
            var main = context.get(Main.key);
            if (main.mockFiles == null) return null;
            JavaFileObject j = main.mockFiles.get(ss);
            return j;
//            return JmlSpecs.instance(context).mockFiles.get(ss);
        }
    }
    
    /** This class represents conventional file system directories */
    public static class FileSystemDir extends Dir {
        /** The java.io.File object for the directory */
        protected File dir;
        
        /** Creates a Dir object for the given directory; the existence of a
         * Dir object does not mean that the underlying directory actually
         * exists
         * @param dirName the relative or absolute path to the directory
         */
        public FileSystemDir(String dirName) {
            this.name = dirName;
            this.dir = new File(dirName);
        }
        
        public FileSystemDir(File dir) {
            this.name = dir.getName();
            this.dir = dir;
        }
        
        @Override
        public boolean exists() {
            return dir.exists() && dir.isDirectory();
        }

        @Override
        public /*@Nullable*/JavaFileObject findFile(String filePath, Context context) {
            File f = new File(dir,filePath);
            if (f.exists()) {
                //return context.get(JavacFileManager.class).getJavaFileObject(f.toPath());
                return new JavacFileManager(context,false,null).getJavaFileObject(f.toPath());
            }
            return null;
        }
    }
    
    /** This class represents .jar (and .zip) files and subdirectories within them */
    public static class JarDir extends Dir {
        /** An object holding the path to the archive file (which may not actually
         * exist)
         */
        protected ZipFile zipArchive;
        
        /** The subdirectory within the archive, with a trailing slash added to
         * the name, or an empty string if the directory desired is the top-level
         * of the archive.
         */
        protected String internalDirSlash;
        
        /** The directory path within the jar file */
        protected RelativePath.RelativeDirectory internalDir;
        
        /** Creates a Dir object representing the content or a subdirectory of
         * a Jar file.
         * @param zip the absolute or relative path to the jar file itself
         * @param name the subdirectory within the jar file (or an empty string
         * if the top-level is desired, not null)
         */
        public JarDir(String zip, String name) {
             try {
                this.zipArchive = new ZipFile(zip);
            } catch (IOException e) {
                this.zipArchive = null;
            }
            this.internalDir = new RelativePath.RelativeDirectory(name);
            this.internalDirSlash = name.length() == 0 ? name : (name + "/");
            this.name = zip + (name.length() == 0 ? name : ("!" + name));
        }
        
        @Override
        public boolean exists() {
            if (zipArchive == null) return false;
            var iter = zipArchive.entries();
            while (iter.hasMoreElements()) {
                if (name.length() == 0) return true;
                // TODO - check that this works correctly // use contains?
                if (iter.nextElement().getName().startsWith(internalDir.getPath())) return true;
            }
            return false;
        }
        
        @Override
        public /*@Nullable*/JavaFileObject findFile(String filePath, Context context) { 
            RelativePath file = new RelativePath.RelativeFile(internalDir,filePath);
            if (zipArchive == null) return null;
            ZipEntry entry = zipArchive.getEntry(file.toString());
            if (entry == null) return null;
            // FIXME return zipArchive.getFileObject(internalDir,filePath);
            return null;
        }
    }
}
