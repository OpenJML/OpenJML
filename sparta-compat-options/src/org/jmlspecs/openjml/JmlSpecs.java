/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

// TODO:
// - document
// - cleanup desugared specs
// - clean up constructors and details of TypeSpecs
// - clean up pretty printing and toString for debugging
// - fix use of ZipArchive subdirectories

import java.io.File;
import java.io.IOException;
import java.io.StringWriter;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipFile;

import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;

import org.eclipse.core.runtime.Platform;
import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignalsOnly;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;
import org.osgi.framework.Bundle;

import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.file.RelativePath;
import com.sun.tools.javac.file.ZipArchive;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;

/** This class manages the specifications of various Java entities
 * during a compilation.  There should be just one instance of JmlSpecs
 * per compilation Context, ensured by calling the preRegister
 * method.  The class provides methods for finding specification files, and it
 * maintains a database of specifications of types, methods, and fields.  
 * The specs are indexed by type 
 * as well as by method, so that obsolete specs can be readily discarded.
 * <P>
 * <B>Specification Paths</B>
 * The specification path is a sequence of directories or analogous locations
 * of files.  Just as the classpath
 * is used by Java to find the classes referenced in a program, the specs path
 * is used to find specification files.  There are a few enhancements on this
 * simple concept:
 * <UL>
 * <LI>1) ordinarily the specsPath is specified on the command-line as the option 
 * of -specspath</LI>
 * <LI>2) if there is no command-line argument, the value of the environment property 
 * org.jmlspecs.specspath is used</LI>
 * <LI>3) if that is not defined, the value of the sourcepath is used (specified 
 * by the -sourcepath command-line option or properties)</LI>
 * <LI>4) if that is not defined, the value of the classpath is used</LI>
 * is used (the -classpath option, if it is specified, or the java.class.path
 * environment property)</LI>
 * <LI>5) the string representing a directory may be a relative or absolute path</LI>
 * <LI>6) the string representing a directory may be a jar or zip file or a
 * directory within a jar or zip file, specified by using a ! to separate the
 * path to the jar file from the internal directory path, e.g. a/b/specs.jar!d/e
 * <LI>7) the string representing a directory may consist of a variable reference that
 * is replaced by a system dependent string.  The following are defined:
 * <UL>
 * <LI>     $CP - expanded to be the directories of the classpath</LI>
 * <LI>     $ECP - expanded to be the content of java.class.path</LI>
 * <LI>     $SP - expanded to be the directories of the sourcepath</LI>
 * <LI>     $SY - expanded to be the directories containing specifications
 *                  of the java system files, either the value of the 
 *                  environmental property org.jmlspecs.system.specs or, if
 *                  that is not set, an internal value corresponding to the
 *                  location of specs shipped with the tool </LI>
 * </UL>
 * </UL>
 * In addition, by default, the specs path has $SY appended to it (unless 
 * disabled with -noInternalSpecs); the classpath has the internal runtime
 * library appended to it (unless disabled with -noInternalRuntime).
 * 
 * <P>
 * <B>Mock files</B>
 * Especially for testing, but perhaps also in other contexts, it is useful to be
 * able to pretend that there is a file with some content at a given location,
 * without the file actually being present in the file system.  This can be
 * accomplished using mock file objects.  This tool handles files abstractly as
 * instances of JavaFileObject.  One can create an instance of a derived class,
 * a MockJavaFileObject, which has a name and a String as content (which should 
 * look like the text of a compilation unit), but which does not actually exist as a file.
 * The name does however have to look like a legitimate path name, with a 
 * directory, a fully-qualified package directory path, and the class file name.
 * The initial directory must be on the specspath.  For that purpose, mock
 * directory names are allowed on the specspath.  These are arbitrary names,
 * beginning with $(==Utils.mockDirChar), which are then listed as directories 
 * on the specspath and
 * used as the directory location of the package+classname representing the
 * specifications file.  For example, the JUnit tests for this tool use two
 * mock directories, $A and $B (in that order).  A test will specify the
 * specsPath for the test to include those two paths (e.g. setSpecsPath("$A;$B");),
 * and it will add mock files with names like "$A/t/A.java" for class t.A.
 * <P>
 * <B>The specifications database</B>
 * This class also handles the database of specifications.  This database is
 * indexed by Symbol - either ClassSymbol, MethodSymbol or VarSymbol as 
 * appropriate.  Specifications for a Java element are also stored 
 * as fields of the JmlClassDecl, JmlMethodDecl, and JmlVariableDecl AST nodes,
 * but these are only the specs that are declared in that compilation unit.
 * The database holds the combined specifications from all sources, e.g. all
 * files that contribute specifications (JML used to allow a sequence of files,
 * but it has been simplified to take specifications from just one file).
 * Also, Java classes which do not have source available to the compiler
 * do not have an AST in which to place references to specifications.  Thus this
 * database is used as the general mechanism for retrieving specs for a Java element.
 * If there is a Java source file and accompanying ASTs, the fields 
 * JmlClassDecl.typeSpecsCombined, JmlMethodDecl.methodSpecsCombined, and
 * JmlVariableDecl.fieldSpecsCombined should have the same entries as the database.
 * 
 * @author David Cok
 *
 */
public class JmlSpecs {
    
    /** The name of the jar file that constitutes an openjml release. 
     * The specs for Java version v are in a top-level directory named
     * prefix + "v" for each version (e.g. in specs16 for Java 1.6)*/
    private final static String releaseJar = Strings.releaseJar;
    
    /** The name of the jar file that contains a copy of the specs to use, as part of
     * a release.  This is expected to be the specs for the version of Java 
     * being used.  
     */
    private final static String specsJar = Strings.specsJar;
    
    /** The prefix of the top-level directory within the JML release jar file
     * containing the specs for various versions of java (e.g. specs15 for 
     * Java 1.5).
     */
    private final static String prefix = "specs1";
    

    /** The key to use to retrieve the instance of this class from the Context object. */
    //@ non_null
    public static final Context.Key<JmlSpecs> specsKey =
        new Context.Key<JmlSpecs>();

    /** A method that returns the unique instance of this class for the given Context
     * (creating it if it does not already exist).
     * 
     * @param context the Context whose JmlSpecs instance is wanted
     * @return the singleton instance (per Context) of this class
     */
    //@ non_null
    public static JmlSpecs instance(Context context) {
        JmlSpecs instance = context.get(specsKey);
        if (instance == null) {
            instance = new JmlSpecs(context);  // registers itself
        }
        return instance;
    }

    /** Call this to register (a factory for) a singleton (per Context instance) object
     * of this class.
     * 
     * @param context The compilation context in which to register a JmlSpecs instance
     */
    // A factory is used so that the object is not created until needed.  This
    // is important since various options are read (e.g. specspath) at 
    // construction time.
    public static void preRegister(final Context context) {
        context.put(specsKey, new Context.Factory<JmlSpecs>() {
            public JmlSpecs make(Context context) {
                return new JmlSpecs(context);
            }
        });
    }


    /** The Context in which this object was constructed */ 
    //@ non_null
    final protected Context context;
    
    /** The Attr tool for this context */
    final protected JmlAttr attr;
    
    /** The Log tool for this context */
    final protected Log log;
    
    /** The Utils tool for this context */
    final protected Utils utils;
    
    /** The map giving the accumulated specifications for a given type */
    final protected Map<ClassSymbol,TypeSpecs> specsmap = new HashMap<ClassSymbol,TypeSpecs>();
    
    /** The specifications path, which is a sequence of directories in which to
     * find specification files; this is created by initializeSpecsPath().
     * NOTE: This is lazily initialized, so call getSpecsPath() to obtain its value.
     */
    protected LinkedList<Dir> specsDirs = null;
    
    
    /** Creates an instance in association with the given Context; 
     * the specs path is initialized by an explicit call of initializeSpecsPath;
     * use JmlSpecs.instance to get instances - do not call the constructor 
     * directly.
     * 
     * @param context The compilation context
     */
    protected JmlSpecs(Context context) {
        this.context = context;
        context.put(specsKey, this); // self-register
        attr = JmlAttr.instance(context);
        log = Log.instance(context);
        utils = Utils.instance(context);
    }
    
    /** Initializes the specs path given the current settings of options.
     */
    public void initializeSpecsPath() {
        Options options = Options.instance(context);
        String s = JmlOption.value(context,JmlOption.SPECS);
        if (s == null) s = options.get(Strings.specsPathEnvironmentPropertyName);
        if (s == null) s = options.get(Strings.sourcepathOptionName);
        if (s == null) s = options.get(Strings.classpathOptionName);
        if (s == null) s = System.getProperty("java.class.path");
        if (s == null) s = "";
        setSpecsPath(s);
    }
    
    /** This method looks for the internal specification directories and, if
     * found, appends them to the argument. 
     * @param dirs the list to which to append the internal spec directories
     * @return true if found, false if not
     */
    public boolean appendInternalSpecs(boolean verbose, java.util.List<Dir> dirs) {
        
        String versionString = System.getProperty("java.version");
        int version;
        if (versionString.startsWith("1.6")) version = 6;
        else if (versionString.startsWith("1.5")) version = 5;
        else if (versionString.startsWith("1.4")) version = 4;
        else if (versionString.startsWith("1.7")) version = 7;
        else {
            log.noticeWriter.println("Unrecognized version: " + versionString);
            version = 6; // default, if the version string is in an unexpected format
        }
        if (verbose) log.noticeWriter.println("Java version " + version);
       
        // Look for a openjml.jar or jmlspecs.jar file on the classpath
        // If present, use it (and use the first one found).  
        // This happens in command-line mode.
        
        String sp = System.getProperty("java.class.path");
        String[] ss = sp.split(java.io.File.pathSeparator);
        Dir d;
        
        String libToUse = prefix+version;
        
        for (String s: ss) {
            if (s.endsWith(releaseJar)) {
                d = new JarDir(s,libToUse);
                if (d.exists()) {
                    if (verbose) log.noticeWriter.println("Using internal specs " + d);
                    dirs.add(d);
                    return true;
                }
            }
        }
        for (String s: ss) {
            if (s.endsWith(specsJar)) {
                d = new JarDir(s,"");
                if (d.exists()) {
                    if (verbose) log.noticeWriter.println("Using internal specs " + d);
                    dirs.add(d);
                    return true;
                }
            }
        }
        
        // Next see if there is jar file on the classpath that contains
        // specs16 or similar directories
        
        for (String s: ss) {
            if (s.endsWith(".jar")) {
                d = new JarDir(s,libToUse);
                if (d.exists()) {
                    if (verbose) log.noticeWriter.println("Using internal specs " + d);
                    dirs.add(d);
                    return true;
                }
                d = new JarDir(s,prefix + (version-1));
                if (d.exists()) {
                    if (verbose) log.noticeWriter.println("Using internal specs " + d);
                    dirs.add(d);
                    return true;
                }
            }
        }
        
        // FIXME - clean this all up and try to get rid of the dependency on eclipseSpecsProjectLocation
        // (which is used in tests) - be careful though, the UI can be tricky and operates
        // differently in development vs. deployed mode
        
        // Finally, for working in the Eclipse environment, see if there
        // is an environment variable that is set.
        
//        Bundle specs = Platform.getBundle("org.jmlspecs.Specs");
//        if (specs != null) {
//        	Enumeration<String> en = specs.getEntryPaths("java" + version);
//        	String p = en.nextElement();
//        		System.out.println(p);
//        		String pp = specs.getLocation();
//        		System.out.println(pp);
//        		java.net.URL ppp = specs.getEntry("");
//        		System.out.println(ppp);
//        }
        
        String sy = Options.instance(context).get(Strings.eclipseSpecsProjectLocation);
//        if (sy == null) {
//            Bundle specs = Platform.getBundle("org.jmlspecs.Specs");
//            if (specs != null) {
//            		String pp = specs.getLocation();
//            		System.out.println(pp);
//            		int k = pp.indexOf("file:/") + "file:/".length();
//            		sy = pp.substring(k);
//            }
//        }
        // These are used in testing - sy should be the trunk directory of the Specs project
        if (sy != null) {
            
            boolean found = false;
            Dir dd;
            for (int v = version; v >= 4; --v) {
                dd = make(sy+"/java"+v);
                if (dd.exists()) { 
                    dirs.add(dd);
                    found = true;
                } else {
                    // We found some directories - the others ought to exist
                    if (found) log.error("jml.internal.specs.dir.not.exist",dd);
                }
            }
            if (!found) log.error("jml.internal.specs.dir.not.exist",sy);
            return true;
        } else {
            log.error("jml.internal.specs.dir.not.defined");
        }
        return false;
    }
    
    /** Returns the current list of specification directories in use.
     * @return The current list of specification directories, in order.
     */
    public List<Dir> getSpecsPath() {
        if (specsDirs == null) initializeSpecsPath();
        return specsDirs;
    }
    
    /** Returns the source path
     */
    public String[] getSourcePath() {
        Options options = Options.instance(context);
        String s = options.get(Strings.sourcepathOptionName);
        if (s == null) s = options.get(Strings.classpathOptionName);
        if (s == null) s = System.getProperty("java.class.path");
        if (s == null) s = "";
        return s.split(java.io.File.pathSeparator);
    }
    

    
    /** Sets the specifications path according to the given string; the
     * string must be a sequence of directories, separated by the host
     * systems java.io.File.pathSeparator character.  The directories are
     * given as absolute file system paths or as paths relative to the current  
     * working directory. 
     * @param specsPath the string holding the specifications path
     */
    //@ modifies this.specsDirs;
    public void setSpecsPath(String specsPath) {
        setSpecsPath(specsPath.split(java.io.File.pathSeparator));
    }
    
    /** Sets the specifications path according to the given array of strings; the
     * elements of the array are the directories of the specs path, either
     * absolute or relative to the working directory 
     * @param specsPathArray the string holding the new specifications path
     */
    //@ requires \nonnullelements(specsPathArray);
    //@ assignable this.specsDirs;
    public void setSpecsPath(String[] specsPathArray) {
        boolean verbose = utils.jmlverbose >= Utils.JMLVERBOSE ||
            Options.instance(context).get("-verbose") != null;

        specsDirs = new LinkedList<Dir>();
        List<String> todo = new LinkedList<String>();
        for (int i = 0; i<specsPathArray.length; i++) {
            String s = specsPathArray[i];
            if (s == null || s.length() == 0) continue;
            todo.add(s);
        }
        String dir;
        boolean checkDirectories = JmlOption.isOption(context,JmlOption.CHECKSPECSPATH);
        if (JmlOption.isOption(context,JmlOption.INTERNALSPECS)) {
            todo.add("$SY");
        }

        boolean syIncluded = false;
        boolean spIncluded = false;
        boolean cpIncluded = false;
        boolean ecpIncluded = false;
        while (!todo.isEmpty()) {
            dir=todo.remove(0);
            if (dir.equals("$SY")) {
                if (syIncluded) {
                    // If we are processing the last entry and it is a duplicate, just
                    // ignore it.
                    if (!todo.isEmpty()) log.warning("jml.bad.sp.var","$SY");
                } else {
                    syIncluded = true;
                    String dirs = Options.instance(context).get(Strings.systemSpecsLocationEnvironmentPropertyName);
                    if (dirs != null) pushback(dirs,todo);
                    else {
                        if (!appendInternalSpecs(verbose,getSpecsPath())) {
                            log.warning("jml.no.internal.specs");
                        }
                    }
                }
            } else if (dir.equals("$CP")) {
                if (cpIncluded) {
                    log.warning("jml.bad.sp.var","$CP");
                } else {
                    cpIncluded = true;
                    String dirs = Options.instance(context).get("-classpath");
                    if (dirs == null) dirs = System.getProperty("java.class.path");
                    if (dirs != null) pushback(dirs,todo);
                }
            } else if (dir.equals("$ECP")) {
                if (ecpIncluded) {
                    log.warning("jml.bad.sp.var","$ECP");
                } else {
                    ecpIncluded = true;
                    String dirs = System.getProperty("java.class.path");
                    if (dirs != null) pushback(dirs,todo);
                }
            } else if (dir.equals("$SP")) {
                if (spIncluded) {
                    log.warning("jml.bad.sp.var","$SP");
                } else {
                    spIncluded = true;
                    String dirs = Options.instance(context).get("-sourcepath");
                    if (dirs != null) pushback(dirs,todo);
                }
            } else if (dir.length()>0){
                Dir d = make(dir);
                if (d != null) {
                    if (checkDirectories && !d.exists()) { 
                        log.warning("jml.specs.dir.not.exist",d);
                    }
                    specsDirs.add(d);
                } else {
                    // At present make always returns non-null
                    log.error("jml.internal.notsobad","Failed to create a directory path entry from " + dir);
                }
            }
        }
        if (verbose) {
            log.noticeWriter.print("specspath:");
            for (Dir s: specsDirs) {
                log.noticeWriter.print(" ");
                log.noticeWriter.print(s);
            }
            Options options = Options.instance(context);
            log.noticeWriter.println("");
            log.noticeWriter.println("sourcepath: " + options.get("-sourcepath"));
            log.noticeWriter.println("classpath: " + options.get("-classpath"));
            log.noticeWriter.println("java.class.path: " + System.getProperty("java.class.path"));
            log.noticeWriter.flush();
        }
    }

    /** This method is used internally to parse the directory path given in the
     * first argument and to push them (in reverse order) onto the front of the
     * queue that is the second argument; in this way the contents of the
     * directory path are handled as the next items in the order in which they
     * are listed in the directory path.
     * @param dirs the directory path to process
     * @param todo the list of directories yet to be processed
     */
    protected void pushback(String dirs, List<String> todo) {
        String[] array = dirs.split(java.io.File.pathSeparator);
        for (int i=array.length-1; i>=0; --i) {
            todo.add(0,array[i]);
        }
    }
    
    /** A map of names to JavaFileObjects representing files.  The JavaFileObjects
     * can function as files containing source or specifications but do not need
     * to be actually present in the file system.  Thus they are handy in testing.
     */
    final protected Map<String,JavaFileObject> mockFiles = new HashMap<String,JavaFileObject>();
    
    /** Adds a name and associated mock file to the database of files (for this
     * context).
     * @param name the "absolute" filename, that is, the directory as it is on
     * the specs path followed by the package and filename and suffix, all 
     * forward-slash separated
     * @param jfo the JavaFileObject associated with the name
     */
    public void addMockFile(String name, JavaFileObject jfo) {
        mockFiles.put(name,jfo);
    }
    
    /** Creates an appropriate kind of Dir object given the String format of
     * the argument
     * @param dirName the directory as specified in the String format of the
     * specs path
     * @return an appropriate derived class of Dir representing this directory
     */
    public Dir make(String dirName) {
        int n;
        if (dirName.charAt(0) == Strings.mockDirChar) {
            return new MockDir(dirName);
        } else if ((n=dirName.indexOf("!")) != -1) {
            return new JarDir(dirName.substring(0,n),dirName.substring(n+1));
        } else if (dirName.endsWith(".jar") || dirName.endsWith(".zip")) {
            return new JarDir(dirName,"");
        } else {
            return new FileSystemDir(dirName);
        }
    }
    
    /** An abstract class representing a directory element of the specs path. */
    abstract static public class Dir {
        
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
        abstract public /*@Nullable*/JavaFileObject findFile(String filePath);
        
        /** Finds a file with the given path (relative directory, name but
         * no suffix) is present in this directory with any active JML suffix
         * (in the order of priority for suffixes).
         * @return a JavaFileObject for that file
         */
        abstract public /*@Nullable*/JavaFileObject findAnySuffixFile(String filePath);
    }
    
    /** This class handles mock directories - data that appear to be files
     * within directories but do not actually exist in the file system.
     */
    public class MockDir extends Dir {
        
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
        public /*@Nullable*/JavaFileObject findFile(String filePath) { 
            String ss = name + "/" + filePath;
            JavaFileObject j = mockFiles.get(ss);
            return j;
        }
        
        @Override
        public /*@Nullable*/JavaFileObject findAnySuffixFile(String filePath) { 
            String ss = name + "/" + filePath;
            for (String suffix : Strings.suffixes) {
                    JavaFileObject j = mockFiles.get(ss + suffix);
                    if (j != null) return j;
            }
            return null; 
        }
        
    }
    
    /** This class represents conventional file system directories */
    public class FileSystemDir extends Dir {
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
        public /*@Nullable*/JavaFileObject findFile(String filePath) {
            File f = new File(dir,filePath);
            if (f.exists()) {
                return ((JavacFileManager)context.get(JavaFileManager.class)).getRegularFile(f);
            }
            return null;
        }
        
        @Override
        public /*@Nullable*/JavaFileObject findAnySuffixFile(String filePath) {
            for (String suffix : Strings.suffixes) {
                File f = new File(dir,filePath + suffix);
                if (f.exists()) {
                    return ((JavacFileManager)context.get(JavaFileManager.class)).getRegularFile(f);
                }
            }
            return null;
        }
    }
    
    /** This class represents .jar (and .zip) files and subdirectories within them */
    public class JarDir extends Dir {
        /** An object holding the path to the archive file (which may not actually
         * exist)
         */
        protected ZipArchive zipArchive;
        
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
                this.zipArchive = new ZipArchive(((JavacFileManager)context.get(JavaFileManager.class)),new ZipFile(zip));
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
            for (RelativePath.RelativeDirectory f: zipArchive.getSubdirectories()) {
                if (name.length() == 0) return true;
                // TODO - check that this works correctly // use contains?
                if (f.getPath().startsWith(internalDir.getPath())) return true;
            }
            return false;
        }
        
        @Override
        public /*@Nullable*/JavaFileObject findFile(String filePath) { 
            RelativePath file = new RelativePath.RelativeFile(internalDir,filePath);
            if (zipArchive == null) return null;
            if (!zipArchive.contains(file)) return null;
            return zipArchive.getFileObject(internalDir,filePath);
        }
        
        @Override
        public /*@Nullable*/JavaFileObject findAnySuffixFile(String filePath) { 
            if (zipArchive == null) return null;
            for (String suffix : Strings.suffixes) {
                String ss = filePath + suffix;
                RelativePath file = new RelativePath.RelativeFile(internalDir,ss);
                if (!zipArchive.contains(file)) continue;
                JavaFileObject j = zipArchive.getFileObject(internalDir,ss);
                if (j != null) return j;
            }
            return null; 
        }
    }
    
    
    
    /** Finds the first specification file (if any) for the given class.  It
     * searches each directory on the specPath, in order, for a file with a
     * JML suffix (in order), returning the first one found.
     * 
     * @param classSym The Symbol of the class whose specification file is to be found
     * @return The file found, or null if none found
     */
    //@ nullable
    public JavaFileObject findSpecFile(ClassSymbol classSym) {
        return findAnySpecFile(classSym.fullname.toString());
    }
    
    /** Finds the first specification file (if any) for the given class.  It
     * searches for the defined suffixes in order, searching the whole specs
     * path for each one before checking for the next suffix.
     * [NOTE: In a previous design of JML, this method would search each
     * directory for any allowed suffix, before moving on to the next
     * directory - that behavior can be restored by switching the loops.]
     * 
     * @param className The fully-qualified name of the file to be found, 
     *  without a suffix (or the dot before the suffix) either
     *  dot or forward-slash separated
     * @return The file found, or null if none found
     */
    //@ nullable
    public JavaFileObject findAnySpecFile(String className) {
        String s = className.replace('.','/');
        for (String suffix : Strings.suffixes){ 
            for (Dir dir: getSpecsPath()) {
                JavaFileObject j = dir.findFile(s + suffix);
                if (j != null) return j;
            }
        }
        return null;
    }
    
    /** Finds a specific specification file 
     * 
     * @param filename The fully qualified (package + file + suffix) name of 
     * the specification file to be found, with / separation
     * @return The file found, or null if not found
     */
    //@ nullable
    public JavaFileObject findSpecificSpecFile(String filename) {
        for (Dir dir: getSpecsPath()) {
            JavaFileObject j = dir.findFile(filename);
            if (j != null) return j;
        }
        return null;
    }
 
    /** Finds a specific file on the sourcepath
     * 
     * @param filename The fully qualified (package + file + suffix) name of 
     * the file to be found, with / separation
     * @return The file found, or null if not found
     */
    //@ nullable
    public JavaFileObject findSpecificSourceFile(String filename) {
        for (String dir: getSourcePath()) {
            if (dir.isEmpty()) continue;
            JavaFileObject j = make(dir).findFile(filename);
            if (j != null) return j;
        }
        return null;
    }
 
    /////////////////////////////////////////////////////////////////////////
    
    /** A debugging method that prints the content of the specs database */
    public void printDatabase() {
        try {
            for (Map.Entry<ClassSymbol,TypeSpecs> e : specsmap.entrySet()) {
                String n = e.getKey().flatname.toString();
                JavaFileObject f = e.getValue().file;
                log.noticeWriter.println(n + " " + (f==null?"<NOFILE>":f.getName()));
                ListBuffer<JmlTree.JmlTypeClause> clauses = e.getValue().clauses;
                log.noticeWriter.println("  " + clauses.size() + " CLAUSES");
                for (JmlTree.JmlTypeClause j: clauses) {
                    log.noticeWriter.println("  " + JmlPretty.write(j));
                }
                log.noticeWriter.println("  " + e.getValue().methods.size() + " METHODS");
                for (MethodSymbol m: e.getValue().methods.keySet()) {
                    MethodSpecs sp = getSpecs(m);
                    log.noticeWriter.println("  " + JmlPretty.write(sp.mods));
                    log.noticeWriter.println(" " + m.enclClass().toString() + " " + m.flatName());
                    log.noticeWriter.print(JmlPretty.write(sp.cases));
                    //log.noticeWriter.println(sp.toString("     "));
                }
                log.noticeWriter.println("  " + e.getValue().fields.size() + " FIELDS");
                for (VarSymbol m: e.getValue().fields.keySet()) {
                    FieldSpecs sp = getSpecs(m);
                    log.noticeWriter.print("  " + JmlPretty.write(sp.mods));
                    log.noticeWriter.println(" " + m.enclClass().toString() + " " + m.flatName());
                    for (JmlTypeClause t: sp.list) {
                        log.noticeWriter.print(JmlPretty.write(t));
                        //log.noticeWriter.println(sp.toString("     "));
                    }
                }
            }
            log.noticeWriter.println("MOCK FILES");
            for (String s: mockFiles.keySet()) {
                log.noticeWriter.println(s + " :: " + mockFiles.get(s));
            }
        } catch (Exception e) {
            log.noticeWriter.println("Exception occurred in printing the database: " + e);
        }
    }
    
    
    /** Retrieves the specifications for a given type, or null if no specs are
     * present for this type
     * @param type the ClassSymbol of the type whose specs are wanted
     * @return the specifications, or null if there are none in the database
     */
    //@ nullable 
    public TypeSpecs get(ClassSymbol type) {
        return specsmap.get(type);
    }
    
    /** Retrieves the specifications for a given type, providing and registering
     * a default if one is not there
     * @param type the ClassSymbol of the type whose specs are wanted
     * @return the specifications
     */
    public TypeSpecs getSpecs(ClassSymbol type) {
        TypeSpecs t = specsmap.get(type);
        if (t == null) {
            specsmap.put(type, t=new TypeSpecs(type));
        }
        return t;
    }
    
    /** Deletes the specs for a given type, including all method and field
     * specs for that type.
     * @param type the type whose specs are to be deleted
     */
    public void deleteSpecs(ClassSymbol type) {
        specsmap.put(type, null);
    }
    
    
    /** Adds the specs for a given type to the database, overwriting anything
     * already there
     * @param type the ClassSymbol of the type whose specs are provided
     * @param spec the specs to associate with the type
     */
    public void putSpecs(ClassSymbol type, TypeSpecs spec) {
        spec.csymbol = type;
        specsmap.put(type,spec);
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("Saving class specs for " + type.flatname + (spec.decl == null ? " (null declaration)": " (non-null declaration)"));
    }
    
    /** Adds the specs for a given method to the database, overwriting anything
     * already there.  There must already be a specs entry for the owning class
     * @param m the MethodSymbol of the method whose specs are provided
     * @param spec the specs to associate with the method
     */
    public void putSpecs(MethodSymbol m, MethodSpecs spec) {
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("            Saving method specs for " + m.enclClass() + " " + m);
        specsmap.get(m.enclClass()).methods.put(m,spec);
    }
    
    /** Adds the specs for a given initialization block to the database, overwriting anything
     * already there.  The type must already have a spec supplied, to which this
     * is added.
     * @param csym the class to which the initialilzation block belongs
     * @param m the Block whose specs are provided
     * @param spec the specs to associate with the block
     */
    public void putSpecs(ClassSymbol csym, JCTree.JCBlock m, MethodSpecs spec) {
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("            Saving initializer block specs " );
        specsmap.get(csym).blocks.put(m,spec);
    }
    
    /** Adds the specs for a given field to the database, overwriting anything
     * already there.  The type must already have a class specs, to which
     * this is added.
     * @param m the VarSymbol of the method whose specs are provided
     * @param spec the specs to associate with the method
     */
    public void putSpecs(VarSymbol m, FieldSpecs spec) {
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("            Saving field specs for " + m.enclClass() + " " + m);
        specsmap.get(m.enclClass()).fields.put(m,spec);
    }
    
    /** Retrieves the specs for a given method
     * @param m the MethodSymbol of the method whose specs are wanted
     * @return the specs of the method, or null if none are present
     */
    //@ nullable
    public MethodSpecs getSpecs(MethodSymbol m) {
        TypeSpecs t = specsmap.get(m.enclClass());
        return t == null ? null : t.methods.get(m);
    }
    
    // TODO - document
    public JmlMethodSpecs getDenestedSpecs(MethodSymbol m) {
        MethodSpecs s = getSpecs(m);
        if (s == null) return null;
        if (s.cases.deSugared == null) {
            attr.deSugarMethodSpecs(s.cases.decl,s);
        }
        return s.cases.deSugared;
    }
    
    // TODO - document
    // FIXME - this needs to be made consistent with the below
    public MethodSpecs defaultSpecs(JmlMethodDecl m) {
        // FIXME - should use a factory
        JmlTree.Maker M = JmlTree.Maker.instance(context);
        JmlMethodSpecs ms = new JmlMethodSpecs();
        MethodSpecs mspecs = new MethodSpecs(null,ms); // FIXME - empty instead of null modifiers?
        ms.pos =  m.pos;
        ms.decl = m;
        ms.deSugared = null; // FIXME- was ms?

        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
        // sym can be null if the method call is in a field initializer (and not in the body of a method)
        // Not sure when sym.type is null - but possibly when an initializer block is created to hold translated
        // material from a field initializer
        for (JCExpression t: m.thrown) {
            list.add(t);
        }
        list.add(JmlTreeUtils.instance(context).makeType(m.pos, Symtab.instance(context).runtimeExceptionType));
        JmlMethodClauseSignalsOnly cl = new JmlMethodClauseSignalsOnly(m.pos,JmlToken.SIGNALS_ONLY, list.toList());
        JmlSpecificationCase cs = new JmlSpecificationCase(m.pos, M.Modifiers(0), false,null,null,com.sun.tools.javac.util.List.<JmlMethodClause>of(cl));
        mspecs.cases.cases = com.sun.tools.javac.util.List.<JmlSpecificationCase>of(cs);
        return mspecs;
    }

    // TODO - document
    public static MethodSpecs defaultSpecs(Context context, MethodSymbol sym, int pos) {
        // FIXME - should use a factory
        JmlTree.Maker M = JmlTree.Maker.instance(context);
        JmlMethodSpecs ms = new JmlMethodSpecs();
        MethodSpecs mspecs = new MethodSpecs(null,ms); // FIXME - empty instead of null modifiers?
        ms.pos = pos;
        ms.decl = null; // FIXME - this needs filling in?
        ms.deSugared = null; // FIXME- was ms?

        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
        // sym can be null if the method call is in a field initializer (and not in the body of a method)
        // Not sure when sym.type is null - but possibly when an initializer block is created to hold translated
        // material from a field initializer
        if (sym != null && sym.type != null) for (Type t: sym.getThrownTypes()) {
            JCExpression e = JmlTreeUtils.instance(context).makeType(pos, t);
            list.add(e);
        }
        list.add(JmlTreeUtils.instance(context).makeType(pos, Symtab.instance(context).runtimeExceptionType));
        JmlMethodClauseSignalsOnly cl = new JmlMethodClauseSignalsOnly(pos,JmlToken.SIGNALS_ONLY, list.toList());
        JmlSpecificationCase cs = new JmlSpecificationCase(pos, M.Modifiers(0), false,null,null,com.sun.tools.javac.util.List.<JmlMethodClause>of(cl));
        mspecs.cases.cases = com.sun.tools.javac.util.List.<JmlSpecificationCase>of(cs);
        return mspecs;
    }

    /** Retrieves the specs for a given field
     * @param m the VarSymbol of the field whose specs are wanted
     * @return the specs of the field, or null if none are present
     */
    //@ nullable
    public FieldSpecs getSpecs(VarSymbol m) {
        ClassSymbol c = m.enclClass();
        if (c == null) return null; // This happens at least when m is the symbol for 'class' as in int.class
        TypeSpecs t = getSpecs(c);
        return t == null ? null : t.fields.get(m);
    }
    
    /** Retrieves the specs for a given initializer block
     * @param sym the class in which the block resides
     * @param m the JCBlock of the block whose specs are wanted
     * @return the specs of the block, or null if none are present
     */
    //@ nullable
    public MethodSpecs getSpecs(ClassSymbol sym, JCTree.JCBlock m) {
        TypeSpecs t = specsmap.get(sym);
        return t == null ? null : t.blocks.get(m);
    }
   
    /** An ADT to hold the JML specifications for a Java class, including
     * clauses (e.g. invariant), JML modifiers of the class, model/ghost
     * declarations
     * @author David Cok
     *
     */
    public static class TypeSpecs {
        /** The Symbol for the type these specs belong to*/
        public ClassSymbol csymbol;
        
        /** The AST from specification files that provide the
         * specs for the class this TypeSpecs object documents.  This is only
         * valid for a TypeSpecs object holding combined specifications.
         */
        public JmlClassDecl refiningSpecDecls = null;
        
        /** The source file for the modifiers, not necessarily for the rest of the specs
         * if these are the combined specs */
        //@ nullable   // may be null if there are no specs
        public JavaFileObject file;

        /** The JmlClassDecl from the specification */ // FIXME - this is probably better used as the decl of the Java file, if any
        //@ nullable   // may be null if there are no specs
        public JmlClassDecl decl; // FIXME - with a spec sequence the specs from more than one

        /** The JML modifiers of the class, as given in the COMBINED specification */
        //@ nullable   // may be null if there are no specs // FIXME - no, at minimum these are the Java modifiers
        public JCTree.JCModifiers modifiers;

        /** Caches the nullity for the associated class: if null, not yet determined;
         * otherwise, the result of considering explicit declarations, declarations
         * on containing classes, and the system default.
         */
        //@ nullable
        private JmlToken defaultNullity = null;
        
        /** All the specification clauses for the class (not method clauses or field clauses or block clauses) */
        /*@ non_null */
        public ListBuffer<JmlTree.JmlTypeClause> clauses;

        /** All the model types directly declared in this type */
        @NonNull
        public ListBuffer<JmlTree.JmlClassDecl> modelTypes = new ListBuffer<JmlTree.JmlClassDecl>();
        
        /** Synthetic methods for model fields (these are also included in the clauses list) */
        /*@ non_null */
        public ListBuffer<JmlTree.JmlTypeClauseDecl> modelFieldMethods = new ListBuffer<JmlTree.JmlTypeClauseDecl>();

        // The following maps are part of the TypeSpecs so that everything associated with a given
        // type can be disposed of at once (by releasing references to the TypeSpecs instance)

        /** A map from methods of the class to the specifications for the method. */
        /*@ non_null */
        public Map<MethodSymbol,MethodSpecs> methods = new HashMap<MethodSymbol,MethodSpecs>();

        /** A map from fields of the class to the specifications for the field. */
        /*@ non_null */
        public Map<VarSymbol,FieldSpecs> fields = new HashMap<VarSymbol,FieldSpecs>();
        
        /** A map from initializer blocks of the class to the specifications for the initializers. */
        /*@ non_null */
        public Map<JCTree.JCBlock,MethodSpecs> blocks = new HashMap<JCTree.JCBlock,MethodSpecs>();

        /** The spec associated with the initializer keyword, if any */
        /*@ nullable */ // will be null if there is no initializer specification
        public JmlTypeClauseInitializer initializerSpec = null;
        
        /** The spec associated with the static_initializer keyword, if any */
        /*@ nullable */ // will be null if there is no static_initializer specification
        public JmlTypeClauseInitializer staticInitializerSpec = null;
        
        // FIXME - comment
        public JmlMethodDecl checkInvariantDecl;
        // FIXME - comment
        public JmlMethodDecl checkStaticInvariantDecl;
        
        /** A quite empty and unfinished TypeSpecs object for a given class,
         * possibly but not necessarily one that has only specs and binary,
         * but no Java source.
         * @param symbol the class symbol for these specs
         */
        public TypeSpecs(ClassSymbol symbol) {
            this.csymbol = symbol;
            this.file = symbol.sourcefile;
            this.decl = null;
            this.modifiers = null;
            this.clauses = new ListBuffer<JmlTree.JmlTypeClause>();
        }
        
        // TODO - comment - only partially fills in the class - used for a binary file - I think everything is pretty much empty and null
        public TypeSpecs(JavaFileObject file, JCTree.JCModifiers mods, ListBuffer<JmlTree.JmlTypeClause> clauses) {
            this.file = file;
            this.decl = null;
            this.modifiers = mods;
            this.clauses = clauses != null ? clauses : new ListBuffer<JmlTree.JmlTypeClause>();
        }
        
        // TODO - comment - only partially fills in the class
        public TypeSpecs(JmlClassDecl decl) {
            this.file = decl.source();
            this.decl = decl;
            this.modifiers = decl.mods;
            this.clauses = decl.typeSpecsCombined != null ? decl.typeSpecsCombined.clauses :
                decl.typeSpecs != null ? decl.typeSpecs.clauses
                    : new ListBuffer<JmlTree.JmlTypeClause>();
        }
        
        // Use when there is no spec for the type symbol (but records the fact
        // that we looked and could not find one)
        public TypeSpecs() {
            this.file = null;
            this.decl = null;
            this.modifiers = null;
            this.clauses = new ListBuffer<JmlTree.JmlTypeClause>();
        }
        
        public String toString() {
            StringWriter s = new StringWriter();
            JmlPretty p = new JmlPretty(s, false);
            for (JmlTypeClause c: clauses) {
                c.accept(p);
                try { p.println(); } catch (IOException e) {} // it can't throw up, and ignore if it does
            }
            if (modelTypes != null) for (JmlClassDecl c: modelTypes) {
                c.accept(p);
                try { p.println(); } catch (IOException e) {} // it can't throw up, and ignore if it does
            }
            return s.toString();
        }
    }
    
    /** Returns the default nullity for the given class - don't call this until
     * classes have been entered and annotations have been attributed.  If the
     * argument is null, then the default nullity as set on the command-line is returned.
     * Note that the default nullity for the class is cached in the class specs once
     * computed, to avoid recompuation.
     * @param csymbol the class whose default nullity is to be determined; if
     *   null the default system nullity setting (per the command-line) is returned
     * @return JmlToken.NULLABLE or JmlToken.NONNULL
     */
    //@ ensures \result != null;
    public /*@non_null*/ JmlToken defaultNullity(/*@ nullable*/ ClassSymbol csymbol) {
        if (csymbol == null) {
            // FIXME - this is no longer true
            // Note: NULLABLEBYDEFAULT turns off NONNULLBYDEFAULT and vice versa.
            // If neither one is present, then the logic here will give the
            // default as NONNULL.
            if (JmlOption.isOption(context,JmlOption.NULLABLEBYDEFAULT)) {
                return JmlToken.NULLABLE;
            } else {
                return JmlToken.NONNULL;
            }
        }
        TypeSpecs spec = get(csymbol); // FIXME - why would spec be null?
        if (spec == null || spec.defaultNullity == null) {
            JmlToken t = null;
            if (csymbol.getAnnotationMirrors() != null) {
                if (csymbol.attribute(attr.nullablebydefaultAnnotationSymbol) != null) {
                    t = JmlToken.NULLABLE;
                } else if (csymbol.attribute(attr.nonnullbydefaultAnnotationSymbol) != null) {
                    t = JmlToken.NONNULL;
                }
            } 
            if (t == null) {
                Symbol sym = csymbol.owner; // The owner might be a package - currently no annotations for packages
                if (sym instanceof ClassSymbol) {
                    t = defaultNullity((ClassSymbol)sym);
                } else {
                    t = defaultNullity(null);
                }
            }
            if (spec == null) return t;
            spec.defaultNullity = t;
        }
        return spec.defaultNullity;
    }

    /** Caches the symbol for the org.jmlspecs.annotation.NonNull */
    ClassSymbol nonnullAnnotationSymbol = null;
    /** Caches the symbol for the org.jmlspecs.annotation.Nullable */
    ClassSymbol nullableAnnotationSymbol = null;
    
    /** Returns whether the given symbol is non-null (either explicitly or by
     * default); the second parameter is the enclosing class.
     * @param symbol the symbol whose nullity is being checked - either a VarDef (a 
     * parameter declaration) or a MethodDef (for the return type)
     * @param csymbol the enclosing class, from which any default comes
     * @return true if the symbol is non-null explicitly or by default
     */
    public boolean isNonNull(Symbol symbol) {
        return isNonNull(symbol,symbol.enclClass());
    }
    
    public boolean isNonNull(Symbol symbol, ClassSymbol csymbol) {
        if (symbol.type.isPrimitive()) return false;
        if (nonnullAnnotationSymbol == null) {
            nonnullAnnotationSymbol = ClassReader.instance(context).enterClass(Names.instance(context).fromString(Strings.nonnullAnnotation));
        }
        // Find the annotation on the given symbol, if any
        Attribute.Compound attr = symbol.attribute(nonnullAnnotationSymbol);
        if (attr!=null) return true;
        if (nullableAnnotationSymbol == null) {
            nullableAnnotationSymbol = ClassReader.instance(context).enterClass(Names.instance(context).fromString(Strings.nullableAnnotation));
        }
        attr = symbol.attribute(nullableAnnotationSymbol);
        if (attr!=null) return false;
        return defaultNullity(csymbol) == JmlToken.NONNULL;

    }
    
    /** An ADT to hold the specs for a method or block */
    public static class MethodSpecs {
        
        public JCTree.JCModifiers mods;
        public VarSymbol queryDatagroup;
        public VarSymbol secretDatagroup;
        public JmlMethodSpecs cases;
        
        public MethodSpecs(JCTree.JCModifiers mods, JmlMethodSpecs m) { 
            this.mods = mods;
            cases = m != null ? m : new JmlMethodSpecs(); 
        }
    }

    /** An ADT to hold the specs for a field declaration */
    public static class FieldSpecs {
        
        /** Modifiers pertinent to this fields specifications */
        public JCTree.JCModifiers mods;
        
        /** A list of the clauses pertinent to this field (e.g. in, maps) */
        public ListBuffer<JmlTree.JmlTypeClause> list = new ListBuffer<JmlTree.JmlTypeClause>();
        
        /** Creates a FieldSpecs object initialized with only the given modifiers */
        public FieldSpecs(JCTree.JCModifiers mods) { 
            this.mods = mods;
        }
        
        @Override
        public String toString() {
            StringWriter s = new StringWriter();
            JmlPretty p = new JmlPretty(s, false);
            mods.accept(p);
            try { p.println(); } catch (IOException e) {} // it can't throw up, and ignore if it does
                                // FIXME - println only if there are mods?
            for (JmlTypeClause c: list) {
                c.accept(p);
                try { p.println(); } catch (IOException e) {} // it can't throw up, and ignore if it does
            }
            return s.toString();
            
        }
    }
    
}

