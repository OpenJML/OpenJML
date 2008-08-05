package org.jmlspecs.openjml;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipFile;

import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;

import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.file.ZipArchive;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;

/** This class manages the specifications during a compilation.  There should be
 * just one instance per compilation Context, ensured by calling the preRegister
 * method.  The class provides methods for finding specification files, and it
 * maintains a database of specifications of types, methods, and field.  
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
 * of -specsPath</LI>
 * <LI>2) if there is no command-line argument, the value of the environment property 
 * org.jmlspecs.specspath is used</LI>
 * <LI>3) if that is not defined, the value of the sourcepath is used (specified 
 * by the -sourcepath command-line option)</LI>
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
 * look like the text of a compilation unit), but which does not actually exist.
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
 * and it will add mock files with names like "$A/t/A.java".
 * <P>
 * <B>The specifications database</B>
 * This class also handles the database of specifications.  This database is
 * indexed by Symbol - either ClassSymbol, MethodSymbol or VarSymbol as 
 * appropriate.  The specifications for a Java element are also stored redundantly
 * as fields of the JmlClassDecl, JmlMethodDecl, and JmlVariableDecl AST nodes.
 * That is simply redundant information for classes which are parsed from source
 * files; however, Java classes which only have binaries or which have neither
 * source nor binary do not have an AST in which to place references.  Thus this
 * database is used as the general mechanism for retrieving specs for a Java element.
 * 
 * @author David Cok
 *
 */
public class JmlSpecs {

    /** The key to use to retrieve the instance of this class from the Context object. */
    //@ non_null
    public static final Context.Key<JmlSpecs> specsKey =
        new Context.Key<JmlSpecs>();

    /** A method that returns the unique instance of this class for the given Context
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

    /** Call this to register a singleton (per Context instance) object
     * of this class.
     * 
     * @param context The compilation context in which to register a JmlSpecs instance
     */
    // A factory is used so that the object is not created until needed.  This
    // is important since various options are read (e.g. specsPath) at 
    // construction time.
    public static void preRegister(final Context context) {
        context.put(specsKey, new Context.Factory<JmlSpecs>() {
            public JmlSpecs make() {
                return new JmlSpecs(context); // Registers the new instance in place of the factory
            }
        });
    }


    /** The Context in which this object was constructed */ 
    //@ non_null
    protected Context context;
    
    protected JmlAttr attr;
    
    /** The map giving the accumulated specifications for a given type */
    protected Map<ClassSymbol,TypeSpecs> specs = new HashMap<ClassSymbol,TypeSpecs>();
    
    /** The specifications path, which is a sequence of directories in which to
     * find specification files; this is created by initializeSpecsPath().
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
        context.put(specsKey, this);
        attr = JmlAttr.instance(context);
    }
    
    /** Initializes the specs path given the current settings of options.
     */
    public void initializeSpecsPath() {
        String s = JmlOptionName.value(context,JmlOptionName.SPECS);
        if (s == null) s = System.getProperty(Utils.specsPathEnvironmentPropertyName);
        if (s == null) s = Options.instance(context).get("-sourcepath");
        if (s == null) s = Options.instance(context).get("-classpath");
        if (s == null) s = System.getProperty("java.class.path");
        if (s != null) setSpecsPath(s);
    }
    
    /** This method looks for the internal specification directories and, if
     * found, appends them to the argument. 
     * @param dirs the list to which to append the internal spec directories
     * @return true if found, false if not
     */
    public boolean appendInternalSpecs(boolean verbose, java.util.List<Dir> dirs) {
        String sp = System.getProperty("java.class.path");
        String[] ss = sp.split(java.io.File.pathSeparator);
        Dir d;
        for (String s: ss) {
            if (s.endsWith("jmlcheck.jar")) {
                d = new JarDir(s,"specs16");
                if (d.exists()) {
                    if (verbose) System.out.println("Using internal specs " + d);
                    dirs.add(d);
                    return true;
                }
                d = new JarDir(s.replace("jmlcheck.jar","jmlspecs.jar"),"");
                if (d.exists()) {
                    if (verbose) System.out.println("Using internal specs " + d);
                    dirs.add(d);
                    return true;
                }
            }
        }
        for (String s: ss) {
            if (s.endsWith(".jar")) {
                d = new JarDir(s,"specs16");
                if (d.exists()) {
                    if (verbose) System.out.println("Using internal specs " + d);
                    dirs.add(d);
                    return true;
                }
            }
        }
        String sy = System.getProperty(Utils.eclipseSpecsProjectLocation);
        // These are used in testing - sy should be the trunk directory of the JMLspecs project
        if (sy != null) {
            String versionString = System.getProperty("java.version");
            int version = 6; // the current default
            if (versionString.startsWith("1.6")) version = 6;
            else if (versionString.startsWith("1.5")) version = 5;
            else if (versionString.startsWith("1.4")) version = 4;
            else if (versionString.startsWith("1.7")) version = 7;
            else {
                System.out.println("Unrecognized version: " + versionString);
                version = 6; // default, if the version string is in an unexpected format
            }
            
            boolean found = false;
            Dir dd;
            for (int v = version; v >= 4; --v) {
                dd = make(sy+"/java"+v);
                if (dd.exists()) { 
                    dirs.add(dd);
                    found = true;
                } else {
                    // We found some directories - the others ought to exist
                    if (found) Log.instance(context).error("jml.internal.specs.dir.not.exist",dd);
                }
            }
            if (!found) Log.instance(context).error("jml.internal.specs.dir.not.exist",sy);
            return true;
        } else {
            Log.instance(context).error("jml.internal.specs.dir.not.defined");
        }
        return false;
    }
    
    public List<Dir> getSpecsPath() {
        return specsDirs;
    }
    
    /** Sets the specifications path according to the given string; the
     * string must be a sequence of directories, separated by the host
     * systems java.io.File.pathSeparator character.  The directories are
     * given as absolute paths or as paths relative to the current working 
     * directory. 
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
    //@ requires \nonnullelements(sp);
    public void setSpecsPath(String[] specsPathArray) {
        boolean verbose = Utils.jmldebug ||
            JmlOptionName.isOption(context,JmlOptionName.JMLVERBOSE) ||
            Options.instance(context).get("-verbose") != null;

        specsDirs = new LinkedList<Dir>();
        List<String> todo = new LinkedList<String>();
        for (int i = 0; i<specsPathArray.length; i++) {
            String s = specsPathArray[i];
            if (s == null || s.length() == 0) continue;
            todo.add(s);
        }
        String dir;
        boolean checkDirectories = !JmlOptionName.isOption(context,JmlOptionName.NOCHECKSPECSPATH);
        if (!JmlOptionName.isOption(context,JmlOptionName.NOINTERNALSPECS)) {
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
                    if (!todo.isEmpty()) Log.instance(context).warning("jml.bad.sp.var","$SY");
                } else {
                    syIncluded = true;
                    String dirs = System.getProperty(Utils.systemSpecsLocationEnvironmentPropertyName);
                    if (dirs != null) pushback(dirs,todo);
                    else {
                        if (!appendInternalSpecs(verbose,specsDirs)) {
                            Log.instance(context).warning("jml.no.internal.specs");
                        }
                    }
                }
            } else if (dir.equals("$CP")) {
                if (cpIncluded) {
                    Log.instance(context).warning("jml.bad.sp.var","$CP");
                } else {
                    cpIncluded = true;
                    String dirs = Options.instance(context).get("-classpath");
                    if (dirs == null) dirs = System.getProperty("java.class.path");
                    if (dirs != null) pushback(dirs,todo);
                }
            } else if (dir.equals("$ECP")) {
                if (ecpIncluded) {
                    Log.instance(context).warning("jml.bad.sp.var","$ECP");
                } else {
                    ecpIncluded = true;
                    String dirs = System.getProperty("java.class.path");
                    if (dirs != null) pushback(dirs,todo);
                }
            } else if (dir.equals("$SP")) {
                if (spIncluded) {
                    Log.instance(context).warning("jml.bad.sp.var","$SP");
                } else {
                    spIncluded = true;
                    String dirs = Options.instance(context).get("-sourcepath");
                    if (dirs != null) pushback(dirs,todo);
                }
            } else if (dir.length()>0){
                Dir d = make(dir);
                if (d != null) {
                    if (checkDirectories && !d.exists()) { 
                        Log.instance(context).warning("jml.specs.dir.not.exist",d);
                    }
                    specsDirs.add(d);
                } else {
                    // At present make always returns non-null
                    Log.instance(context).error("jml.internal.notsobad","Failed to create a directory path entry from " + dir);
                }
            }
        }
        if (verbose) {
            for (Dir s: specsDirs) {
                System.out.println("SPECSPATH " + s);
            }
            System.out.println("SOURCEPATH -sourcepath = " + Options.instance(context).get("-sourcepath"));
            System.out.println("CLASSPATH -classpath = " + Options.instance(context).get("-classpath"));
            System.out.println("CLASSPATH java.class.path = " + System.getProperty("java.class.path"));
        }
    }
    
    /** Appends the internal runtime directory to the -classpath option.
     */
    protected void appendRuntime() {
        boolean verbose = Utils.jmldebug ||
            JmlOptionName.isOption(context,JmlOptionName.JMLVERBOSE) ||
            Options.instance(context).get("-verbose") != null;
        String sp = System.getProperty("java.class.path");
        String[] ss = sp.split(java.io.File.pathSeparator);
        String sss = null;
        for (String s: ss) {
            if (s.endsWith("jmlcheck.jar")) {
                Dir d = new JarDir(s,"org/jmlspecs/lang");
                if (d.exists()) {
                    sss = s;
                    break;
                }
            }
        }
        if (sss == null) for (String s: ss) {
            if (s.endsWith(".jar")) {
                Dir d = new JarDir(s,"org/jmlspecs/lang");
                if (d.exists()) {
                    sss = s;
                    break;
                }
            }
        }
        if (sss == null) {
            String sy = System.getProperty(Utils.eclipseProjectLocation);
            // These are used in testing - sy should be the directory of the OpenJML project
            if (sy != null) {
                sss = sy + "/runtime";
            }
        }
        if (sss != null) {
            if (verbose) System.out.println("Using internal runtime " + sss);
            sp = Options.instance(context).get("-classpath");
            if (sp != null) Options.instance(context).put("-classpath",sp + java.io.File.pathSeparator + sss);
        } else {
            Log.instance(context).warning("jml.no.internal.runtime");
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
    protected Map<String,JavaFileObject> mockFiles = new HashMap<String,JavaFileObject>();
    
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
    
    /** Creates an appropriate kind of DIr object given the String format of
     * the argument
     * @param dirName the directory as specified in the String format of the
     * specs path
     * @return an appropriate derived class of Dir representing this directory
     */
    public Dir make(String dirName) {
        int n;
        if (dirName.charAt(0) == Utils.mockDirChar) {
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
        abstract public JavaFileObject findFile(String filePath);
        
        /** Finds a file with the given path (relative directory, name but
         * no suffix) is present in this directory with any active JML suffix
         * (in the order of priority for suffixes).
         * @return a JavaFileObject for that file
         */
        abstract public JavaFileObject findAnySuffixFile(String filePath);
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
        public JavaFileObject findFile(String filePath) { 
            String ss = name + "/" + filePath;
            JavaFileObject j = mockFiles.get(ss);
            return j;
        }
        
        @Override
        public JavaFileObject findAnySuffixFile(String filePath) { 
            String ss = name + "/" + filePath;
            for (String suffix : Utils.suffixes) {
                    JavaFileObject j = mockFiles.get(ss + suffix);
                    if (j != null) return j;
            }
            return null; 
        }
        
    }
    
    /** This class represents conventional file system directories */
    public class FileSystemDir extends Dir {
        /** The java.io.File object for the directory */
        File dir;
        
        /** Creates a Dir object for the given directory; the existence of a
         * Dir object does not mean that the underlying directory actually
         * exists
         * @param dirName the relative or absolute path to the directory
         */
        public FileSystemDir(String dirName) {
            this.name = dirName;
            this.dir = new File(dirName);
        }
        
        @Override
        public boolean exists() {
            return dir.exists() && dir.isDirectory();
        }

        @Override
        public JavaFileObject findFile(String filePath) {
            File f = new File(dir,filePath);
            if (f.exists()) {
                return ((JavacFileManager)context.get(JavaFileManager.class)).getRegularFile(f);
            }
            return null;
        }
        
        @Override
        public JavaFileObject findAnySuffixFile(String filePath) {
            for (String suffix : Utils.suffixes) {
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
        ZipArchive zipArchive;
        
        /** The subdirectory within the archive, with a trailing slash added to
         * the name, or an empty string if the directory desired is the top-level
         * of the archive.
         */
        String internalDirSlash;
        
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
            this.internalDirSlash = name.length() == 0 ? name : (name + "/");
            this.name = zip + (name.length() == 0 ? name : ("!" + name));
        }
        
        @Override
        public boolean exists() {
            if (zipArchive == null) return false;
            for (String f: zipArchive.getSubdirectories()) {
                if (name.length() == 0) return true;
                if (f.startsWith(internalDirSlash)) return true;
            }
            return false;
        }
        
        @Override
        public JavaFileObject findFile(String filePath) { 
            if (zipArchive == null) return null;
            if (!zipArchive.contains(internalDirSlash + filePath)) return null;
            return zipArchive.getFileObject(internalDirSlash,filePath);
        }
        
        @Override
        public JavaFileObject findAnySuffixFile(String filePath) { 
            if (zipArchive == null) return null;
            for (String suffix : Utils.suffixes) {
                String ss = filePath + suffix;
                if (!zipArchive.contains(internalDirSlash + ss)) continue;
                JavaFileObject j = zipArchive.getFileObject(internalDirSlash,ss);
                if (j != null) return j;
            }
            return null; 
        }
    }
    
    /** A debugging method that prints the content of the specs database */
    public void printDatabase() {
        System.out.println("SPECS DATABASE " + specs.size());
        try {
            for (Map.Entry<ClassSymbol,TypeSpecs> e : specs.entrySet()) {
                String n = e.getKey().flatname.toString();
                JavaFileObject f = e.getValue().file;
                System.out.println(n + " " + (f==null?"<NOFILE>":f.getName()));
                ListBuffer<JmlTree.JmlTypeClause> clauses = e.getValue().clauses;
                System.out.println("  " + clauses.size() + " CLAUSES");
                for (JmlTree.JmlTypeClause j: clauses) {
                    // FIXME               System.out.println("  " + j.token.internedName() + " " + j.expression.toString());
                }
                System.out.println("  " + e.getValue().methods.size() + " METHODS");
                for (MethodSymbol m: e.getValue().methods.keySet()) {
                    JmlMethodSpecs sp = getSpecs(m);
                    System.out.println("  " + m.enclClass().toString() + " " + m.flatName());
                    System.out.print(JmlPretty.write(sp));
                    //System.out.println(sp.toString("     "));
                }
                System.out.println("  " + e.getValue().fields.size() + " FIELDS");
                for (VarSymbol m: e.getValue().fields.keySet()) {
                    FieldSpecs sp = getSpecs(m);
                    for (JmlTypeClause t: sp.list) {
                    System.out.println("  " + m.enclClass().toString() + " " + m.flatName());
                    System.out.print(JmlPretty.write(t));
                    //System.out.println(sp.toString("     "));
                    }
                }
            }
            System.out.println("MOCK FILES");
            for (String s: mockFiles.keySet()) {
                System.out.println(s + " :: " + mockFiles.get(s));
            }
        } catch (Exception e) {
            System.out.println("Exception occurred in printing the database: " + e);
        }
    }
    
    
    /** Retrieves the specifications for a given type
     * @param type the ClassSymbol of the type whose specs are wanted
     * @return the specifications, or null if there are none in the database
     */
    //@ nullable
    public TypeSpecs get(ClassSymbol type) {
        return specs.get(type);
    }
    
    /** Deletes the specs for a given type, including all method and field
     * specs for that type.
     * @param type the type whose specs are to be deleted
     */
    public void deleteSpecs(ClassSymbol type) {
        specs.put(type, null);
    }
    
    
    /** Adds the specs for a given type to the database, overwriting anything
     * already there
     * @param type the ClassSymbol of the type whose specs are provided
     * @param spec the specs to associate with the type
     */
    public void putSpecs(ClassSymbol type, /*@ nullable */ TypeSpecs spec) {
        spec.csymbol = type;
        specs.put(type,spec);
        if (Utils.jmldebug) System.out.println("PUTTING SPECS " + type.flatname + (spec.decl == null ? " (null declaration)": " (non-null declaration)"));
    }
    
    /** Adds the specs for a given method to the database, overwriting anything
     * already there
     * @param m the MethodSymbol of the method whose specs are provided
     * @param spec the specs to associate with the method
     */
    public void putSpecs(MethodSymbol m, JmlMethodSpecs spec) {
        if (Utils.jmldebug) System.out.println("            PUTTING METHOD SPECS " + m.enclClass() + " " + m);
        specs.get(m.enclClass()).methods.put(m,spec);   // FIXME - what if the type is not present
    }
    
    /** Adds the specs for a given method to the database, overwriting anything
     * already there
     * @param m the MethodSymbol of the method whose specs are provided
     * @param spec the specs to associate with the method
     */
    public void putSpecs(ClassSymbol csym, JCTree.JCBlock m, JmlMethodSpecs spec) {
        if (Utils.jmldebug) System.out.println("            PUTTING BLOCK SPECS " );
        specs.get(csym).blocks.put(m,spec);   // FIXME - what if the type is not present
    }
    
    /** Adds the specs for a given field to the database, overwriting anything
     * already there
     * @param m the VarSymbol of the method whose specs are provided
     * @param spec the specs to associate with the method
     */
    public void putSpecs(VarSymbol m, FieldSpecs spec) {
        if (Utils.jmldebug) System.out.println("            PUTTING FIELD SPECS " + m.enclClass() + " " + m);
        specs.get(m.enclClass()).fields.put(m,spec);   // FIXME - what if the type is not present
    }
    
    /** Retrieves the specs for a given method
     * @param m the MethodSymbol of the method whose specs are wanted
     * @return the specs of the method, or null if none are present
     */
    //@ nullable
    public JmlMethodSpecs getSpecs(MethodSymbol m) {
        TypeSpecs t = specs.get(m.enclClass());
        return t == null ? null : t.methods.get(m);
    }
    
    public JmlMethodSpecs getDenestedSpecs(MethodSymbol m) {
        JmlMethodSpecs s = getSpecs(m);
        if (s == null) return null;
        if (s.deSugared == null) {
            attr.deSugarMethodSpecs(s.decl,s);
        }
        return s.deSugared;
    }
    
    
    /** Retrieves the specs for a given field
     * @param m the VarSymbol of the field whose specs are wanted
     * @return the specs of the field, or null if none are present
     */
    //@ nullable
    public FieldSpecs getSpecs(VarSymbol m) {
        TypeSpecs t = specs.get(m.enclClass());
        return t == null ? null : t.fields.get(m);
    }
    
    /** Retrieves the specs for a given initializer block
     * @param sym the class in which the block resides
     * @param m the JCBlock of the block whose specs are wanted
     * @return the specs of the block, or null if none are present
     */
    //@ nullable
    public JmlMethodSpecs getSpecs(ClassSymbol sym, JCTree.JCBlock m) {
        TypeSpecs t = specs.get(sym);
        return t == null ? null : t.blocks.get(m);
    }
    
    
    /** Finds the first specification file (if any) for the given class.  It
     * searches each directory on the specPath, in order, for a file with a
     * JML suffix (in order), returning the first one found.
     * 
     * @param classSym The Symbol of the class whose specification file is to be found
     * @return The file found, or null if none found
     */
    //@ nullable
    public JavaFileObject findLeadingSpecFile(ClassSymbol classSym) {
        return findLeadingSpecFile(classSym.fullname.toString());
    }
    
    /** Finds the first specification file (if any) for the given class.  It
     * searches each directory on the specPath, in order, for a file with a
     * JML suffix (in order), returning the first one found.
     * 
     * @param className The fully-qualified name of the file to be found, 
     *  without a suffix (or the dot before the suffix) either
     *  dot or forward-slash separated
     * @return The file found, or null if none found
     */
    //@ nullable
    public JavaFileObject findLeadingSpecFile(String className) {
        String s = className.replace('.','/');
        for (Dir dir: specsDirs) {
            JavaFileObject j = dir.findAnySuffixFile(s);
            if (j != null) return j;
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
    public JavaFileObject findSpecFile(String filename) {
        for (Dir dir: specsDirs) {
            JavaFileObject j = dir.findFile(filename);
            if (j != null) return j;
        }
        return null;
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
        
        /** The source file for the specifications */
        //@ nullable   // may be null if there are no specs
        public JavaFileObject file; // FIXME - these may come from different files

        /** The JmlClassDecl from the specification */
        //@ nullable   // may be null if there are no specs
        public JmlClassDecl decl; // FIXME - with a spec sequence the specs from more than one

        /** The JML modifiers of the class, as given in the specification */
        //@ nullable   // may be null if there are no specs
        public JCTree.JCModifiers modifiers;

        // FIXME - document
        //@ nullable
        private JmlToken defaultNullity = null;
        
        /** All the specification clauses for the class (not method clauses or field clauses or block clauses) */
        /*@ non_null */
        public ListBuffer<JmlTree.JmlTypeClause> clauses;

        /** Synthetic methods for model fields (these are also included in the clauses list) */
        /*@ non_null */
        public ListBuffer<JmlTree.JmlTypeClauseDecl> modelFieldMethods = new ListBuffer<JmlTree.JmlTypeClauseDecl>();

        // The following maps are part of the TypeSpecs so that everything associated with a given
        // type can be disposed of at once (by releasing references to the TypeSpecs instance)

        /** A map from methods of the class to the specifications for the method. */
        /*@ non_null */
        public Map<MethodSymbol,JmlMethodSpecs> methods = new HashMap<MethodSymbol,JmlMethodSpecs>();

        /** A map from fields of the class to the specifications for the field. */
        /*@ non_null */
        public Map<VarSymbol,FieldSpecs> fields = new HashMap<VarSymbol,FieldSpecs>();
        
        /** A map from initializers of the class to the specifications for the initializers. */ // FIXME - verify this comment
        /*@ non_null */
        public Map<JCTree.JCBlock,JmlMethodSpecs> blocks = new HashMap<JCTree.JCBlock,JmlMethodSpecs>();

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
        
        // FIXME - comment - only partially fills in the class - used for a binary file - I think everything is pretty much empty and null
        public TypeSpecs(JavaFileObject file, JCTree.JCModifiers mods, ListBuffer<JmlTree.JmlTypeClause> clauses) {
            this.file = file;
            this.decl = null;
            this.modifiers = mods;
            this.clauses = clauses != null ? clauses : new ListBuffer<JmlTree.JmlTypeClause>();
        }
        
        // FIXME - comment - only partially fills in the class
        public TypeSpecs(JmlClassDecl decl) {
            this.file = decl.sourcefile;
            this.decl = decl;
            this.modifiers = decl.mods;
            this.clauses = new ListBuffer<JmlTree.JmlTypeClause>();
        }
        
        // Use when there is no spec for the type symbol (but records the fact
        // that we looked and could not find one)
        public TypeSpecs() {
            this.file = null;
            this.decl = null;
            this.modifiers = null;
            this.clauses = new ListBuffer<JmlTree.JmlTypeClause>();
        }
        
    }
    
    /** Returns the default nullity for the given class - don't call this until
     * classes have been entered and annotations have been attributed.
     * @param csymbol the class whose default nullity is to be determined
     * @return JmlToken.NULLABLE or JmlToken.NONNULL
     */
    //@ requires csymbol != null;
    public JmlToken defaultNullity(ClassSymbol csymbol) {
        if (csymbol == null) {
            if (JmlOptionName.isOption(context,JmlOptionName.NULLABLEBYDEFAULT)) {
                return JmlToken.NULLABLE;
            } else {
                return JmlToken.NONNULL;
            }
        }
        TypeSpecs spec = get(csymbol);
        if (spec.defaultNullity == null) {
            JmlToken t = null;
            if (csymbol.getAnnotationMirrors() != null) {
                if (csymbol.attribute(attr.nullablebydefaultAnnotationSymbol) != null) {
                    t = JmlToken.NULLABLE;
                } else if (csymbol.attribute(attr.nonnullbydefaultAnnotationSymbol) != null) {
                    t = JmlToken.NONNULL;
                }
            } 
            if (t == null) {
                ClassSymbol s = csymbol.enclClass();
                t = defaultNullity(s != csymbol? s : null);
            }
            spec.defaultNullity = t;
        }
        return spec.defaultNullity;
    }

    
// For method specifications, use the JmlTree.JmlMethodSpecs class
//    public static class MethodSpecs {
//        public MethodSpecs(JmlMethodSpecs m) { methodSpecs = m; }
//        public JmlMethodSpecs methodSpecs;
//    }

    /** An ADT to hold the specs for a field declaration */
    public static class FieldSpecs {
        /** A list of the specs for the field, i.e. the in and maps clauses */
        public JCTree.JCModifiers mods;
        public ListBuffer<JmlTree.JmlTypeClause> list = new ListBuffer<JmlTree.JmlTypeClause>();
        public FieldSpecs(JCTree.JCModifiers mods) { 
            this.mods = mods;
        }
    }
    
}

