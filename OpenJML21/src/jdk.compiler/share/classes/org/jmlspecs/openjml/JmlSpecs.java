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
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;

//import org.eclipse.core.runtime.Platform;
import org.jmlspecs.openjml.IJmlClauseKind.ModifierKind;
import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.ext.MethodSimpleClauseExtensions;
import org.jmlspecs.openjml.ext.Modifiers;
import org.jmlspecs.openjml.ext.SingletonExpressions;
import org.jmlspecs.openjml.ext.TypeInitializerClauseExtension;
import org.jmlspecs.openjml.visitors.JmlTreeCopier;

import static org.jmlspecs.openjml.ext.AssignableClauseExtension.*;
import static org.jmlspecs.openjml.ext.SignalsClauseExtension.*;
import static org.jmlspecs.openjml.ext.SignalsOnlyClauseExtension.*;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;
import static org.jmlspecs.openjml.ext.TypeInitializerClauseExtension.*;
import static org.jmlspecs.openjml.ext.MiscExtensions.*;
import static org.jmlspecs.openjml.ext.Modifiers.PURE;
import static org.jmlspecs.openjml.ext.Modifiers.SPEC_PURE;
import static org.jmlspecs.openjml.ext.Modifiers.STRICTLY_PURE;
import static org.jmlspecs.openjml.ext.Modifiers.NO_STATE;
import static org.jmlspecs.openjml.ext.JmlPrimitiveTypes.*;
//import org.osgi.framework.Bundle;
//import org.w3c.dom.Element;

//import com.sun.tools.classfile.Annotation;
import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.Annotate;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Enter;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.file.RelativePath;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.main.Option;
import com.sun.tools.javac.parser.JmlToken;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Position;
import com.sun.tools.javac.util.PropagatedException;

/** This class manages the specifications of various Java entities
 * during a compilation.  There should be just one instance of JmlSpecs
 * per compilation Context, ensured by calling the preRegister
 * method.  The class provides methods for finding specification files, and it
 * maintains a database of specifications of types, methods, and fields.  
 * The specs are indexed by class 
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
 * In addition, by default, the specs path has $SY appended to it.
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
    
    private final static boolean debugSpecs = org.jmlspecs.openjml.Utils.debug("specs");
    
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
    
    /** The Names tool for this context */
    final protected Names names;
    
    /** The Utils tool for this context */
    final protected Utils utils;
    
    /** The map giving the accumulated specifications for a given type */
    final protected Map<TypeSymbol,TypeSpecs> specsTypes = new HashMap<>();
    final protected Map<MethodSymbol,MethodSpecs> specsMethods = new HashMap<>();
    final protected Map<VarSymbol,FieldSpecs> specsFields = new HashMap<>();
    final protected Map<VarSymbol,VarSpecs> specsFormals = new HashMap<>();
    
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
        names = Names.instance(context);
    }
    
    /** Initializes the specs path given the current settings of options.
     */
    public void initializeSpecsPath() {
        Options options = Options.instance(context);
        String s = JmlOption.value(context,JmlOption.SPECS);
        if (debugSpecs) System.out.println("specs: specspath option: " + s);
        if (s == null || s.isEmpty()) s = System.getProperty(Strings.specsPathEnvironmentPropertyName);
        if (debugSpecs) System.out.println("specs: system property: " + s);
        if (s == null || s.isEmpty()) s = getSourcePathString();
        if (debugSpecs) System.out.println("specs: sourcepath value: " + s);
        setSpecsPath(s);
    }
    
    /** This method looks for the internal specification directories and, if
     * found, appends them to the argument. 
     * @param dirs the list to which to append the internal spec directories
     * @return true if any found, false if not
     */
    public boolean appendInternalSpecs(boolean verbose, java.util.List<Dir> dirs) {
        PrintWriter noticeWriter = log.getWriter(WriterKind.NOTICE);
        boolean print = verbose || Utils.debug("paths");
        
        // Look for specs in a file on the classpath
        // If present, use it.
        // Otherwise look use the default installation.
        
        String sp = System.getProperty("java.class.path");
        String[] ss = sp.split(java.io.File.pathSeparator);
        Dir d;
        
        
        // See if there is any jar file on the classpath that contains
        // specs files at the top-level
        
        for (String s: ss) {
            if (s.endsWith(".jar")) {
                d = new JarDir(s,"");
                if (d.exists() && d.findFile("java/lang/Object.jml") != null) {
                    if (print) noticeWriter.println("Using specs on classpath [Jar: " + s + "]: " + d);
                    dirs.add(d);
                    return true;
                }
            }
            File f = new File(s + "/java/lang/Object.jml");
            if (f.exists()) {
                if (print) noticeWriter.println("Using specs on classpath [Dir: " + s + "]: " + f.getAbsolutePath());
                dirs.add(new FileSystemDir(f.getAbsolutePath()));
                return true;
            }
        }
                
        // Default for test or install environment
        if (Main.root != null) {
            String sy = Main.root + "/specs"; // expected for installation
            if (!new File(sy).exists()) {
            	sy = Main.root + "/../Specs/specs"; // expected for development
            }
            try { sy = new File(sy).getCanonicalPath(); } catch (IOException e) {}
            
            File f = new File(sy);
            if (f.exists() && f.isDirectory()) {
                if (print) noticeWriter.println("Using internal specs [Root: " + Main.root + "]:" + sy);
                dirs.add(new FileSystemDir(f.getAbsolutePath()));
                return true;
            } else {
            	log.error("jml.internal.specs.dir.not.exist",sy);
            }
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
    public String getSourcePathString() {
        boolean p = Utils.debug("paths");
        Options options = Options.instance(context);
        String s = options.get(Strings.sourcepathOptionName);
        if (p) System.out.println("sourcepath: option: " + s);
        if (s == null || s.isEmpty()) s = getClassPathString();
        if (p) System.out.println("sourcepath: cp: " + s);
        return s;
    }
    public String[] getSourcePath() {
        return getSourcePathString().split(java.io.File.pathSeparator);
    }
    
    public String getClassPathString() {
        boolean p = Utils.debug("paths");
        Options options = Options.instance(context);
        String s = options.get(Strings.classpathOptionName);
        if (p) System.out.println("classpath: option: " + s);
        if (s == null) s = System.getProperty("java.class.path"); // This is empty if not set rather than null
        if (p) System.out.println("classpath: java.class.path: " + s);
        if (s == null || s.isEmpty()) s = ".";
        if (p) System.out.println("classpath: default: " + s);
        return s;
    }
    public String[] getClassPath() {
        return getClassPathString().split(java.io.File.pathSeparator);
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
        boolean verbose = utils.verbose() ||
            Options.instance(context).get(Option.VERBOSE.getPrimaryName()) != null;
        PrintWriter noticeWriter = log.getWriter(WriterKind.NOTICE);

        specsDirs = new LinkedList<Dir>();
        List<String> todo = new LinkedList<String>();
        for (int i = 0; i<specsPathArray.length; i++) {
            String s = specsPathArray[i];
            if (s == null || s.length() == 0) continue;
            todo.add(s);
        }
        String dir;
        boolean checkDirectories = JmlOption.isOption(context,JmlOption.CHECKSPECSPATH);
        //if (JmlOption.isOption(context,JmlOption.INTERNALSPECS)) {
            todo.add("$SY");
        //}

        String cwd = System.getProperty("user.dir");
        
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
                    if (!todo.isEmpty()) utils.warning("jml.bad.sp.var","$SY");
                } else {
                    syIncluded = true;
                    String dirs = Options.instance(context).get(Strings.systemSpecsLocationEnvironmentPropertyName);
                    if (dirs != null) pushback(dirs,todo);
                    else {
                        if (!appendInternalSpecs(verbose,getSpecsPath())) {
                            utils.warning("jml.no.internal.specs");
                        }
                    }
                }
            } else if (dir.equals("$CP")) {
                if (cpIncluded) {
                    utils.warning("jml.bad.sp.var","$CP");
                } else {
                    cpIncluded = true;
                    String dirs = Options.instance(context).get(Option.CLASS_PATH.getPrimaryName());
                    if (dirs == null) dirs = System.getProperty("java.class.path");
                    if (dirs != null) pushback(dirs,todo);
                }
            } else if (dir.equals("$ECP")) {
                if (ecpIncluded) {
                    utils.warning("jml.bad.sp.var","$ECP");
                } else {
                    ecpIncluded = true;
                    String dirs = System.getProperty("java.class.path");
                    if (dirs != null) pushback(dirs,todo);
                }
            } else if (dir.equals("$SP")) {
                if (spIncluded) {
                    utils.warning("jml.bad.sp.var","$SP");
                } else {
                    spIncluded = true;
                    String dirs = Options.instance(context).get(Option.SOURCE_PATH.getPrimaryName());
                    if (dirs != null) pushback(dirs,todo);
                }
            } else if (dir.length()>0){
                Dir d = make(dir);
                if (d != null) {
                    if (checkDirectories && !d.exists()) { 
                        utils.warning("jml.specs.dir.not.exist",d + " (" + cwd + ")");
                    }
                    specsDirs.add(d);
                } else {
                    // At present make always returns non-null
                    utils.error("jml.internal.notsobad","Failed to create a directory path entry from " + dir);
                }
            }
        }
        if (debugSpecs) {
            noticeWriter.print("specspath:");
            for (Dir s: specsDirs) {
                noticeWriter.print(" ");
                noticeWriter.print(s);
            }
            Options options = Options.instance(context);
            noticeWriter.println("");
            noticeWriter.println("sourcepath: " + options.get("--source-path"));
            noticeWriter.println("classpath: " + options.get("--class-path"));
            noticeWriter.println("java.class.path: " + System.getProperty("java.class.path"));
            noticeWriter.flush();
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
                return ((JavacFileManager)context.get(JavaFileManager.class)).getJavaFileObject(f.toPath());
            }
            return null;
        }
        
        @Override
        public /*@Nullable*/JavaFileObject findAnySuffixFile(String filePath) {
            for (String suffix : Strings.suffixes) {
                File f = new File(dir,filePath + suffix);
                if (f.exists()) {
                    return ((JavacFileManager)context.get(JavaFileManager.class)).getJavaFileObject(f.toPath());
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
        public /*@Nullable*/JavaFileObject findFile(String filePath) { 
            RelativePath file = new RelativePath.RelativeFile(internalDir,filePath);
            if (zipArchive == null) return null;
            ZipEntry entry = zipArchive.getEntry(file.toString());
            if (entry == null) return null;
            // FIXME return zipArchive.getFileObject(internalDir,filePath);
            return null;
        }
        
        @Override
        public /*@Nullable*/JavaFileObject findAnySuffixFile(String filePath) { 
            if (zipArchive == null) return null;
            for (String suffix : Strings.suffixes) {
                String ss = filePath + suffix;
                RelativePath file = new RelativePath.RelativeFile(internalDir,ss);
                if (zipArchive.getEntry(file.toString()) == null) continue;
                // FIXME JavaFileObject j = zipArchive.getFileObject(internalDir,ss);
                // if (j != null) return j;
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
    public JavaFileObject findSpecFile(String classFlatName) {
        String s = classFlatName.replace('.','/');
        String suffix = Strings.specsSuffix; 
        for (Dir dir: getSpecsPath()) {
        	if (false) System.out.println("parser+: TRYING " + dir + " " + s + suffix);
        	JavaFileObject j = dir.findFile(s + suffix);
        	if (j != null) return j;
        }
        return null;
    }
    
    public JavaFileObject findSpecFile(ClassSymbol classSym) {
        return findSpecFile(classSym.toString());
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
    
//    /** A debugging method that prints the content of the specs database */
    public void printDatabase() {
//        PrintWriter noticeWriter = log.getWriter(WriterKind.NOTICE);
//        try {
//            for (Map.Entry<TypeSymbol,TypeSpecs> e : specsmap.entrySet()) {
//                String n = e.getKey().flatName().toString();
//                JavaFileObject f = e.getValue().file;
//                noticeWriter.println(n + " " + (f==null?"<NOFILE>":f.getName()));
//                ListBuffer<JmlTree.JmlTypeClause> clauses = e.getValue().clauses;
//                noticeWriter.println("  " + clauses.size() + " CLAUSES");
//                for (JmlTree.JmlTypeClause j: clauses) {
//                    noticeWriter.println("  " + JmlPretty.write(j));
//                }
//                noticeWriter.println("  " + e.getValue().methods.size() + " METHODS");
//                for (MethodSymbol m: e.getValue().methods.keySet()) {
//                    MethodSpecs sp = getSpecs(m);
//                    noticeWriter.println("  " + JmlPretty.write(sp.mods));
//                    noticeWriter.println(" " + m.enclClass().toString() + " " + m.flatName());
//                    noticeWriter.print(JmlPretty.write(sp.cases));
//                    //log.noticeWriter.println(sp.toString("     "));
//                }
//                noticeWriter.println("  " + e.getValue().fields.size() + " FIELDS");
//                for (VarSymbol m: e.getValue().fields.keySet()) {
//                    FieldSpecs sp = getSpecs(m);
//                    noticeWriter.print("  " + JmlPretty.write(sp.mods));
//                    noticeWriter.println(" " + m.enclClass().toString() + " " + m.flatName());
//                    for (JmlTypeClause t: sp.list) {
//                        noticeWriter.print(JmlPretty.write(t));
//                        //noticeWriter.println(sp.toString("     "));
//                    }
//                }
//            }
//            noticeWriter.println("MOCK FILES");
//            for (String s: mockFiles.keySet()) {
//                noticeWriter.println(s + " :: " + mockFiles.get(s));
//            }
//        } catch (Exception e) {
//            noticeWriter.println("Exception occurred in printing the database: " + e);
//        }
    }
    
    
    /** Retrieves the current stored specifications for the given type -- may be null if they have
     * not yet been 'put', and may not be attributed
     */
    //@ nullable 
    public TypeSpecs get(ClassSymbol type) {
        return specsTypes.get(type);
    }
    
    public TypeSpecs getLoadedSpecs(ClassSymbol classSym) {
    	if (status(classSym).less(SpecsStatus.SPECS_LOADED)) {
    	    boolean ok = JmlEnter.instance(context).requestSpecs(classSym);
            //if (!ok) System.out.println("REQUEST TO GET SPECS ONLY QUEUED: " + classSym);
    	}
    	var ts = get(classSym);
    	if (ts == null) {
    		ts = new TypeSpecs(classSym, null, (JmlModifiers)JmlTree.Maker.instance(context).Modifiers(classSym.flags()), null);
            utils.note(true,"      inserting default class specs for " + classSym.flatname);
    		specsTypes.put(classSym,  ts);
    	}
    	return ts;
    }
    
    /** Returns loaded specs: modifiers are present; specification cases may be present, 
     * but are not necessarily attributed.
     */
    //@ non_null
    public JmlTree.JmlModifiers getSpecsModifiers(ClassSymbol m) {
    	return getLoadedSpecs(m).modifiers;
    }
    
    public TypeSpecs getAttrSpecs(ClassSymbol csym) {
    	if (status(csym).less(SpecsStatus.SPECS_ATTR)) {
    		attr.attrSpecs(csym);
    	}
        return getLoadedSpecs(csym);
    }
    
    public void getAttrSpecs(Symbol s) {
    	if (s instanceof ClassSymbol cs) getAttrSpecs(cs);
    	if (s instanceof MethodSymbol ms) getAttrSpecs(ms);
    	if (s instanceof VarSymbol vs) getAttrSpecs(vs);
    }
    
//    /** Retrieves the specifications for a given type, providing and registering
//     * a default if one is not there
//     * @param type the ClassSymbol of the type whose specs are wanted
//     * @return the specifications
//     */
//    public TypeSpecs initializeAndGetSpecs(ClassSymbol type) {
//        TypeSpecs t = specsmap.get(type);
//        if (t == null) {
//            specsmap.put(type, t=new TypeSpecs(type));
//        }
//        return t;
//    }
    
    /** Deletes the specs for a given type, including all method and field
     * specs for that type.
     * @param type the type whose specs are to be deleted
     */
    public void deleteSpecs(ClassSymbol type) {
        specsTypes.put(type, null);
    }
    
    
    /** Adds the specs for a given type to the database, overwriting anything
     * already there
     * @param type the ClassSymbol of the type whose specs are provided
     * @param spec the specs to associate with the type
     */
    public void putSpecs(ClassSymbol type, TypeSpecs spec) {
        //if (type.toString().endsWith(".Object")) System.out.println("PUTSPECS " + type + " " + ((JCClassDecl)spec.specsEnv.tree).sym + " " + spec);
        spec.csymbol = type;
        specsTypes.put(type,spec);        
        setStatus(type, SpecsStatus.SPECS_LOADED);
    	if (utils.verbose()) utils.note("      Saving class specs for " + type.flatname + (spec.specDecl == null ? " (null declaration)": " (non-null declaration)"));
    }
    
    public void removeSpecs(ClassSymbol type) {
        specsTypes.remove(type);
    }
    
    /** Adds the specs for a given method to the database, overwriting anything
     * already there.  There must already be a specs entry for the owning class
     * @param m the MethodSymbol of the method whose specs are provided
     * @param spec the specs to associate with the method
     */
    public void putSpecs(MethodSymbol specSym, MethodSpecs spec) {
    	//if (specSym.owner.toString().contains("Object") && specSym.toString().contains("toString")) { System.out.println("SAVE " + specSym.owner + " " + specSym + " " + spec);  Utils.dumpStack(); }
    	spec.specSym = specSym;
        specsMethods.put(specSym,spec);
        int i = 0;
        var decl = spec.specDecl == null ? spec.javaDecl : spec.specDecl;
        if (decl != null) {
            if (specSym.params == null) System.out.println("NULL PARAMS " + specSym);
            var iter = specSym.params.iterator();
            for (JCVariableDecl d: decl.params) {
                boolean nn = isNonNullFormal(d.type, i++, spec, specSym);
                var f = new LocalSpecs((JmlVariableDecl)d, nn, specSym);
                var jsym = iter.next();
                specsFormals.put(jsym, f);
                // System.out.println("    Formal specs " + d.sym + " " + jsym.hashCode() + " " +  specSym + " " + f.isNonNull + " " + f.mods);
            }
        }
        spec.returnNonNull = findNonNullReturn(specSym, decl);
        if (utils.verbose()) utils.note("            Saving method specs for " + specSym.owner + "." + specSym + " " + specSym.hashCode() + " " + spec.returnNonNull);
        setStatus(specSym, SpecsStatus.SPECS_LOADED);
    }
    
    public boolean findNonNullReturn(MethodSymbol sym, JCMethodDecl specDecl) {
        if (specDecl != null) {
//            if (specDecl.name.toString().equals("n")) {
//                System.out.println("FNNR " + specDecl.mods + " : " + specDecl.restype);
//                System.out.println("    " + hasTypeAnnotation(specDecl.restype, Modifiers.NON_NULL) + " " +
//                        hasTypeAnnotation(specDecl.restype, Modifiers.NULLABLE) + " " + 
//                        findModifier(specDecl, Modifiers.NON_NULL) + " " + findModifier(specDecl, Modifiers.NON_NULL) + " " +
//                        findAnnotation(specDecl.mods.annotations, Modifiers.NON_NULL) + " " + findAnnotation(specDecl.mods.annotations, Modifiers.NULLABLE) + " " 
//                        + defaultNullity((ClassSymbol)sym.owner)
//                );
//            }
            if (hasTypeAnnotation(specDecl.restype, Modifiers.NON_NULL)) return true;
            if (hasTypeAnnotation(specDecl.restype, Modifiers.NULLABLE)) return false;
            if (findModifier(specDecl, Modifiers.NON_NULL)) return true;
            if (findModifier(specDecl, Modifiers.NULLABLE)) return false;
            if (findAnnotation(specDecl.mods.annotations, Modifiers.NON_NULL) != null) return true;
            if (findAnnotation(specDecl.mods.annotations, Modifiers.NULLABLE) != null) return false;
        }
        return defaultNullity((ClassSymbol)sym.owner) == Modifiers.NON_NULL;
    }
    
    public boolean findModifier(JCMethodDecl decl, ModifierKind kind) {
        JmlModifiers jmods = (JmlModifiers)decl.mods;
        for (var m: jmods.jmlmods) if (m.jmlclausekind == kind) return true;
        return false;
    }
    
    public boolean findModifier(JCVariableDecl decl, ModifierKind kind) {
        JmlModifiers jmods = (JmlModifiers)decl.mods;
        for (var m: jmods.jmlmods) if (m.jmlclausekind == kind) return true;
        return false;
    }
    
    public void putAttrSpecs(MethodSymbol specSym, MethodSpecs spec) {
    	putSpecs(specSym, spec);
    	setStatus(specSym, SpecsStatus.SPECS_ATTR);
    }

    
    public void dupSpecs(MethodSymbol m, MethodSymbol old) {
    	var spec = getLoadedSpecs(old);
    	specsMethods.put(m, spec);
    	setStatus(m, status(old));
    }

    
    /** Adds the specs for a given initialization block to the database, overwriting anything
     * already there.  The type must already have a spec supplied, to which this
     * is added.
     * @param csym the class to which the initialilzation block belongs
     * @param m the Block whose specs are provided
     * @param spec the specs to associate with the block
     */
    public void putSpecs(ClassSymbol csym, JCTree.JCBlock m, MethodSpecs spec) {
    	if (utils.verbose()) utils.note("            Saving initializer block specs " );
        specsTypes.get(csym).blocks.put(m,spec);
    }
    
    /** Adds the specs for a given field to the database, overwriting anything
     * already there.  The type must already have a class specs, to which
     * this is added.
     * @param m the VarSymbol of the method whose specs are provided
     * @param spec the specs to associate with the method
     */
    public void putSpecs(VarSymbol m, JmlVariableDecl decl, VarSpecs spec) {
        if (spec != null) {
            spec.isNonNull = computeVarNullness(decl, m.owner);
        }
        specsFormals.put(m, spec);
        setStatus(m, SpecsStatus.SPECS_LOADED);
        if (utils.verbose()) utils.note("            Saving local/formal specs for " + m.owner + " " + m + " " + status(m) + " " + m.hashCode());
    }
    
    public void putSpecs(VarSymbol m, FieldSpecs spec) {
        if (spec != null) {
            spec.isNonNull = computeVarNullness(spec.decl, m.owner);
        }
        specsFields.put(m, spec);
        setStatus(m, SpecsStatus.SPECS_LOADED);
        //if (m.owner.toString().contains("Throwable")) System.out.println("            Saving field specs for " + m.owner + " " + m + " " + status(m) + " " + m.hashCode());
        if (utils.verbose()) utils.note("            Saving field specs for " + m.owner + " " + m + " " + status(m) + " " + m.hashCode() + " " + spec.isNonNull);
    }
    
    public boolean computeVarNullness(JmlVariableDecl decl, Symbol owner) {
        if (decl != null) {
            //System.out.println("CVN " + decl + " " + hasTypeAnnotation(decl.vartype, Modifiers.NULLABLE) + " " + decl.mods.annotations + " " + findAnnotation(decl.mods.annotations, Modifiers.NULLABLE));
            JmlModifiers jmods = (JmlModifiers)decl.mods;
            if (findModifier(decl, Modifiers.NON_NULL)) return true;
            if (findModifier(decl, Modifiers.NULLABLE)) return false;
            if (findAnnotation(jmods.annotations, Modifiers.NON_NULL)!=null) return true;
            if (findAnnotation(jmods.annotations, Modifiers.NULLABLE)!=null) return false;
            if (hasTypeAnnotation(decl.vartype, Modifiers.NON_NULL)) return true;
            if (hasTypeAnnotation(decl.vartype, Modifiers.NULLABLE)) return false;
            if (utils.isOnlyDatagroup(decl.type)) return false;
            //if (decl.vartype.toString().contains("JMLDataGroup")) return false; // A primitive type
        }
        if (owner instanceof MethodSymbol m) owner = m.owner;
        return defaultNullity((ClassSymbol)owner) == Modifiers.NON_NULL;
    }
    
    /** Retrieves the attributed specs for a given method, possibly default specs;
     *  these will be attributed but not desugared specs.
     * @param m the MethodSymbol of the method whose specs are wanted
     * @return the specs of the method
     */
    //@ non_null
    public MethodSpecs getAttrSpecs(MethodSymbol m) {
    	if (status(m).less(SpecsStatus.SPECS_ATTR)) {
    		attr.attrSpecs(m, null);
    	}
        return get(m);
    }
    
    /** Returns loaded specs: modifiers are present; specification cases may be present, 
     * but are not necessarily attributed.
     */
    //@ non_null
    public JmlTree.JmlModifiers getSpecsModifiers(MethodSymbol m) {
    	MethodSpecs ms = getLoadedSpecs(m);
    	return ms == null ? null : (JmlTree.JmlModifiers)ms.mods; // FIXME - can this ever be null?
    }
    
    /** Returns loaded specs: modifiers are present; specification cases may be present, 
     * but are not necessarily attributed; does not fill in default specs, so may return null
     * if no specification file is found.
     */
    //@ nullable // FIXME - really?
    public MethodSpecs getLoadedSpecs(MethodSymbol m) {
        boolean print = false; // m.owner.toString().equals("java.lang.Object") && m.toString().contains("toString");
        if (m.enclClass() != m.owner) System.out.println("Unexpected difference - method " + m + " " + m.owner + " " + m.enclClass());
    	if (print) System.out.println(" STATUS " + m.owner + " " + m + " " + status(m.owner));
        if (status(m.owner).less(SpecsStatus.SPECS_LOADED)) {
    		var ms = getLoadedSpecs((ClassSymbol)m.owner);
            if (print) System.out.println(" GOT CLASS SPECS " + m.owner );
    		if (ms == null) setStatus(m, SpecsStatus.SPECS_LOADED); // FIXME - why this?
//        	if (ms == null) {
//        		setStatus(m, SpecsStatus.SPECS_LOADED);// So defaultSpecs does not go into an infinite loop
//                if (utils.verbose()||true) {
//                	System.out.println("Null specs returned from getLoadedSpecs (inserting defaults) for " + m.owner + " " + m + " " + m.hashCode());
//                	if (m.toString().equals("append(java.lang.CharSequence)")) Utils.dumpStack();
//                }
//        		ms = defaultSpecs(null,m,Position.NOPOS); 
//        		specsMethods.put(m,ms);
//        	}
    	}
    	var ms = get(m);
        if (print) System.out.println(" GLS " + m.owner + " " + m + " " + ms);
//        if (ms == null) System.out.println("Null specs returned from getLoadedSpecs (no default) for " + m.owner + " " + m + " " + status(m) + " " + m.hashCode());
        return ms;
    }
    
    public MethodSpecs getLoadedOrDefaultSpecs(MethodSymbol m, int pos) {
        var ms = getLoadedSpecs(m);
        if (ms == null) {
            ms = defaultSpecs(null, m, pos);
            putSpecs(m, ms);
            setStatus(m, SpecsStatus.SPECS_ATTR);
        }
        return ms;
    }
    
    /** Returns precisely what is in the current specs data base -- may be null */
    //@ nullable
    public MethodSpecs get(MethodSymbol m) {
    	return specsMethods.get(m);
    }
    
    /** Retrieves attributed, desugared specs */
    public JmlMethodSpecs getDenestedSpecs(MethodSymbol m) {
        MethodSpecs s = getAttrSpecs(m);
        //System.out.println("DENEST " + m + " " + s);
        if (s == null) {
        	// FIXME - recheck the conditions undere which this branch can be taken
            // This can happen when -no-internalSpecs is used, probably for a binary class, but it probably shouldn't - specs should be created when the class is laoded - FIXME
            // This can also happen for a method that has no JML declaration or specification in its static class,
            // but does inherit a method (and spec) from a parent class.
            s = defaultSpecs(null,m,Position.NOPOS);
            putAttrSpecs(m,s);
            s.cases.deSugared = s.cases;
            return s.cases;    // FIXME - this is not actually fully desugared, but we don't have a decl to call deSugarMethodSpecs
        }
        if (s.cases.deSugared == null) {
            //System.out.println("DESUGARING " + m + " " + s);
            attr.deSugarMethodSpecs(m,s);
        }
        //System.out.println("DESUGARED " + m + " " + s.cases.deSugared);
        return s.cases.deSugared;
    }
    
    // TODO - document
    // FIXME - this needs to be made consistent with the below
    public MethodSpecs defaultSpecs(JmlMethodDecl m) {
        return defaultSpecs(m, m.sym, m.pos);
    }

    // TODO - document
    public MethodSpecs defaultSpecs(/*@ nullable */ JmlMethodDecl decl, MethodSymbol sym, int pos) {
        // decl can be null in the case of Enum.values(), and others
        JmlTree.Maker M = JmlTree.Maker.instance(context);
        Symtab syms = Symtab.instance(context);
        JmlTreeUtils treeutils = JmlTreeUtils.instance(context);
        JmlMethodSpecs ms = M.at(pos).JmlMethodSpecs(com.sun.tools.javac.util.List.<JmlSpecificationCase>nil());
        ms.decl = decl;
        ms.deSugared = null;
        JCTree.JCModifiers mods = M.at(pos).Modifiers(sym.flags() & Flags.AccessFlags);
        if (decl != null) mods = decl.mods; // Caution -- these are now aliased
        MethodSpecs mspecs = new MethodSpecs(mods,ms); // FIXME - empty instead of null modifiers?
        if (decl != null) mspecs.modelBody = decl.body;
        
        List<MethodSymbol> parents = utils.parents(sym,true);
        
        if (decl == null) {
            if (parents.size() > 1) {
                // This is the case (at least) of a binary class B with method m, that is not 
                // declared and has no specs in a JML file, but does override a method in a 
                // parent class P. B.m then adds no specification cases.
                java.util.ListIterator<MethodSymbol> iter = parents.listIterator(parents.size()-1);
                MethodSpecs parentSpecs = getLoadedSpecs(iter.previous());
                mspecs.cases.decl = decl = parentSpecs == null ? null : parentSpecs.cases.decl;
                mspecs.cases.cases = com.sun.tools.javac.util.List.<JmlSpecificationCase>nil();
                mspecs.cases.deSugared = mspecs.cases;
                putAttrSpecs(sym, mspecs);
                return mspecs;
            } else {
                // This is a binary method that has no JML declaration and does not override
                // anything. There is no declaration to co-opt. The method gets a standard
                // default specification.
            }
        }
        
        MethodSymbol superSym = null;
        if ((sym.flags() & Flags.GENERATEDCONSTR) != 0) {
        	var iter = ((ClassSymbol)sym.owner).getSuperclass().tsym.members().getSymbols(s->s.isConstructor() && s.type.getParameterTypes().size() == sym.type.getParameterTypes().size()).iterator();
        	if (iter.hasNext()) superSym = (MethodSymbol)iter.next();
        }
        


        // FIXME - check the case of a binary generated constructor with a declaration in JML
        if (((sym.flags() & Flags.GENERATEDCONSTR) != 0 && superSym != null && attr.isPureMethod(superSym)) 
            || ( sym.owner == syms.objectType.tsym && sym.isConstructor()) 
            || sym.owner == Symtab.instance(context).enumSym ) {
            JmlMethodClause clp = M.at(pos).JmlMethodClauseStoreRef(assignableID, assignableClauseKind,
                    com.sun.tools.javac.util.List.<JCExpression>of(new JmlTree.JmlStoreRefKeyword(pos,nothingKind)));
            if (sym.isConstructor()) {
                //JCAnnotation annotation = org.jmlspecs.openjml.Utils.instance(context).modToAnnotationAST(Modifiers.PURE, pos, pos);
                //var envv = JmlEnter.instance(context).tlenv; // Enter.instance(context).getEnv();
                //attr.attribAnnotationTypes(com.sun.tools.javac.util.List.<JCAnnotation>of(annotation), envv);
                //JCFieldAccess fa = (JCTree.JCFieldAccess)annotation.annotationType;
                //fa.sym = JmlAttr.instance(context).modToAnnotationSymbol.get(Modifiers.PURE);
                //annotation.type = fa.type = fa.sym.type;
                
                addModifier(pos, Modifiers.PURE, mods);
            }

            JmlMethodClauseSignals sig = M.at(pos).JmlMethodClauseSignals(signalsID, signalsClauseKind, null, JmlTreeUtils.instance(context).falseLit);
            JCModifiers csm = M.at(pos).Modifiers(mods.flags & Flags.AccessFlags);
            JmlSpecificationCase cs = M.at(pos).JmlSpecificationCase( csm, false, MethodSimpleClauseExtensions.behaviorClause,null,com.sun.tools.javac.util.List.<JmlMethodClause>of(clp,sig),null);
            mspecs.cases.cases = com.sun.tools.javac.util.List.<JmlSpecificationCase>of(cs);
            JmlSpecs.instance(context).putSpecs(sym, mspecs); // FIXME - are the specs attributed or not
            return mspecs;
        } else if ((sym.owner.flags() & Flags.RECORD) != 0) { // Only generate default record specs for esc
            if (utils.esc && sym.isConstructor() && (sym.flags() & Flags.GENERATEDCONSTR) != 0) {
                ListBuffer<JmlMethodClause> clauses = new ListBuffer<>();
                for (VarSymbol param: sym.params) { 
                    Symbol field = sym.owner.members().findFirst(param.name, s->!(s instanceof MethodSymbol));
                    // At this point thisSymbol is not yet available, so we can't make the expression this.x == x
                    // Instead we make just x == x, with the lhs having the symbol of the field and the rhs the symbol
                    // of the parameter. This appears to work OK for JmlAssertionAdder
                    var rhs = M.at(pos).Ident(param);
                    var fi = treeutils.makeIdent(pos, field);
                    var eq = treeutils.makeEqObject(pos, fi, rhs);
                    JmlMethodClause ens = M.at(pos).JmlMethodClauseExpr(ensuresID, ensuresClauseKind, eq);
                    clauses.add(ens);
                }
                var csm = M.Modifiers(Flags.PUBLIC);
                JmlSpecificationCase cs = M.at(pos).JmlSpecificationCase( csm, false, MethodSimpleClauseExtensions.normalBehaviorClause,null,clauses.toList(),null);
                mspecs.cases.cases = com.sun.tools.javac.util.List.<JmlSpecificationCase>of(cs);
                addModifier(pos, Modifiers.PURE, mods);
                JmlSpecs.instance(context).putSpecs(sym, mspecs);
                return mspecs;
            } else if (sym.name.toString().equals("toString")) {
            } else if (sym.name.toString().equals("hashCode")) {
            } else if (sym.name.toString().equals("equals")) {
            } else if (sym.params.length() == 0) {
                Symbol field = sym.owner.members().findFirst(sym.name, s->!(s instanceof MethodSymbol));
                if (field != null) {
                    var cspecs = getAttrSpecs((ClassSymbol)sym.owner);
                    var thissym = cspecs.javaDecl.thisSymbol;
                    ListBuffer<JmlMethodClause> clauses = new ListBuffer<>();
                    if (utils.esc) { 
                        JmlMethodClause clp = M.at(pos).JmlMethodClauseStoreRef(assignableID, assignableClauseKind,
                                com.sun.tools.javac.util.List.<JCExpression>of(new JmlTree.JmlStoreRefKeyword(pos,nothingKind)));
                        clauses.add(clp);
                        var nm = sym.name;
                        var res = M.at(pos).JmlSingleton(SingletonExpressions.resultKind);
                        res.type = field.type;
                        var id = M.at(pos).Ident(names._this);
                        id.sym = thissym;
                        id.type = sym.owner.type;
                        var fa = M.at(pos).Select(id, nm);
                        fa.type = field.type;
                        fa.sym = field;
                        var eq = treeutils.makeEqObject(pos, res, fa);
                        JmlMethodClause reads = M.at(pos).JmlMethodClauseStoreRef(readsID, accessibleClauseKind, 
                                com.sun.tools.javac.util.List.<JCExpression>of(fa));
                        clauses.add(reads);
                        JmlMethodClause ens = M.at(pos).JmlMethodClauseExpr(ensuresID, ensuresClauseKind, eq);
                        clauses.add(ens);
                    }
                    var csm = M.Modifiers(Flags.PUBLIC|Flags.FINAL);
                    JmlSpecificationCase cs = M.at(pos).JmlSpecificationCase( csm, false, MethodSimpleClauseExtensions.normalBehaviorClause,null,clauses.toList(),null);
                    mspecs.cases.cases = com.sun.tools.javac.util.List.<JmlSpecificationCase>of(cs);
                    addModifier(pos, Modifiers.STRICTLY_PURE, mods);
                    JmlSpecs.instance(context).putSpecs(sym, mspecs);
                    return mspecs;

                }
            }
            // FIXME - this case should happen only if parent constructors are pure and have no signals clause
        } else xx: if ((sym.owner.flags() & Flags.ENUM) != 0 && !sym.isConstructor()) {
            JmlMethodClause clp = M.at(pos).JmlMethodClauseStoreRef("assignable", assignableClauseKind,
                    com.sun.tools.javac.util.List.<JCExpression>of(new JmlTree.JmlStoreRefKeyword(pos,nothingKind)));
            JmlMethodClause clpa = M.at(pos).JmlMethodClauseStoreRef("accessible", accessibleClauseKind,
                    com.sun.tools.javac.util.List.<JCExpression>of(new JmlTree.JmlStoreRefKeyword(pos,nothingKind)));
            JmlMethodClauseSignals sig = M.at(pos).JmlMethodClauseSignals("signals", signalsClauseKind, null, JmlTreeUtils.instance(context).falseLit);
            JCExpression res = M.at(pos).JmlSingleton(SingletonExpressions.resultKind);
            res.setType(sym.type.asMethodType().restype); // sym.type might be a Type.ForAll
            JCBinary resnn = treeutils.makeNotNull(pos,res);
            JmlMethodClauseExpr en = M.at(pos).JmlMethodClauseExpr("ensures", ensuresClauseKind, resnn);
            List<Symbol> elems = sym.owner.getEnclosedElements();
            int count = 0;
            for (Symbol s: elems) if ((s.flags() & Flags.ENUM) != 0 && s instanceof VarSymbol) {
                count++;
            }
            JCModifiers csm = M.at(pos).Modifiers(mods.flags & Flags.AccessFlags);
            com.sun.tools.javac.util.List<JmlMethodClause> clauses;
            if (sym.name.equals(names.values)) {
                clauses = com.sun.tools.javac.util.List.<JmlMethodClause>nil();

                // Default specs for the values() method of an Enum
                // public behavior
                //    [requires true;]
                //    ensures \result == <Enum>._JMLvalues;
                //    assignable \nothing;
                //    accessible \nothing;
                //    signals() false;
                //    ensures \result != null;
                //    ensures \result.length == <number of elements in enum>
                //    for the ith enum item    ensures _JMLvalues[i] == item   // TODO
                
                Name nv = names.fromString("_JMLvalues");
                JCFieldAccess valf = treeutils.makeSelect(pos, treeutils.makeIdent(pos, sym.owner), nv);
                valf.type = res.type;
                for (Symbol s: sym.owner.getEnclosedElements()) {
                    if (s.name == nv) {
                        valf.sym = s;
                    }
                }
                JCExpression fa = treeutils.makeArrayLength(pos, res); // \result.length
                JCBinary len = M.at(pos).Binary(JCTree.Tag.EQ, fa, treeutils.makeIntLiteral(pos,count).setType(syms.intType));
                len.operator = treeutils.inteqSymbol;
                len.setType(syms.booleanType);  // len: // \result.length == [[count]]
                JmlMethodClauseExpr enn = new JmlTree.JmlMethodClauseExpr(pos, ensuresID, ensuresClauseKind,len); // ensures \result.length == [[count]]
                JCExpression val = treeutils.makeEqObject(pos, res, valf);
                // ensures \result == <Enum>._JMLvalues;
                JmlMethodClause cval = M.at(pos).JmlMethodClauseExpr(ensuresID, ensuresClauseKind,val);
                clauses = com.sun.tools.javac.util.List.<JmlMethodClause>of(en,enn,clp,clpa,sig,cval);
                // FIXME - need to add a helper, pure annotation
                var mdef = (JmlMethodDecl)M.at(pos).MethodDef(sym,null);
                addModifier(pos, Modifiers.SPEC_PURE, mdef.mods);
                addModifier(pos, Modifiers.HELPER, mdef.mods);
                addModifier(pos, Modifiers.NON_NULL, mdef.mods);
                mspecs.specDecl = mdef;
                
            } else if (sym.name.equals(names.valueOf)) {
               // FIXME - add a disjunction of all possibilities?
                // FIXME - might throw an exception?
                // Default specifications:
                //   ensures arg != null && \result != null;
                //   assignable \nothing;
                //   accessible \nothing;
                //   signals (NullPointerException) arg == null;
                //   signals_only NullPointerException, IllegalArgumentException;
                VarSymbol arg = sym.params().get(0); 
                JmlMethodClauseSignalsOnly sigo = null;
                if (arg.type.isReference()) {
                    Type npeType = ClassReader.instance(context).enterClass(names.fromString("java.lang.NullPointerException")).type;
                    JCVariableDecl vd = treeutils.makeVarDef(npeType, null, sym, pos);
                	JCExpression argnn = treeutils.makeNotNull(pos,treeutils.makeIdent(pos, arg));
                	JCExpression argnull = treeutils.makeEqNull(pos,treeutils.makeIdent(pos, arg));
                	sig.expression = argnull;
                    sig = M.at(pos).JmlMethodClauseSignals(signalsID, signalsClauseKind, vd, argnull);
                    sigo = M.at(pos).JmlMethodClauseSignalsOnly(signalsOnlyID, signalsOnlyClauseKind, com.sun.tools.javac.util.List.<JCExpression>of(M.Type(npeType),M.Type(syms.illegalArgumentExceptionType)));
                    en = M.at(pos).JmlMethodClauseExpr("ensures", ensuresClauseKind, treeutils.makeAnd(pos, argnn, resnn));
                    clauses = com.sun.tools.javac.util.List.<JmlMethodClause>of(en,clp,clpa,sig,sigo);
                    // FIXME - Illegal argument exception? What about user supplied valueOf methods?
                    var mdef = (JmlMethodDecl)M.at(pos).MethodDef(sym,null);
                    addModifier(pos, Modifiers.SPEC_PURE, mdef.mods);
                    addModifier(pos, Modifiers.HELPER, mdef.mods);
                    addModifier(pos, Modifiers.NON_NULL, mdef.mods); // FIXME - PUSH AS TYPE ANNOTATION
                    JCVariableDecl param = mdef.params.head;
                    addModifier(pos,Modifiers.NULLABLE,param.mods); // FIXME - PUSH AS TYPE ANNOTATION
                    mspecs.specDecl = mdef;
                    
                } else {
                    clauses = com.sun.tools.javac.util.List.<JmlMethodClause>of(en,clp,clpa);
                }
            } else if (sym.name.equals(names.ordinal)) {
                // int result - do not use non null clause (en)
                JCBinary lo = treeutils.makeBinary(pos, JCTree.Tag.LE, treeutils.zero, res);
                JCBinary hi = treeutils.makeBinary(pos, JCTree.Tag.LE, res, treeutils. makeIntLiteral(pos,count) );
                JCBinary pred = treeutils.makeBinary(pos, JCTree.Tag.AND, lo, hi);
                JmlMethodClause enn = M.at(pos).JmlMethodClauseExpr(ensuresID, ensuresClauseKind,pred);
                clauses = com.sun.tools.javac.util.List.<JmlMethodClause>of(clp,sig,clpa,enn);
            } else if (sym.name.equals(names._name)) {
                // FIXME - add a disjunction of all possibilities?
                clauses = com.sun.tools.javac.util.List.<JmlMethodClause>of(en,clp,sig,clpa);
            } else if (sym.name.equals(names.toString)) {
                // FIXME - need to equate toString() and name()
                clauses = com.sun.tools.javac.util.List.<JmlMethodClause>of(en,clp,sig,clpa);
            } else {
                break xx;
            }
            JmlSpecificationCase cs = M.at(pos).JmlSpecificationCase( csm, false, MethodSimpleClauseExtensions.behaviorClause,null,clauses,null);
            mspecs.cases.cases = com.sun.tools.javac.util.List.<JmlSpecificationCase>of(cs);
            //System.out.println("ADDING SPEC_PURE " + sym.owner + " " + sym + " " + (decl!=null));
            addModifier(pos, Modifiers.SPEC_PURE, mspecs.mods);
//            if (sym.name.equals(names.valueOf)) {
//            	System.out.println("VALUEOF MSPECS " + mspecs);
//                System.out.println("VALUEOF DECL " + mspecs.specDecl);
//            }
            JmlSpecs.instance(context).putSpecs(sym, mspecs); // FIXME - are the specs attributed or not?
            return mspecs;
            
        }
        

        // Non-special case. Default specs are
        //   <same access as method> behavior
        //        assignable \everything;
        //        accessible \everything;
        //        signals_only RuntimeException, <list of declared exceptions>;
        
        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
        // sym can be null if the method call is in a field initializer (and not in the body of a method)
        // Not sure when sym.type is null - but possibly when an initializer block is created to hold translated
        // material from a field initializer
        if (sym != null && sym.type != null) for (Type t: sym.getThrownTypes()) {
            JCExpression e = JmlTreeUtils.instance(context).makeType(pos, t);
            list.add(e);
        }
        
        boolean print = sym.owner.toString().contains("java.util.Collection") && sym.toString().contains("size");
        
        boolean libraryMethod = sym.owner instanceof ClassSymbol && sym.owner.toString().startsWith("java");
        boolean isPureA = determinePurity(sym) != null ;
               // : utils.hasModifier(mspecs.mods, Modifiers.PURE, Modifiers.SPEC_PURE, MOdifiers.STRICTLY_PURE, Modifiers.NO_STATE); // use isPure?
        boolean isPureL = (libraryMethod && !JmlOption.isOption(context,JmlOption.PURITYCHECK));
        //if (print) System.out.println("DEFAULT " + sym.owner + " " + sym + " "+ libraryMethod + " " + JmlOption.isOption(context,JmlOption.PURITYCHECK) + " " + isPureA + " " + isPureL);
        JmlMethodClause clp = M.at(pos).JmlMethodClauseStoreRef(assignableID, assignableClauseKind,
                com.sun.tools.javac.util.List.<JCExpression>of(new JmlTree.JmlStoreRefKeyword(pos,isPureA||isPureL?nothingKind:everythingKind)));
        JmlMethodClause clpa = new JmlTree.JmlMethodClauseStoreRef(pos,accessibleID, accessibleClauseKind,
                com.sun.tools.javac.util.List.<JCExpression>of(new JmlTree.JmlStoreRefKeyword(pos,everythingKind)));

        list.add(JmlTreeUtils.instance(context).makeType(pos, Symtab.instance(context).runtimeExceptionType));
        JmlMethodClauseSignalsOnly cl = M.at(pos).JmlMethodClauseSignalsOnly(signalsOnlyID, signalsOnlyClauseKind, list.toList());
        cl.defaultClause = true;
        com.sun.tools.javac.util.List<JmlMethodClause> clauses;
        if (decl == null) clauses = com.sun.tools.javac.util.List.<JmlMethodClause>of(clp,clpa,cl);
        else clauses = com.sun.tools.javac.util.List.<JmlMethodClause>of(cl);
        JCModifiers csm = M.at(pos).Modifiers(mods.flags & Flags.AccessFlags);
        JmlSpecificationCase cs = M.at(pos).JmlSpecificationCase(csm, false, MethodSimpleClauseExtensions.behaviorClause,null,clauses,null);
        mspecs.cases.cases = com.sun.tools.javac.util.List.<JmlSpecificationCase>of(cs);
        if (decl == null) mspecs.cases.deSugared = mspecs.cases;
        //FIXME: this sets as pure far more methods than needed, including some that are definitely not pure
        //if (print) System.out.println("LIB-PURE " + sym.owner + " " + sym + " " + isPureA + " " + isPureL + " " + (decl!= null));
        //if (isPureL && !isPureA && (decl==null)) addModifier(pos, Modifiers.SPEC_PURE, mspecs.mods);
        //if (print) System.out.println("DEFAULT SPECS " + mspecs);
        return mspecs;
    }
    
    public void addModifier(int pos, ModifierKind m, JCModifiers mods) {
        var tok = new com.sun.tools.javac.parser.JmlToken(m, log.currentSourceFile(), pos, pos, null);
        ((JmlModifiers)mods).jmlmods.add(tok);
    }
    
    public void addModifier(int pos, int endpos, ModifierKind m, JCModifiers mods) {
        var tok = new com.sun.tools.javac.parser.JmlToken(m, log.currentSourceFile(), pos, endpos, null);
        ((JmlModifiers)mods).jmlmods.add(tok);
    }
    
//    protected/* @ nullable */JCAnnotation tokenToAnnotationAST(JmlTokenKind jt,
//            int position, int endpos) {
//        JmlTree.Maker M = JmlTree.Maker.instance(context);
//        Symtab syms = Symtab.instance(context);
//        JmlTreeUtils treeutils = JmlTreeUtils.instance(context);
//        Class<?> c = jt.annotationType;
//        if (c == null) return null;
//        JCExpression t = (M.at(position).Ident(names.fromString("org")));
//        t = (M.at(position).Select(t, names.fromString("jmlspecs")));
//        t = (M.at(position).Select(t, names.fromString("annotation")));
//        t = (M.at(position).Select(t, names.fromString(c.getSimpleName())));
//        JCAnnotation ann = (M.at(position).Annotation(t,
//                com.sun.tools.javac.util.List.<JCExpression> nil()));
//        ((JmlTree.JmlAnnotation)ann).sourcefile = log.currentSourceFile();
//        //storeEnd(ann, endpos);
//        return ann;
//    }

//    public com.sun.tools.javac.util.List<JCAnnotation> addPureAnnotation(int pos, com.sun.tools.javac.util.List<JCAnnotation> annots) {
//        JmlTree.Maker F = JmlTree.Maker.instance(context);
//        JmlAnnotation pure = makePureAnnotation(pos, true, F);
//        return annots.append(pure);
//    }
//    
//    public com.sun.tools.javac.util.List<JCAnnotation> addAnnotation(int pos, ModifierKind mk, com.sun.tools.javac.util.List<JCAnnotation> annots) {
//        JmlTree.Maker F = JmlTree.Maker.instance(context);
//        JmlAnnotation a = makeAnnotation(pos, F, mk);
//        return annots.append(a);
//    }
//    
//    public JmlAnnotation makePureAnnotation(int pos, boolean withType, JmlTree.Maker F) {
//        JmlAnnotation annot = makeAnnotation(pos, F, Modifiers.PURE);
//        if (withType) annot.type = annot.annotationType.type = pureAnnotationSymbol().type;
//        return annot;
//    }

//    public com.sun.tools.javac.util.List<JCAnnotation> addModelAnnotation(int pos, com.sun.tools.javac.util.List<JCAnnotation> annots) {
//        JmlTree.Maker F = JmlTree.Maker.instance(context);
//        JmlAnnotation annot = makeAnnotation(pos, F, Modifiers.MODEL);
//        annot.type = annot.annotationType.type = modelAnnotationSymbol().type;
//        return annots.append(annot);
//    }
//
//    public JmlAnnotation makeAnnotation(int pos, JmlTree.Maker F, ModifierKind jt) {
//        String s = jt.fullAnnotation;
//        int k = s.lastIndexOf(".");
//        JCExpression t = (F.Ident(names.fromString("org")));
//        t = (F.Select(t, names.fromString("jmlspecs")));
//        t = (F.Select(t, names.fromString("annotation")));
//        t = (F.Select(t, names.fromString(s.substring(k+1))));
//        JmlAnnotation ann = (F.Annotation(t, com.sun.tools.javac.util.List.<JCExpression> nil()));
//        ann.kind = jt;
////        annot.type = annot.annotationType.type = modelAnnotationSymbol().type; // FIXME - needs type
//        //((JmlTree.JmlAnnotation)ann).sourcefile = log.currentSourceFile();
//        //storeEnd(ann, endpos);
//        return ann;
//    }

    /** Retrieves the specs for a given field
     * @param m the VarSymbol of the field whose specs are wanted
     * @return the specs of the field, or null if none are present
     */
    //@ nullable
    public FieldSpecs getAttrSpecs(VarSymbol v) {
    	if (!(v.owner instanceof ClassSymbol c)) return null;
    	getLoadedSpecs(c);
//    	if (c == null) System.out.println("Unexpected difference - field " + m + " " + m.owner + " " + m.enclClass());
//    	if (c == null) Utils.dumpStack();
    	if (status(v).less(SpecsStatus.SPECS_ATTR)) attr.attrSpecs(v);
//        TypeSpecs t = specsmap.get(c);
//        return t == null ? null : t.fields.get(m);
    	return get(v);
    }
    
    /** Returns precisely what is in the current specs data base -- may be null */
    //@ nullable
    public FieldSpecs get(VarSymbol v) {
//        TypeSpecs t = specsmap.get(m.owner);
//        return t == null ? null : t.fields.get(m);
    	return specsFields.get(v);
    }
    
    public VarSpecs getFormal(VarSymbol v) {
        //System.out.println("   GetFormal " + v + " " + v.owner + " " + v.hashCode());
        return specsFormals.get(v);
    }
    
   /** Retrieves the specs for a given field
     * @param m the VarSymbol of the field whose specs are wanted
     * @return the specs of the field, or null if none are present
     */
    //@ nullable
    public FieldSpecs getLoadedSpecs(VarSymbol m) {
    	if (m.owner instanceof ClassSymbol && status(m).less(SpecsStatus.SPECS_LOADED)) {
    		getLoadedSpecs((ClassSymbol)m.owner);
    	}
    	return specsFields.get(m);
    }
    
    public JmlModifiers getSpecsModifiers(VarSymbol vsym) {
    	try {
    		var sp = getLoadedSpecs(vsym);
    		return sp == null ? null : sp.mods;
    	} catch (Exception e) {
    		utils.note(false,"Exception when calling getSpecsModifiers for " + vsym + " " + vsym.owner);
    		throw e;
    	}
    }
    
    /** Retrieves the specs for a given initializer block
     * @param sym the class in which the block resides
     * @param m the JCBlock of the block whose specs are wantedTATUS
     * @return the specs of the block, or null if none are present
     */
    //@ nullable
    public MethodSpecs getAttrSpecs(ClassSymbol sym, JCTree.JCBlock m) {
        TypeSpecs t = getAttrSpecs(sym);
        return t.blocks.get(m);
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

        //@ nullable
        public Env<AttrContext> specsEnv; // The env to use to typecheck the specs; can be null if there is no spec file
        
        
        // The source file for the specifications -- not necessarily the same as csymbol.sourcefile
        //@ nullable
        public JavaFileObject file; // can be null if there is no spec file for a binary class

        /** The JmlClassDecl for the specification
         */
        //@ nullable   // may be null if the class is binary and there is no specification file
        public JmlClassDecl specDecl;

        /** The JmlClassDecl for the source
         */
        //@ nullable   // may be null if the class is binary; may be the same as specDecl if there is source and no .jml
        public JmlClassDecl javaDecl;

        /** The modifiers of the class, including JML modifiers */
        public JmlModifiers modifiers;

        /** Caches the nullity for the associated class: if null, not yet determined;
         * otherwise, the result of considering explicit declarations, declarations
         * on containing classes, and the system default.
         */
        //@ nullable
        private ModifierKind defaultNullity = null;
        
        /** All the specification clauses for the class (not method clauses or field clauses or block clauses) */
        /*@ non_null */
        public ListBuffer<JmlTree.JmlTypeClause> clauses;

        // FIXME - is this still used?
        /** Synthetic methods for model fields (these are also included in the clauses list) */
        /*@ non_null */
        public ListBuffer<JmlTree.JmlTypeClauseDecl> modelFieldMethods = new ListBuffer<JmlTree.JmlTypeClauseDecl>();

        /** A map from initializer blocks of the class to the specifications for the initializers. */ // FIXME - review
        /*@ non_null */
        public Map<JCTree.JCBlock,MethodSpecs> blocks = new HashMap<JCTree.JCBlock,MethodSpecs>();

        /** The spec associated with the initializer keyword, if any */
        /*@ nullable */ // will be null if there is no initializer specification
        public JmlTypeClauseInitializer initializerSpec = null;
        
        /** The spec associated with the static_initializer keyword, if any */
        /*@ nullable */ // will be null if there is no static_initializer specification
        public JmlTypeClauseInitializer staticInitializerSpec = null;
        
       
        // Only for the case in which there is no specification file -- that is, default or inferred specs
        public TypeSpecs(ClassSymbol csymbol, /*@ nullable */ JavaFileObject file, JmlModifiers mods, /*@ nullable */ Env<AttrContext> env) {
            this.file = file; // can be null for binary classes with no spec file
            this.csymbol = csymbol;
            this.specDecl = null;
            this.javaDecl = null;
            this.modifiers = mods;
            this.clauses = new ListBuffer<JmlTypeClause>();
            this.specsEnv = env; // can be null for binary classes with no spec file
        }
        
        public TypeSpecs(JmlClassDecl specdecl, JmlClassDecl javadecl, Env<AttrContext> specenv) {
        	if (specdecl == null) throw new AssertionError("Unexpected null specdecl");
        	if (javadecl != null && javadecl.specsDecl != specdecl) throw new AssertionError("Mismatched decls");
        	if (javadecl != null && javadecl.sym != specdecl.sym) throw new AssertionError("Mismatched class symbols");
        	this.specDecl = specdecl;
        	this.javaDecl = javadecl;
        	this.csymbol = specdecl.sym;
        	this.file = specdecl.source(); // FIXME - do we need this caching?
        	this.modifiers = (JmlModifiers)specdecl.mods; // FIXME - need to set mods from java or csymbol
        	this.clauses = new ListBuffer<JmlTree.JmlTypeClause>();
        	for (JCTree t: specdecl.defs) {
        		if (t instanceof JmlTypeClauseInitializer init) {
        			if (init.keyword.equals(TypeInitializerClauseExtension.staticinitializerID)) {
        				staticInitializerSpec = init;
        			} else {
        				initializerSpec = init;
        			}
        		} else if (t instanceof JmlTypeClauseConditional) {
        			// No such clause should be present // FIXME: error message
        			System.out.println("UNEXPECTED RW CLAUSE " + t);
        		} else if (t instanceof JmlTypeClause) {
        			this.clauses.add((JmlTypeClause)t);
        		}
        	}
        	specdecl.typeSpecs = this; // FIXME - should we really reset this?or even cache it?
            this.specsEnv = specenv;
            // FIXME ??? - blocks
        }
        
        public void setEnv(Env<AttrContext> env) {
        	specsEnv = env;
        }
        
        // FIXME - what about modifiers, initializer clauses, blocks
        public String toString() {
            StringWriter s = new StringWriter();
            JmlPretty p = new JmlPretty(s, false);
            for (JmlTypeClause c: clauses) {
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
     * @return Modifiers.NULLABLE or Modifiers.NON_NULL
     */
    //@ ensures \result != null;
    public /*@non_null*/ ModifierKind defaultNullity(/*@ nullable*/ ClassSymbol csymbol) {
    	ModifierKind t = null;
        if (csymbol == null) {
            // Note: NULLABLEBYDEFAULT turns off NONNULLBYDEFAULT and vice versa.
            // If neither one is present, then the logic here will give the
            // default as NONNULL.
            if (JmlOption.isOption(context,JmlOption.NULLABLEBYDEFAULT)) {
                return Modifiers.NULLABLE;
            } else if (JmlOption.isOption(context,JmlOption.NONNULLBYDEFAULT)) {
                return Modifiers.NON_NULL;
            } else {
                return Modifiers.NON_NULL;  // The default when nothing is specified
            }
        }
        
        TypeSpecs spec = getLoadedSpecs(csymbol);
        t = spec.defaultNullity;
        if (t == null) {
        	if (utils.hasMod(spec.modifiers, Modifiers.NULLABLE_BY_DEFAULT)) { 
        		t = Modifiers.NULLABLE; 
        	} else if (utils.hasMod(spec.modifiers, Modifiers.NON_NULL_BY_DEFAULT)) {
        		t =  Modifiers.NON_NULL;
        	} else {
                Symbol sym = csymbol.owner; // The owner might be a package - currently no annotations for packages
                if (sym instanceof ClassSymbol) {
                    t = defaultNullity((ClassSymbol)sym);
                } else {
                    t = defaultNullity(null);
                }
            }
            spec.defaultNullity = t;
        }
        return t;
    }

//    // Not complete
//    public /*@non_null*/ JCAnnotation defaultNullityAnnotation(/*@ nullable*/ ClassSymbol csymbol) {
//        if (csymbol == null) {
//            // FIXME - this is no longer true
//            // Note: NULLABLEBYDEFAULT turns off NONNULLBYDEFAULT and vice versa.
//            // If neither one is present, then the logic here will give the
//            // default as NONNULL.
////            JmlAnnotation a;
////            if (JmlOption.isOption(context,JmlOption.NULLABLEBYDEFAULT)) {
////                a = new JmlAnnotation(nullablebydefaultAnnotationSymbol.type, com.sun.tools.javac.util.List.<JCExpression>nil());
////            } else if (JmlOption.isOption(context,JmlOption.NONNULLBYDEFAULT)) {
////                return JmlToken.NONNULL;
////            } else {
////                return JmlToken.NONNULL;  // The default when nothing is specified
////            }
//            return null;
//        }
//        
//        TypeSpecs tspecs = JmlSpecs.instance(context).getLoadedSpecs(csymbol);
//        if (tspecs != null) {
//        	JCModifiers mods = tspecs.decl.mods;
//        	JCAnnotation a = utils.findMod(mods,attr.nullablebydefaultAnnotationSymbol);
//        	if (a != null) return a;
//            a = utils.findMod(mods,attr.nonnullbydefaultAnnotationSymbol);
//            if (a != null) return a;
//        }
//        Symbol owner = csymbol.owner;
//        if (owner instanceof Symbol.PackageSymbol) owner = null;
//        return defaultNullityAnnotation((Symbol.ClassSymbol)owner);
//    }

//    /** Caches the symbol for the org.jmlspecs.annotation.NonNull */
//    ClassSymbol nonnullAnnotationSymbol = null;
//    /** Caches the symbol for the org.jmlspecs.annotation.Nullable */
//    ClassSymbol nullableAnnotationSymbol = null;
//    ClassSymbol nullablebydefaultAnnotationSymbol = null;
//    ClassSymbol nonnullbydefaultAnnotationSymbol = null;
    
    /** Returns whether the given symbol is non-null (either explicitly or by
     * default); the second parameter is the enclosing class.
     * @param symbol the symbol whose nullity is being checked - either a VarDef (a 
     * parameter declaration) or a MethodDef (for the return type)
     * @param csymbol the enclosing class, from which any default comes
     * @return true if the symbol is non-null explicitly or by default
     */
    public boolean isNonNull(Symbol symbol) {
        if (symbol instanceof VarSymbol) return isNonNull((VarSymbol)symbol);
        if (symbol instanceof MethodSymbol) return isNonNull((MethodSymbol)symbol);
        if (symbol instanceof ClassSymbol) return defaultNullity((ClassSymbol)symbol) == Modifiers.NON_NULL;
        utils.error("jmllinternal", "Unexpected execution path in isNonNull");
        return false;
    }

    public boolean isNonNullNoDefault(VarSymbol sym) {
    	if (!sym.type.isReference()) return false;
    	var fspecs = getLoadedSpecs(sym);
    	if (fspecs != null) {
    		if (utils.hasMod(fspecs.mods, Modifiers.NON_NULL)) return true;
    	}
		if (attr.hasAnnotation2(sym, Modifiers.NON_NULL)) return true;
    	if (findAnnotation(sym.type, Modifiers.NON_NULL)) return true;
    	return false;
    }

    public boolean isNullableNoDefault(VarSymbol sym) {
    	if (!sym.type.isReference()) return false;
    	var fspecs = getLoadedSpecs(sym);
    	if (fspecs != null) {
        	if (utils.hasMod(fspecs.mods, Modifiers.NULLABLE)) return true;
    	}
    	if (attr.hasAnnotation2(sym, Modifiers.NULLABLE)) return true;
    	if (findAnnotation(sym.type, Modifiers.NULLABLE)) return true;
    	return false;
    }

    public boolean isNonNull(VarSymbol sym) {
        return isNonNull(sym, null);
    }
    
    public boolean isNonNull(VarSymbol sym, JmlVariableDecl decl) {
        if (utils.isJavaOrJmlPrimitiveType(sym.type)) return false;
        // formal, field or local variable
        var fsp = getFormal(sym);
        if (fsp != null) return fsp.isNonNull;
        
        var fspecs = getLoadedSpecs(sym);
        if (fspecs != null) return fspecs.isNonNull;
        //      if (fspecs != null) {
        //            if (utils.hasModOrAnn(fspecs.mods, Modifiers.NULLABLE)) return false;
        //            if (utils.hasModOrAnn(fspecs.mods, Modifiers.NON_NULL)) return true;
        //      }
        //      if (attr.hasAnnotation2(sym, Modifiers.NULLABLE)) return false;
        //      if (attr.hasAnnotation2(sym, Modifiers.NON_NULL)) return true;
        // Local?
        
        if (decl != null) {
            return computeVarNullness(decl, sym.owner);
        }
        
        return isNonNull(sym.type, sym.enclClass());
    }
    
    public boolean isNonNullFormal(VarSymbol sym) {
        var x = getFormal(sym);
        if (x != null) return x.isNonNull;
        return isNonNull(sym.owner.owner);
    }

    
    public boolean findAnnotation(Type type, ModifierKind kind) {
    	for (var a: type.getAnnotationMirrors()) {
    		if (a.type.toString().endsWith(kind.fullAnnotation)) return true; // FIXME - there has to be a better way
    	}
    	return false;
    }
    
    public boolean findAnnotation(JCExpression type, ModifierKind kind) {
    	if (!(type instanceof JCTree.JCAnnotatedType)) return false;
    	for (var a: ((JCTree.JCAnnotatedType)type).annotations) {
    		if (a.toString().endsWith(kind.fullAnnotation)) return true; // FIXME - there has to be a better way
    	}
    	return false;
    }

    public JCAnnotation findAnnotation(List<JCAnnotation> annotations, ModifierKind kind) {
        for (var a: annotations) {
            //var s = a.annotationType.toString();
            //if (s.charAt(0) == '@') s = s.substring(1);
            //if (s.endsWith(kind.fullAnnotation)) return a;
            if (a instanceof JmlAnnotation ja) {
                if (ja.kind == kind) return a;
                // FIXME - check why (local) annotations may not have 'kind' set
                if (ja.kind == null && a.annotationType.toString().endsWith(kind.fullAnnotation)) return a;
            }
        }
        return null;
    }

    public boolean isCheckNonNullFormal(Type type, int i,  MethodSpecs calleeSpecs, MethodSymbol msym) {
    	// Extension type values are always non-null, but we do not check for that
    	if (utils.isExtensionValueType(type)) return false;
    	if ((msym.owner.flags() & Flags.ENUM) !=  0 && msym.name.equals(names.valueOf)) return false;
    	return isNonNullFormal(type, i, calleeSpecs, msym);
    }

    @SuppressWarnings("unchecked")
    public boolean isNonNullFormal(Type type, int i, MethodSpecs calleeSpecs, MethodSymbol msym) {
        //boolean pr = i == 0 && msym.name.toString().equals("m");
        //if (pr) System.out.println("NNF " + type + " " + i + " " + msym + " " + msym.enclClass() + " " + defaultNullity(msym.enclClass()) + " " + calleeSpecs);
        if (!type.isReference()) return false;
        if (Types.instance(context).isSubtype(type, 
                Symtab.instance(context).jmlPrimitiveType)) return true;
        //if (pr) System.out.println("NNF-A " + findAnnotation(type, Modifiers.NULLABLE) + " " + findAnnotation(type, Modifiers.NON_NULL));
        if (findAnnotation(type, Modifiers.NULLABLE)) return false;
        if (findAnnotation(type, Modifiers.NON_NULL)) return true;
        //if (type instanceof Type.TypeVar) return false; 
        //if (pr) System.out.println("SPECS " + calleeSpecs + " # " + calleeSpecs.specDecl);
        if (!(type instanceof Type.TypeVar) && calleeSpecs.specDecl != null) {
            var decl = (JmlVariableDecl)calleeSpecs.specDecl.params.get(i);
            JmlModifiers mods = (JmlModifiers)decl.mods;
            //if (pr) System.out.println("ARG " + i + " " + decl + " # " + decl.type + " " + mods + "::" + decl.vartype);
            if (hasTypeAnnotation(decl.vartype, Modifiers.NULLABLE)) return false;
            if (hasTypeAnnotation(decl.vartype, Modifiers.NON_NULL)) return true;
            //if (pr) System.out.println("NNF-B " + mods + " " + utils.hasModOrAnn(mods, Modifiers.NULLABLE) + " " + utils.hasModOrAnn(mods, Modifiers.NON_NULL));
            if (utils.hasModOrAnn(mods, Modifiers.NULLABLE)) return false;
            if (utils.hasModOrAnn(mods, Modifiers.NON_NULL)) return true;
        }
        //if (pr) System.out.println("NNF-C " + msym.enclClass()+ " " + defaultNullity(msym.enclClass()));
        return defaultNullity(msym.enclClass()) == Modifiers.NON_NULL;
    }
    
    public boolean hasTypeAnnotation(JCExpression vartype, ModifierKind kind) {
        if (vartype instanceof JCAnnotatedType at) {
            for (JCAnnotation a: at.annotations) if (a instanceof JmlAnnotation ja && ja.kind == kind) return true;
            return false;
        } else if (vartype instanceof JCFieldAccess fa) {
            return false;
        } else if (vartype instanceof JCArrayTypeTree att) {
            return hasTypeAnnotation(att.elemtype, kind);
        } else if (vartype instanceof JCTypeApply app) {
            return hasTypeAnnotation(app.clazz, kind);
        } else {
            return false;
        }
    }
    
	public boolean isCheckNonNullReturn(Type type, MethodSymbol msym) {
    	// Extension type values are always non-null, but we do not check for that
    	if (utils.isExtensionValueType(type)) return false;
    	{
    	    var s = type.toString();
    	    // FIXME - there must be a better way
            if (s.contains("org.jmlspecs.annotation.NonNull")) return true;
            if (s.contains("org.jmlspecs.annotation.Nullable")) return false;
    	}
        if (isNonNull(type)) return true; // FIXME - does this duplicate the above
    	if (isNonNullReturn(msym)) return true;
    	return false;
    }
		
    
    @SuppressWarnings("unchecked")
	public boolean isNonNullReturn(MethodSymbol msym) {
        var ms = get(msym);
        return ms.returnNonNull;
    }
    
    @SuppressWarnings("unchecked")
	public boolean isNonNull(Type type) {
    	if (!type.isReference()) return false;
    	if (Types.instance(context).isSubtype(type, 
    			Symtab.instance(context).jmlPrimitiveType)) return true;
    	if (findAnnotation(type, Modifiers.NULLABLE)) return false;
    	if (findAnnotation(type, Modifiers.NON_NULL)) return true;
    	return false;
    }
    
    @SuppressWarnings("unchecked")
	public boolean isNonNull(Type type, ClassSymbol classOwner) {
    	if (!type.isReference()) return false;
    	if (Types.instance(context).isSubtype(type, 
    			Symtab.instance(context).jmlPrimitiveType)) return true;
    	if (findAnnotation(type, Modifiers.NULLABLE)) return false;
    	if (findAnnotation(type, Modifiers.NON_NULL)) return true;
    	if (type instanceof Type.TypeVar) return false; 
    	return defaultNullity(classOwner) == Modifiers.NON_NULL;
    }
    
    @SuppressWarnings("unchecked")
	public boolean isNonNull(Type type, MethodSymbol msym) {
    	if (!type.isReference()) return false;
    	if (Types.instance(context).isSubtype(type, 
    			Symtab.instance(context).jmlPrimitiveType)) return true;
        if (findAnnotation(type, Modifiers.NULLABLE)) return false;
        if (findAnnotation(type, Modifiers.NON_NULL)) return true;
    	if (type instanceof Type.TypeVar) return false; 
    	return isNonNull(msym);
    }
    
    public boolean isNonNull(MethodSymbol sym) {
    	// For some reason, type annotations are not part of the method return type,
    	// but are in the MethodSymbol's annotations
    	if (!sym.getReturnType().isReference()) return false;
    	if (attr.hasAnnotation2(sym, Modifiers.NULLABLE)) return false;
		if (attr.hasAnnotation2(sym, Modifiers.NON_NULL)) return true;
		var sp = specsMethods.get(sym);
		if (sp.cases.decl != null) {
			if (attr.hasAnnotation(sp.cases.decl.mods.annotations, Modifiers.NON_NULL)) return true;
			if (attr.hasAnnotation(sp.cases.decl.mods.annotations, Modifiers.NULLABLE)) return false;
		}
    	return isNonNull(sym.enclClass());
    }
    
    public boolean isNonNull(JmlVariableDecl decl) {
    	if (!decl.type.isReference()) return false;
    	if (decl.sym.owner instanceof ClassSymbol) {
    		return isNonNull(decl.sym);
    	} else {
    		// Local variable or parameter -- owned by method
    		JmlModifiers mods = (JmlModifiers)decl.mods;
        	if (utils.hasMod(mods, Modifiers.NULLABLE)) return false;
        	if (utils.hasMod(mods, Modifiers.NON_NULL)) return true;
        	return defaultNullity(decl.sym.enclClass()) == Modifiers.NON_NULL;
    	}
    }
    
    public boolean isNonNull(JmlClassDecl decl) {
    	return defaultNullity(decl.sym) == Modifiers.NON_NULL; 
    }
    
//    public void makeAnnotationSymbols() {
//        if (nonnullAnnotationSymbol == null) {
//            nonnullAnnotationSymbol = ClassReader.instance(context).enterClass(Names.instance(context).fromString(Strings.nonnullAnnotation));
//        }
//        if (nullableAnnotationSymbol == null) {
//            nullableAnnotationSymbol = ClassReader.instance(context).enterClass(Names.instance(context).fromString(Strings.nullableAnnotation));
//        }
//        if (nullablebydefaultAnnotationSymbol == null) {
//            nullablebydefaultAnnotationSymbol = ClassReader.instance(context).enterClass(Names.instance(context).fromString(Strings.nullablebydefaultAnnotation));
//        }
//        if (nonnullbydefaultAnnotationSymbol == null) {
//            nonnullbydefaultAnnotationSymbol = ClassReader.instance(context).enterClass(Names.instance(context).fromString(Strings.nonnullbydefaultAnnotation));
//        }
//    }
//    
//    public boolean isNonNull(Symbol symbol, ClassSymbol csymbol) {
//        if (!(symbol instanceof MethodSymbol) && utils.isPrimitiveType(symbol.type)) return false;
//        if (JmlTypes.instance(context).isOnlyDataGroup(symbol.type)) return false;
//        
//        // TODO - perhaps cache these when the JmlSpecs class is created? (watch for circular tool creation)
//        makeAnnotationSymbols();
//        Attribute.Compound attr;
//        if (symbol instanceof Symbol.VarSymbol && symbol.owner instanceof Symbol.ClassSymbol) {
//            // Field
//            FieldSpecs fspecs = getLoadedSpecs((Symbol.VarSymbol)symbol);
//            if (fspecs == null) return false; // FIXME - we need private fields of binary classes that have no specs declared to be nullable
//            if (fspecs != null && utils.findMod(fspecs.mods,nullableAnnotationSymbol) != null) return false;
//            else if (fspecs != null && utils.findMod(fspecs.mods,nonnullAnnotationSymbol) != null) return true;
//            else if (symbol.name == names._this) return true;
//            else return defaultNullity((Symbol.ClassSymbol)symbol.owner) == Modifiers.NON_NULL;
//        } else if (symbol instanceof Symbol.VarSymbol && (symbol.owner == null || symbol.owner instanceof Symbol.MethodSymbol)) {
//            attr = symbol.attribute(nullableAnnotationSymbol);
//            if (attr != null) return false;
//            attr = symbol.attribute(nonnullAnnotationSymbol);
//            if (attr != null) return true;
//
//            // Method parameter or variable in body
////            MethodSpecs mspecs = getSpecs((Symbol.MethodSymbol)symbol.owner);
//            // FIXME - not clear we are able to look up a particular parameter - which case do we use? don't want inherited specs?
////            specs.cases.decl
////            if (mspecs != null && utils.findMod(mspecs.mods,nullableAnnotationSymbol) != null) return false;
////            else if (mspecs != null && utils.findMod(mspecs.mods,nonnullAnnotationSymbol) != null) return true;
//            // else return defaultNullity(csymbol) == JmlToken.NONNULL;
//            
//            // Need to distinguish the two cases. The following is correct for variables in the body
//            return defaultNullity(csymbol) == Modifiers.NON_NULL;
//            
//        } else if (symbol instanceof Symbol.MethodSymbol) {
//            // Method return value
//            MethodSpecs mspecs = getLoadedSpecs((Symbol.MethodSymbol)symbol);
//            if (mspecs != null && utils.findMod(mspecs.mods,nullableAnnotationSymbol) != null) return false;
//            else if (mspecs != null && utils.findMod(mspecs.mods,nonnullAnnotationSymbol) != null) return true;
//            else return defaultNullity(csymbol) == Modifiers.NON_NULL;
//        } else {
//            // What else?
//            attr = symbol.attribute(nullableAnnotationSymbol);  // FIXME - the symbol might be 'THIS' which should always be non_null
//            if (attr != null) return false;
//            attr = symbol.attribute(nonnullAnnotationSymbol);
//            if (attr != null) return true;
//            return defaultNullity(csymbol) == Modifiers.NON_NULL;
//        }
//    }
    
    /** Caches the symbol for a Pure annotation, which is computed on demand. */
    private ClassSymbol pureAnnotationSymbol = null;
    private ClassSymbol queryAnnotationSymbol = null;
    private ClassSymbol functionAnnotationSymbol = null;
    private ClassSymbol modelAnnotationSymbol = null;

    // FIXME - these are also computed in JmlAttr
    protected ClassSymbol pureAnnotationSymbol() {
    	return annotationSymbol(Modifiers.PURE);
    }

    protected ClassSymbol modelAnnotationSymbol() {
    	return annotationSymbol(Modifiers.MODEL);
    }

    protected ClassSymbol annotationSymbol(ModifierKind mk) {
    	if (mk.annotationSym == null) {
    		mk.annotationSym = utils.createClassSymbol(Symtab.instance(context).java_base, mk.fullAnnotation);
    	}
    	return mk.annotationSym;
    }
    
    public boolean isPureMethod(MethodSymbol symbol) {
        boolean print = false;//symbol.toString().contains("ok(");
        if (print) System.out.println("IPM " + symbol.owner + " " + symbol  );
        java.util.List<MethodSymbol> overrideList = Utils.instance(context).parents(symbol,true);
        java.util.ListIterator<MethodSymbol> iter = overrideList.listIterator(overrideList.size());
        while (iter.hasPrevious()) {
            MethodSymbol msym = iter.previous();
            if (print) System.out.println("  CHECKING " + symbol + " " + msym.owner + "." + msym);
            MethodSpecs mspecs = getLoadedSpecs(msym); // Could be null if we are in the middle of generating defaultSpecs
            if (print) System.out.println("  IPMA " + symbol.owner + "." + symbol + " " + msym.owner + "." + msym + " " + mspecs);
            if (mspecs == null) {  // FIXME - observed to happen for in gitbug498 for JMLObjectBag.insert
                // FIXME - A hack - the .jml file should have been read for org.jmlspecs.lang.JMLList
                if (msym.toString().equals("size()") && msym.owner.toString().equals(Strings.jmlSpecsPackage + ".JMLList")) return true;
                boolean isPure =  isPureClass((ClassSymbol)msym.owner);
                if (isPure && print) System.out.println("  ISPURE-N " + symbol.owner + " " + symbol);
                if (isPure) return true;
            } else {
                boolean isPure = isPureLocal(msym); // Also checks enclosing class
                if (isPure && print) System.out.println("  ISPURE " + symbol.owner + " " + symbol +  " " + msym.owner + "." + msym);
                if (isPure) return true;
            }
        }
        if (print) System.out.println("  NOTPURE " + symbol.owner + " " + symbol);
        return false;
    }
    
    public boolean isAnyPurityMethod(MethodSymbol symbol) {
        var t = determinePurity(symbol);
        if (t == null) return false;
        var k = t.jmlclausekind;
        if (k == NO_STATE) return true;
        if (k == STRICTLY_PURE) return true;
        if (k == SPEC_PURE) return true;
        if (k == PURE) return true;
        return false;
    }

    public boolean isSpecPureMethod(MethodSymbol symbol) {
        var t = determinePurity(symbol);
        return t != null && t.jmlclausekind == SPEC_PURE;
    }

    public boolean isStrictlyPureMethod(MethodSymbol symbol) {
        var t = determinePurity(symbol);
        return t != null && t.jmlclausekind == STRICTLY_PURE;
    }
    
    public boolean isSpecOKMethod(MethodSymbol msym) {
        var t = determinePurity(msym);
        if (t == null) return false;
        var k = t.jmlclausekind;
        if (k == SPEC_PURE || k == STRICTLY_PURE || k == NO_STATE) return true;
        if (k == PURE) {
            Type ty = msym.getReturnType();
            if (utils.isJavaOrJmlPrimitiveType(ty)) return true;
        }
        return false;  
    }

    public JmlToken findPurityModifier(JmlModifiers mods) {
        return utils.findModifier(mods,  Modifiers.SPEC_PURE, Modifiers.STRICTLY_PURE, Modifiers.PURE, Modifiers.NO_STATE);
    }
    
    public JmlToken determinePurity(MethodSymbol msym) {
        boolean print = false; // msym.toString().contains("add");// && msym.owner.toString().equals("java.util.Collection");
        JmlModifiers mods = getSpecsModifiers(msym);
        if (print) System.out.println("DP_REQUEST " + msym.owner + " " + msym + " " + mods);
        if (mods != null) {
            var a = utils.findModifier(mods,  Modifiers.SPEC_PURE, Modifiers.STRICTLY_PURE, Modifiers.PURE, Modifiers.NO_STATE);
            if (print) System.out.println("DIRECT  " + msym.owner + " " + msym + " " + a);
            if (a != null) return a;
        }
        JmlToken best = null;
        for (var mp: utils.parents(msym, false)) {
            var p = determinePurity(mp);
            if (print) System.out.println("DET  " + msym.owner + " " + msym + " " + mp.owner + " " + mp + " " + p);
            if (p == null) continue;
            if (p.jmlclausekind == Modifiers.NO_STATE) return p;
            else if (p.jmlclausekind == Modifiers.STRICTLY_PURE) best = p;
            else if (p.jmlclausekind == Modifiers.SPEC_PURE && (best == null || best.jmlclausekind != Modifiers.STRICTLY_PURE)) best = p;
            else if (p.jmlclausekind == Modifiers.PURE && (best == null || best.jmlclausekind == Modifiers.PURE)) best = p;
            if (print) System.out.println("OVER " + msym.owner + " " + msym + " " + mp.owner + " " + mp + " " + best);
        }
        if (best != null) return best;
        if (msym.owner instanceof ClassSymbol owner) {
            var m = determinePurity(owner);
            if (print) System.out.println("TOCLASS " + msym.owner + " " + msym + " " + m);
            if (m != null) return m;
        }
        return null;
    }

    public JmlToken determinePurity(ClassSymbol csym) {
        JmlModifiers mods = getSpecsModifiers(csym);
        if (mods != null) {
            var a = utils.findModifier(mods,  Modifiers.SPEC_PURE, Modifiers.STRICTLY_PURE, Modifiers.PURE, Modifiers.NO_STATE);
            //if (csym.toString().equals("java.lang.Iterable")) System.out.println("Iterable-A " + a);
            //if (csym.toString().equals("java.util.Collection")) System.out.println("Collection-A " + a);
            if (a != null) return a;
        }
        if (csym.owner instanceof ClassSymbol owner) {
            var m = determinePurity(owner);
            //if (csym.toString().equals("java.lang.Iterable")) System.out.println("Iterable-B " + m);
            //if (csym.toString().equals("java.util.Collection")) System.out.println("Collection-B " + m);
            if (m != null) return m;
        }
        //if (csym.toString().equals("java.lang.Iterable")) System.out.println("Iterable NULL");
        //if (csym.toString().equals("java.util.Collection")) System.out.println("Collection NULL");
        return null;
    }

    /** Returns true if the given method symbol is itself annotated with some purity */
    public boolean isPureLocal(MethodSymbol symbol) {
        JmlModifiers mods = getSpecsModifiers(symbol);
        if (mods != null) {
            //if (print) System.out.println("MODS " + symbol.owner + " " + symbol + " " + mods + " " + mods.annotations + " " + utils.hasModifier(mods,  Modifiers.PURE) + " " + utils.hasModifier(mods,  Modifiers.NO_STATE) + " " + isPure((Symbol.ClassSymbol)symbol.owner));
            if (utils.hasModifier(mods,  Modifiers.PURE, Modifiers.NO_STATE)) return true; 
        }
        //if (print) System.out.println("MODS " + symbol.owner + " " + symbol + "  NULL MODS");
        return isPureClass((ClassSymbol)symbol.owner);
    }
    
    public boolean isPureClass(ClassSymbol symbol) {
        // Classes do not garner purity from enclosing or superclasses
        if (utils.hasModifier(getSpecsModifiers(symbol), Modifiers.PURE)) return true;
        return false;
    }
    
//    public boolean isPureClass(ClassSymbol symbol) {
//        if (isPureLocal(symbol)) return true;
//        if (symbol.owner instanceof ClassSymbol c) return isPureClass(c);
//        return false;
//    }
    
    /** Returns true if the given method symbol is annotated as Query */
    public boolean isQuery(MethodSymbol symbol) {
    	JmlModifiers mods = getSpecsModifiers(symbol);
    	if (utils.hasModifier(mods,  Modifiers.QUERY)) return true; 
        return false;
    }
    
    public boolean fieldSpecHasModifier(VarSymbol sym, ModifierKind token) {
    	JmlModifiers mods = getSpecsModifiers(sym);
    	return utils.hasModifier(mods, token); 
    }

//    public boolean methodSpecHasAnnotation(MethodSymbol sym, ModifierKind token) {
//    	JmlModifiers mods = getSpecsModifiers(sym);
//    	return utils.hasMod(mods, token); 
//    }
    
    public static class VarSpecs {
        public boolean isNonNull;
    }
    
    public static class BlockSpecs {
    	public JmlModifiers mods;
    	public JmlMethodSpecs specCases;
    	public Env<AttrContext> specsEnv;
        public SpecsStatus status;
    	public BlockSpecs(JmlModifiers mods, JmlMethodSpecs specCases, Env<AttrContext>  env) {
    		this.mods = mods;
    		this.specCases = specCases;
    		this.specsEnv = env;
    		this.status = SpecsStatus.SPECS_LOADED;
    	}
    }

    
    public static MethodSpecs copy(MethodSpecs m, Void p, JmlTreeCopier copier) {
        if (m == null) return null;
        MethodSpecs mr = new MethodSpecs(m.cases.decl);
        mr.cases = copier.copy(m.cases,p);
        mr.queryDatagroup = m.queryDatagroup;
        mr.secretDatagroup = m.secretDatagroup;
        mr.mods = copier.copy(m.mods,p);
        mr.specsEnv = m.specsEnv;
        return mr;
    }
    
    /** An ADT to hold the specs for a method or block */
    public static class MethodSpecs {
        
        public MethodSymbol javaSym;
    	public MethodSymbol specSym;
    	public JmlMethodDecl javaDecl;
    	public JmlMethodDecl specDecl;
        public JCTree.JCModifiers mods;
        public VarSymbol queryDatagroup;
        public VarSymbol secretDatagroup;
        public JmlMethodSpecs cases;
        public Env<AttrContext> javaEnv;
        public Env<AttrContext> specsEnv;
        public boolean returnNonNull;
        public JCBlock modelBody;
        
        public MethodSpecs(JmlMethodDecl specsDecl) { 
            this.mods = specsDecl.mods;
            this.specDecl = specsDecl;
            if (specsDecl.methodSpecs == null) {
                cases = new JmlMethodSpecs();
                cases.pos = specsDecl.pos;
            } else {
                cases = specsDecl.methodSpecs;
            }
            cases.decl = specsDecl;
            specsEnv = null;
            modelBody = specsDecl.body;
        }
        
        public MethodSpecs(JCTree.JCModifiers mods, JmlMethodSpecs methodSpecs) { 
            this.mods = mods;
            if (methodSpecs.cases == null) {
                cases = new JmlMethodSpecs();
                cases.pos = methodSpecs.pos;
            } else {
                cases = methodSpecs;
            }
            specsEnv = null;
        }

        public void setEnv(Env<AttrContext> env) {
        	//JmlAttr.printEnv(env, "SETENV " + this.msym);
            specsEnv = env;
        }

        // FIXME - is this useful? Where is it used?
        public String toString() {
            return JmlPretty.write(cases) + Strings.eol + JmlPretty.write(mods);
        }
    }

    /** An ADT to hold the specs for a field declaration */
    public static class FieldSpecs extends VarSpecs {
        
        /** Modifiers pertinent to this field's specifications */
        public JmlModifiers mods;

        /** A list of the clauses pertinent to this field (e.g. in, maps) */
        public ListBuffer<JmlTree.JmlTypeClause> list = new ListBuffer<JmlTree.JmlTypeClause>();
        
        public JavaFileObject source() {
            return decl == null ? null : decl.source();
        }
        
        //@ nullable
        public JmlVariableDecl decl; // The textual origin of the field specifications, if any
        
        // FIXME - should this be initialized with the specsDecl? and are the clauses already present?
        /** Creates a FieldSpecs object initialized with only the given modifiers */
        public FieldSpecs(JmlVariableDecl decl) { 
            this.decl = decl;
            this.mods = (JmlModifiers)(decl.mods);
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
    /** An ADT to hold the specs for a local variable or formal parameter declaration */
    public static class LocalSpecs extends VarSpecs {
        
        /** Modifiers pertinent to this field's specifications */
        public JmlModifiers mods;
        
        public MethodSymbol owner;
        
        public JavaFileObject source() {
            return decl == null ? null : decl.source();
        }
        
        //@ nullable
        public JmlVariableDecl decl; // The textual origin of the field specifications, if any
        
        // FIXME - should this be initialized with the specsDecl? and are the clauses already present?
        /** Creates a FieldSpecs object initialized with only the given modifiers */
        public LocalSpecs(JmlVariableDecl decl, boolean isNN, MethodSymbol owner) { 
            this.decl = decl;
            this.mods = (JmlModifiers)(decl.mods);
            this.owner = owner;
            this.isNonNull = isNN;
        }
        
        @Override
        public String toString() {
            StringWriter s = new StringWriter();
            JmlPretty p = new JmlPretty(s, false);
            mods.accept(p);
            try { p.println(); } catch (IOException e) {} // it can't throw up, and ignore if it does
                                // FIXME - println only if there are mods?
            return s.toString();
            
        }
    }
    
    /** Finds the specs file for a given compilation unit.
     * @param jmlcu The compilation unit of the Java source, if any
     * @param specs if true, looks for any specs file; if false, looks for Java file
     * @return the source object of the specifications
     */
    /*@ nullable */
    public JavaFileObject findSpecs(JmlCompilationUnit jmlcu, boolean specs) {
        JCTree.JCExpression pkgName = (JCExpression)jmlcu.getPackageName();
        String pack = pkgName == null ? null : pkgName.toString();
        String filepath = jmlcu.getSourceFile().getName();
        // In the following, we need a name as the prefix to look for the specs.
        // That is supposed to be the same as the name of the public class within
        // the file, and thus the same as the name of the file itself.
        // However, a file may have no public classes within it - so 
        // the best indication of the spec file name is the name of the
        // java file just parsed.
        // (TODO) Unfortunately, there is no guarantee as to what getName()
        // will return.  It would be safer, but a pain, to dismember the 
        // associated URI. (getName is even deprecated within some subclasses)
        int i = filepath.lastIndexOf('/');
        int ii = filepath.lastIndexOf('\\');
        if (i < ii) i = ii;
        int k = filepath.lastIndexOf(".");
        String rootname = k >= 0 ? filepath.substring(i+1,k) : filepath.substring(i+1);
        JavaFileObject f;
        if (specs) {
            f = JmlSpecs.instance(context).findAnySpecFile(pack == null ? rootname : (pack + "." + rootname));
        } else {
            String path = (pack == null ? rootname : (pack + "." + rootname)).replace('.', '/') + Strings.javaSuffix;
            f = JmlSpecs.instance(context).findSpecificSourceFile(path);
        }
        return f;
    }
 
	Map<Symbol, SpecsStatus> specsStatus = new java.util.HashMap<>();
	
	public SpecsStatus status(Symbol sym) {
		var s = specsStatus.get(sym);
		return (s == null) ? SpecsStatus.NOT_LOADED : s;
	}
	
	public boolean statusOK(Symbol sym) {
		var s = specsStatus.get(sym);
		return s != SpecsStatus.ERROR;
	}
	
	public void setStatus(Symbol sym, SpecsStatus status) {
		specsStatus.put(sym, status);
	}

    public static enum SpecsStatus {
    	NOT_LOADED,
    	QUEUED,
    	SPECS_LOADED,
    	SPECS_ATTR,
    	ERROR;
    	
    	public boolean less(SpecsStatus s) { return this.ordinal() < s.ordinal(); }
    	
    }
    	
}

