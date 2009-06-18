package org.jmlspecs.openjml;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.URI;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import javax.tools.DiagnosticListener;
import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;
import javax.tools.SimpleJavaFileObject;
import javax.tools.JavaFileObject.Kind;

import org.jmlspecs.annotations.NonNull;
import org.jmlspecs.annotations.Nullable;
import org.jmlspecs.openjml.JmlSpecs.Dir;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.esc.BasicBlocker;
import org.jmlspecs.openjml.esc.BasicProgram;
import org.jmlspecs.openjml.esc.JmlEsc;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;

import tests.TestJavaFileObject;

import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.main.JavaCompiler.CompileState;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;

/** This class is a wrapper and publicly published API for the OpenJML tool 
 * functionality.  In principle, any external programmatic interaction with
 * openjml would go through methods in this class.
 * <P>
 * The class is used as follows.  The user creates a new API object and makes
 * calls to it; each distinct API object encapsulates a completely separate
 * compilation context.  What would ordinarily be command-line options are
 * specified on creation of the API object; for the most part they are not
 * changeable after the compilation context has been created (where change is
 * allowed, a method call is provided).
 * <P>
 * There are also static methods, named execute, that are public entry points to the
 * various tools (jml checker, jmldoc, ...) that openjml provides.  It performs 
 * a one-time processing of files, without making the classes and ASTs available,
 * just like a command-line execution would do.
 * <P>
 * Public API for tool actions:
 * <UL>
 * <LI>API -- TBD - one initializes, one does not
 * <LI>compile - compiles and typechecks a set of files, retaining ASTs and the like;
 *          the arguments are both the options and the files/directories
 * <LI>parseSingleFile - parses a single java or spec file, without parsing any
 *          other compilation units and without entering or checking any symbols
 * <LI>parseFiles - parses a set of java files and their specification files, if
 *          any, returning a list of ASTs; no symbol table entries or type
 *          checking is performed.
 * <LI>enterAndCheck - accepts a set of ASTs, entering types and other names into
 *          the symbol table, and typechecking the result
 * <LI>doEsc - performs ESC on the class or method corresponding to the given symbol
 * </UL>
 * Public API for various utility routines:
 * <UL>
 * <LI>getSpecs - returns an object holding the specs for the Type, Method, or 
 *          field denoted by the argument
 * <LI>getAllSpecs - returns all the (inherited) specs for the given type or method
 * <LI>getPackageSymbol - returns the symbol for a fully-qualified package name
 * <LI>getClassSymbol - returns a Type symbol given a String holding a fully
 *          qualified class name
 * <LI>getClassAST - returns the AST for the given class, denoted by a String
 * <LI>collectSuperMethods - returns a list of all the super types and interfaces
 *          of the argument (including the argument)
 * <LI>collectSuperMethods - returns a list of all the methods in classes and interfaces
 *          that this method overrides, including itself
 *          holding the fully qualified class name
 * <LI>prettyPrint - prints out a String representation of the argument
 * </UL>
 * @author David Cok
 *
 */
public class API {
    
    public static enum Tool {
        PARSE_ONLY, // parse specified files only (and not any referenced classes)
        PARSE, // parse files and referenced classes only
        CHECK, // typecheck
        JMLDOC, // generate jmldoc for all specified classes
        ESC, // do static checking on all specified files
        RAC, // generate compiled .class files with JML runtime checks
    }

    /** Returns the string describing the version of OpenJML that is this
     * set of classes.
     * @return the version of this instance of OpenJML
     */
    public static @NonNull String version() {
        return JavaCompiler.version();
    }
    
    public static int execute(@NonNull String ... args) {
        int ret = org.jmlspecs.openjml.Main.execute(args);
        return ret;
    }
    
    public static int execute(PrintWriter writer, DiagnosticListener<JavaFileObject> diagListener, @NonNull String ... args) {
        int ret = org.jmlspecs.openjml.Main.execute(writer,diagListener,args);
        return ret;
    }
    
    public static int execute(@NonNull Tool tool, @NonNull String ... args) {
        int ret = 5;
        try {
            switch (tool) {
                case PARSE_ONLY:
                    System.out.println(tool + " option not yet implemented");
                    ret = 2;
                    break;
                case PARSE:
                    System.out.println(tool + " option not yet implemented");
                    ret = 2;
                    break;
                case CHECK:
                    // FIXME - this does not yet stop after type-checking
                    ret = org.jmlspecs.openjml.Main.execute(args);
                    break;
                case JMLDOC:
                    ret = org.jmlspecs.openjml.jmldoc.Main.execute(args);
                    break;
                case ESC:
                case RAC:
                    System.out.println(tool + " option not yet implemented");
                    ret = 2;
                    break;
            }
        } catch (Exception e) {
            System.out.println("Exception caught at the top-level: " + e);
            e.printStackTrace(System.out);
            return 3;
        }
        return ret;
    }
    
    /** The encapsulated org.jmlspecs.openjml.Main object */
    protected Main main = null;
    
    /** The encapsulated compilation context */
    public Context context = null;
    
    /** The log (for the current compilation context) */
    protected Log log;
    
    //@ initially main != null;
    
    /** Creates a new compilation context, initialized with given command-line arguments (no files or directories).
     * @param args the command-line options and initial set of files with which
     * to load the compilation environment
     */
    //@ ensures isOpen;
    public API(@NonNull String ... args) throws Exception {
        this(new PrintWriter(System.err),null,args);
    }
    
    /** Creates an API, with all options set to default values, and
     * set to send informational and diagnostic
     * output to System.out.
     */
    //@ ensures isOpen;
    public API() throws java.io.IOException {
        this(new PrintWriter(System.err),null);
    }
    
    /** Creates an uninitialized API that will send informational output to the
     * given PrintWriter and diagnostic output to the given listener.
     * @param writer
     * @param listener
     */
    //@ ensures isOpen;
    public API(PrintWriter writer, DiagnosticListener<? extends JavaFileObject> listener, String... args) throws java.io.IOException {
        main = new Main(Main.applicationName,writer,listener,args);
        context = main.context;
        Log.instance(context).multipleErrors = true;
    }
    
    /** The (possibly null) listener for progress reports. */
    protected @Nullable Main.IProgressReporter delegate = null;
    
    /** Sets a progress listener that hears any progress reports (e.g. names of
     * files as they are parsed).  Any previous listener is forgotten (there is
     * just one listener at a time).
     * @param p The listener
     */
    public void setProgressReporter(@Nullable Main.IProgressReporter p) {
        delegate = p;
        if (main.progressDelegate != null) main.progressDelegate.setDelegate(p);
    }
    
    /** Runs a compilation with the given command-line arguments.  This will
     * delete the previous compilation context and create a new one.
     * @param args the command-line arguments (options and files)
     * @return a return code (0=success, 1,2,3 = various kinds of errors)
     */
    //@ requires isOpen && args != null && \nonnullarguments(args);
    //@ ensures isOpen;
    public int compile(String[] args) {
        int ret = main.compile(args);
        context = main.context;
        return ret;
    }
    
    static public int jmldoc(String[] args) {
        return org.jmlspecs.openjml.jmldoc.Main.execute(args);
    }
    
    /** Initializes the API object with the given command-line arguments.  The
     * API object may not be already initialized
     * @param args command-line options without files or directories
     * @return this object
     * @throws Exception
     */
    public API initialize(String[] args) throws Exception {
        if (context != null) {
            // FIXME - already initialized
            return this;
        }
        main.initialize(args);
        main.context = context;
        log = Log.instance(context);
        return this;
    }
    
    public int enterAndCheck(JmlCompilationUnit... trees) throws IOException {
        if (context == null) {
            // FIXME - error
            return 1;
        }
        ListBuffer<JCCompilationUnit> list = new ListBuffer<JCCompilationUnit>();
        for (JmlCompilationUnit c: trees) list.append(c);
        return enterAndCheck(list.toList());
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public int enterAndCheck(Collection<? extends JmlCompilationUnit> trees) throws java.io.IOException {
        if (context == null) {
            // FIXME - error
            return 1;
        }
        ListBuffer<JCCompilationUnit> list = new ListBuffer<JCCompilationUnit>();
        for (JmlCompilationUnit c: trees) list.append(c);
        return enterAndCheck(list.toList());
    }
    
    protected int enterAndCheck(List<JCCompilationUnit> list) throws IOException {
        JmlCompiler jcomp = (JmlCompiler)JmlCompiler.instance(context);
        
        JavaCompiler dc =
            jcomp.processAnnotations(
                    jcomp.enterTrees(jcomp.stopIfError(CompileState.PARSE, list)),
                com.sun.tools.javac.util.List.<String>nil());
        dc.flow(dc.attribute(dc.todo));
        int errs = Log.instance(context).nerrors;
        Log.instance(context).nerrors = 0;
        return errs;
    }

    /** Parses each java file and its specs returning a list of the ASTs corresponding
     * java files; the spec files are automatically found according to JML rules 
     * (do not list them on the command line);  the ASTs of the spec files are contained in the 
     * JmlCompilationUnit.specsSequence.  Error messages are reported separately;
     * if there are errors, a parse tree may be incomplete.  The trees are not
     * type-checked and do not have any name resolution applied.
     * @param files the java.io.File objects of the input .java files
     * @return a list of corresponding ASTs
     */
    //@ requires \nonnullelements(files);
    //@ requires isOpen;
    //@ ensures isOpen;
    //@ ensures files.length == \result.size();
    //@ ensures (* output elements are non-null *); // FIXME - what about parse errors?
    public @NonNull java.util.List<JmlCompilationUnit> parseFiles(@NonNull File... files) {
        JmlCompiler c = (JmlCompiler)JmlCompiler.instance(context);
        c.inSequence = false;
        Iterable<? extends JavaFileObject> fobjects = ((JavacFileManager)context.get(JavaFileManager.class)).getJavaFileObjects(files);
        ArrayList<JmlCompilationUnit> trees = new ArrayList<JmlCompilationUnit>();
        for (JavaFileObject fileObject : fobjects)
            trees.add((JmlCompilationUnit)c.parse(fileObject));
        return trees;
    }
    
    /** Produces a parse tree for a single file without any specifications; the
     * file may be either a .java or a specification file.  The trees are not
     * type-checked and do not have any name resolution applied and are not made
     * part of the compilation context.
     * @param file the file to be parsed
     * @return the parse tree for the file
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public JmlCompilationUnit parseSingleFile(File file) {
        JmlCompiler c = (JmlCompiler)JmlCompiler.instance(context);
        c.inSequence = true;
        Iterable<? extends JavaFileObject> fobjects = ((JavacFileManager)context.get(JavaFileManager.class)).getJavaFileObjects(file);
        return ((JmlCompilationUnit)c.parse(fobjects.iterator().next()));
    }
    
    
    /** Produces a parse tree for a single file without any specifications; the
     * file may be either a .java or a specification file.  The trees are not
     * type-checked and do not have any name resolution applied and are not made
     * part of the compilation context.
     * @param file the file to be parsed
     * @return the parse tree for the file
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public JmlCompilationUnit parseString(@Nullable String name, @NonNull String content) throws Exception {
        JmlCompiler c = (JmlCompiler)JmlCompiler.instance(context);
        JavaFileObject file = new StringJavaFileObject(name,content);
        c.inSequence = true;  // true so that no searching for spec files happens
        Iterable<? extends JavaFileObject> fobjects = List.<JavaFileObject>of(file);
        return ((JmlCompilationUnit)c.parse(fobjects.iterator().next()));
    }
    
    /** Parses, creates symbol table symbols and typechecks the given set of files.
     *  This method may be called multiple times to add new classes to the symbol
     *  table entries.  Other files may be parsed and entered if they are dependencies
     *  of the files given as arguments.
     * @param files the set of files to parse and check
     * @throws java.io.IOException
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public void parseAndCheck(File... files) throws java.io.IOException {
        JmlCompiler c = (JmlCompiler)JmlCompiler.instance(context);
        c.inSequence = false;
        Iterable<? extends JavaFileObject> sourceFileObjects = ((JavacFileManager)context.get(JavaFileManager.class)).getJavaFileObjects(files);
        ListBuffer<JavaFileObject> list = ListBuffer.<JavaFileObject>lb();
        for (JavaFileObject jfo : sourceFileObjects) list.append(jfo);
        c.processAnnotations(c.enterTrees(c.stopIfError(CompileState.PARSE,c.parseFiles(list.toList()))),
                main.classnames.toList());
    }
    
    /** Retrieves the symbol table entry for a given name, based on files already
     * parsed and present in the symbol table.
     * @param qualifiedName the dot and dollar (for nested classes) separated 
     * class name
     * @return the class symbol or null if it is not found
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable ClassSymbol getClassSymbol(@NonNull String qualifiedName) {
        Name n = Names.instance(context).fromString(qualifiedName);
        return Symtab.instance(context).classes.get(n);
    }
    
    /** Retrieves the symbol table entry for a given package name, based on files already
     * parsed and present in the symbol table.
     * @param qualifiedName the dot separated package name
     * @return the package symbol or null if it is not found
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable PackageSymbol getPackageSymbol(@NonNull String qualifiedName) {
        Name n = Names.instance(context).fromString(qualifiedName);
        return Symtab.instance(context).packages.get(n);
    }
    
    /** Returns the type specs for the given class symbol
     * 
     * @param sym the class symbol whose specs are wanted
     * @return the specs for that class
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull TypeSpecs getSpecs(@NonNull ClassSymbol sym) {
        return JmlSpecs.instance(context).get(sym);
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public java.util.List<TypeSpecs> getAllSpecs(@NonNull ClassSymbol sym) {
        java.util.List<ClassSymbol> list = new ArrayList<ClassSymbol>();
        collectSuperTypes(sym,list);
        JmlSpecs specs = JmlSpecs.instance(context);
        java.util.List<TypeSpecs> tslist = new ArrayList<TypeSpecs>();
        for (ClassSymbol c: list) tslist.add(specs.get(c));
        return tslist;
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public JmlMethodDecl getJavaDecl(MethodSymbol msym) {
        JmlClassDecl cdecl = getJavaDecl((ClassSymbol)msym.owner);
        for (JCTree t: cdecl.defs) {
            if (t instanceof JmlMethodDecl && ((JmlMethodDecl)t).sym == msym) {
                return (JmlMethodDecl)t;
            }
        }
        return null;
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public void setOption(String name, String value) {
        Options.instance(context).put(name,value);
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public void setOption(String name) {
        Options.instance(context).put(name,"");
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public void removeOption(String name) {
        Options.instance(context).remove(name);
    }
    

    
//    //@ requires isOpen;
//    //@ ensures isOpen;
//    static public void setLibrarySpecsPath(String[] dirs) {
//        JmlSpecs.externalDefaultSpecs = dirs;
//    }
//    
//    //@ requires isOpen;
//    //@ ensures isOpen;
//    public static void setExternalRuntime(@Nullable String[] paths) {
//        JmlSpecs.externalRuntime = paths;
//    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public java.util.List<String> getSpecsPath() {
        java.util.List<Dir> list = JmlSpecs.instance(context).getSpecsPath();
        java.util.List<String> out = new LinkedList<String>();
        for (Dir d: list) out.add(d.name());
        return out;
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public void doEsc(MethodSymbol msym) {
        JmlMethodDecl decl = getJavaDecl(msym);
        JmlEsc.instance(context).proveMethod(decl);
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public JmlClassDecl getJavaDecl(ClassSymbol csym) {
        JCTree tree = JmlEnter.instance(context).getClassEnv(csym).tree;
        return (JmlClassDecl)tree;
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public void doEsc(ClassSymbol csym) {
        
        JCTree tree = JmlEnter.instance(context).getClassEnv(csym).tree;
        JmlClassDecl decl = (JmlClassDecl)tree;
        JmlEsc.instance(context).visitClassDef(decl);
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public IProverResult getProofResult(MethodSymbol msym) {
        return JmlEsc.instance(context).proverResults.get(msym);
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public String getBasicBlockProgram(MethodSymbol msym) {
        JmlMethodDecl tree = getJavaDecl(msym);
        JmlClassDecl cdecl = getJavaDecl((ClassSymbol)msym.owner);
        BasicProgram program = BasicBlocker.convertToBasicBlocks(context, tree, JmlSpecs.instance(context).getSpecs(msym).cases.deSugared, cdecl);
        return program.write("BASIC BLOCK PROGRAM FOR " + msym.owner.getQualifiedName() + "." + msym.toString() + "\n\n");
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public void collectSuperTypes(@NonNull ClassSymbol csym, java.util.List<ClassSymbol> list) {
        Type tt = csym.getSuperclass();
        if (tt != null && tt != Type.noType) {
            ClassSymbol s = (ClassSymbol)tt.tsym; // FIXME - when is a TypeSymbol not a class Symbol - parameterization?
            collectSuperTypes(s,list);
        }
        for (Type t: csym.getInterfaces()) {
            ClassSymbol c = (ClassSymbol)t.tsym;
            if (!list.contains(c)) {
                collectSuperTypes(c,list);  // c and any super interfaces are added here
            }
        }
        list.add(csym);
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public void collectSuperMethods(@NonNull MethodSymbol msym, java.util.List<MethodSymbol> list) {
        java.util.List<ClassSymbol> clist = new ArrayList<ClassSymbol>();
        collectSuperTypes(msym.enclClass(),clist);
        for (ClassSymbol c: clist) {
            // find a method matching msym in c
            Scope.Entry e = c.members().lookup(msym.getSimpleName());
            while (e != null) {
                Symbol sym = e.sym;
                e = e.sibling;
                if (!(sym instanceof MethodSymbol)) continue;
                MethodSymbol mmsym = (MethodSymbol)sym;
                if (!msym.overrides(mmsym,msym.enclClass(),Types.instance(context),false)) continue;
                list.add(mmsym);
                break;
            }
        }
    }
    
    /** Returns the specs for a given method
     * 
     * @param sym the method symbol whose specs are wanted
     * @return the specs for that method
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull JmlSpecs.MethodSpecs getSpecs(@NonNull MethodSymbol sym) {
        return JmlSpecs.instance(context).getSpecs(sym);
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public java.util.List<JmlSpecs.MethodSpecs> getAllSpecs(@NonNull MethodSymbol msym) {
        java.util.List<JmlSpecs.MethodSpecs> tslist = new ArrayList<JmlSpecs.MethodSpecs>();
        if (msym.isStatic() || msym.isConstructor()) {
            tslist.add(getSpecs(msym));
            return tslist;
        }
        java.util.List<MethodSymbol> list = new ArrayList<MethodSymbol>();
        collectSuperMethods(msym,list);
        JmlSpecs specs = JmlSpecs.instance(context);
        for (MethodSymbol c: list) tslist.add(specs.getSpecs(c));
        return tslist;
    }
    
    /** Returns the specs for a given method in denested form
     * 
     * @param sym the method symbol whose specs are wanted
     * @return the specs for that method
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull JmlMethodSpecs getDenestedSpecs(@NonNull MethodSymbol sym) {
        return JmlSpecs.instance(context).getDenestedSpecs(sym);
    }
    
    /** Returns the specs for a given field
     * 
     * @param sym the field symbol whose specs are wanted
     * @return the specs for that field
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull FieldSpecs getSpecs(@NonNull VarSymbol sym) {
        return JmlSpecs.instance(context).getSpecs(sym);
    }
    // FIXME - what about nested classes?  what separator?
    /** Returns the AST for a given class (not compilation unit)
     * 
     * @param qualifiedName the fully-qualified name of the class whose AST is wanted
     * @return the AST for that class
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull JmlClassDecl getClassAST(@NonNull String qualifiedName) {
        return getClassAST(getClassSymbol(qualifiedName));
    }
    
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull JmlClassDecl getClassAST(@NonNull ClassSymbol sym) {
        return (JmlClassDecl)JmlEnter.instance(context).getEnv(sym).tree;
    }
    
    
    /** Prints out a given parse tree (or subtree).  If likeSource is true,
     * then the output is valid Java source, if the tree is a Java construct
     * (e.g. JML constructs are in inside JML comments).  If likeSource is
     * false, no JML comment symbols are used and other internal information
     * may also be output.
     * 
     * @param ast the ast to print
     * @param likeSource if true, prints out as valid source code
     * @return a string containing the output
     * @throws Exception
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull String prettyPrint(@NonNull JCTree ast, boolean likeSource) throws Exception {
        StringWriter s = new StringWriter();
        ast.accept(JmlPretty.instance(s,likeSource));
        return s.toString();
    }
    
    /** Prints out a list of parse trees.  If likeSource is true,
     * then the output is valid Java source, if the tree is a Java construct
     * (e.g. JML constructs are in inside JML comments).  If likeSource is
     * false, no JML comment symbols are used and other internal information
     * may also be output.
     * 
     * @param astlist a list of asts to print
     * @param likeSource if true, prints out as valid source code
     * @param sep  a String that is written out as a separator
     * @return a string containing the output
     * @throws Exception
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull String prettyPrint(@NonNull java.util.List<? extends JCTree> astlist, boolean likeSource, @NonNull String sep) throws Exception {
        StringWriter s = new StringWriter();
        boolean isFirst = true;
        for (JCTree ast: astlist) {
            if (!isFirst) { s.append(sep); isFirst = false; }
            JmlPretty.instance(s,likeSource).print(ast);
        }
        return s.toString();
    }
    
    /** Closes this instance of the compiler, releasing internal memory;
     * no further use of the instance is permitted (and will likely result in
     * exceptions thrown).
     */
    //@ requires isOpen;
    //@ assignable isOpen;
    //@ ensures !isOpen;
    public void close() {
        JmlCompiler.instance(context).close();
        context = null;
        main = null;
    }
    
    //@ public model boolean isOpen; private represents isOpen = main != null;

    public JavaFileObject makeJFOfromString(String name, String content) throws Exception {
        return new StringJavaFileObject(name,content);
    }
    
    public JavaFileObject makeJFOfromFilename(String filename) {
        JavacFileManager dfm = (JavacFileManager)context.get(JavaFileManager.class);
        return dfm.getFileForInput(filename);
    }
    /** This class encapsulates a String as a JavaFileObject, making it a pseudo-file
     */
    public static class StringJavaFileObject extends SimpleJavaFileObject {
        
        /** The content of the mock file */
        //@ non_null
        protected String content;
        
        /** A fake file name, used when the user does not want to be bothered
         * supplying one.  We have to make and cache this because it is a pain to
         * deal with exceptions in constructors.
         */
        //@ non_null
        static final protected URI uritest = makeURI();
        
        /** A utility method to make the URI, so it can handle the exceptions. 
         * We don't try to recover gracefully if the exception occurs - this is
         * just used in testing anyway. */
        private static URI makeURI() {
            try {
                return new URI("file:///TEST.java");
            } catch (Exception e) {
                System.err.println("CATASTROPHIC EXIT - FAILED TO CONSTRUCT A MOCK URI");
                System.exit(3);
                return null;
            }
        }


        /** Constructs a new JavaFileObject of kind SOURCE or OTHER depending on the
         * filename extension
         * @param filename the filename to use (no leading slash) (null indicates to
         *          use the internal fabricated filename)
         * @param s the content of the pseudo file
         * @throws Exception if a URI cannot be created
         */
        public StringJavaFileObject(/*@ nullable */String filename, /*@ non_null */String s) throws Exception {
            // This takes three slashes because the filename is supposed to be absolute.
            // In our case this is not a real file anyway, so we pretend it is absolute.
            super(filename == null ? uritest : new URI("file:///" + filename),
                    filename == null || filename.endsWith(".java") ? Kind.SOURCE : Kind.OTHER);
            content = s;
        }

        /** Overrides the parent to provide the content directly from the String
         * supplied at construction, rather than reading the file.  This is called
         * by the system.
         */
        @Override
        public CharSequence getCharContent(boolean ignoreEncodingErrors) {
            return content;
        }
        
        /** Overrides the parent method to allow name compatibility between 
         * pseudo files of different kinds.
         */
        // Don't worry about whether the kinds match, just the file extension
        @Override
        public boolean isNameCompatible(String simpleName, Kind kind) {
            String s = uri.getPath();
            if (kind == Kind.OTHER) {
                int i = s.lastIndexOf('/');
                s = s.substring(i+1);
                return s.startsWith(simpleName);
            } else {
                String baseName = simpleName + kind.extension;
                return s.endsWith("/" + baseName);
            }
        }
        
        /** Returns true if the receiver and argument are the same object */
        public boolean equals(Object o) {
            return o == this;
        }
        
        /** A definition of hashCode, since we have a definition of equals */
        public int hashCode() {
            return super.hashCode();
        }
    }
}
