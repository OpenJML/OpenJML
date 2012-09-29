package org.jmlspecs.openjml;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.URI;
import java.util.ArrayList;
import java.util.Collection;

import javax.tools.DiagnosticListener;
import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;
import javax.tools.SimpleJavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.annotation.Pure;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.esc.BasicBlocker;
import org.jmlspecs.openjml.esc.BasicBlocker.TracerBB;
import org.jmlspecs.openjml.esc.BasicProgram;
import org.jmlspecs.openjml.esc.JmlEsc;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;

import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.Enter;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.main.JavaCompiler.CompileState;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Position;

/** This class is a wrapper and publicly published API for the OpenJML tool 
 * functionality.  In principle, any external programmatic interaction with
 * openjml would go through methods in this class.  [In practice some internal
 * classes are exposed as well.]
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
 * The public API consists of the methods with public visibility in this 
 * compilation unit.
 *
 * @author David Cok
 */
public class API {
    
    /** Returns the string describing the version of OpenJML that is this
     * set of classes.
     * @return the version of this instance of OpenJML
     */
    public static @NonNull String version() {
        return JavaCompiler.version();
    }
    
    /** Executes the command-line version of OpenJML, returning the exit code.
     * All output and diagnostics are written to System.out.
     * @param args the command-line arguments
     * @return the exit code (0 is success; 1, 2, 3, 4 are various kinds of errors)
     */
    public static int execute(@NonNull String ... args) {
        int ret = org.jmlspecs.openjml.Main.execute(args);
        return ret;
    }
    
    /** Executes the command-line version of OpenJML, returning the exit code.
     * @param writer the PrintWriter to receive general output
     * @param diagListener a listener to receive reports of diagnostics (e.g. parse or typechecking errors and warnings)
     * @param args the command-line arguments
     * @return the exit code (0 is success; 1, 2, 3, 4 are various kinds of errors)
     */
    public static int execute(@NonNull PrintWriter writer, @Nullable DiagnosticListener<JavaFileObject> diagListener, @NonNull String ... args) {
        int ret = org.jmlspecs.openjml.Main.execute(writer,diagListener,args);
        return ret;
    }
    
    
    /** Executes the jmldoc tool on the given command-line arguments. */
    public static int jmldoc(@NonNull String... args) {
        return org.jmlspecs.openjml.jmldoc.Main.execute(args);
    }
    
    //////////////// Non-static API ////////////////////////////////
    
    /** The encapsulated org.jmlspecs.openjml.Main object */
    protected Main main = null;
    //@ initially main != null;
    
    /** The encapsulated compilation context */
    // protected invariant main != null ==> mail.context == context;
    protected Context context = null;
    
    /** Creates a new compilation context, initialized with given command-line options
     * @param args the command-line options and initial set of files with which
     * to load the compilation environment
     */
    //@ ensures isOpen;
    public API(@NonNull String ... args) throws IOException {
        this(new PrintWriter(System.out),null,args);
    }
        
    /** Creates an API that will send informational output to the
     * given PrintWriter and diagnostic output to the given listener.
     * @param writer
     * @param listener
     */
    //@ ensures isOpen;
    public API(@NonNull PrintWriter writer, 
            @Nullable DiagnosticListener<? extends JavaFileObject> listener, 
            @NonNull String... args) throws java.io.IOException {
        main = new Main(Main.applicationName,writer,listener,args);
        context = main.context;
        Log.instance(context).multipleErrors = true;
    }
    
    /** The compilation context for this API object */
    //@ ensures \result == context;
    @Pure
    public @Nullable Context context() {
        return context;
    }
    
    /** Sets a progress listener that hears any progress reports (e.g. names of
     * files as they are parsed).  Any previous listener is forgotten (there is
     * just one listener at a time).
     * @param p The listener
     */
    public void setProgressReporter(@Nullable Main.IProgressReporter p) {
        if (main.progressDelegate != null) main.progressDelegate.setDelegate(p);
    }
    
    /** Runs a compilation with the given command-line arguments.  This will
     * delete the previous compilation context, including its options, and create a new one.
     * @param args the command-line arguments (options and files)
     * @return a return code (0=success, 1,2,3 = various kinds of errors)
     */
    // FIXME - does compile retain options???
    //@ requires isOpen && args != null && \nonnullarguments(args);
    //@ ensures isOpen;
    public int exec(@NonNull String... args) {
        int ret = main.compile(args);
        context = main.context;
        return ret;
    }
    
    /** Enters and typechecks the provided compilation unit ASTs.  The elements
     * of the list should all be JmlCompilationUnit nodes.
     * @param trees a varargs list or an array of the ASTs to be checked
     * @return the number of errors encountered
     * @throws IOException
     */
    public int enterAndCheck(@NonNull JmlCompilationUnit... trees) throws IOException {
        if (context == null) {
            throw new NullPointerException("There is no valid compilation context");
        }
        if (trees == null) {
            throw new IllegalArgumentException("Argument 'trees' of API.enterAndCheck is null");
        }
        ListBuffer<JCCompilationUnit> list = new ListBuffer<JCCompilationUnit>();
        list.appendArray(trees);
        return enterAndCheck(list.toList());
    }
    
    /** Enters and typechecks the provided compilation unit ASTs.
     * @param trees a collection of the ASTs to be checked
     * @return the number of errors encountered
     * @throws IOException
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public int enterAndCheck(@NonNull Collection<? extends JmlCompilationUnit> trees) throws java.io.IOException {
        if (context == null) {
            throw new NullPointerException("There is no valid compilation context");
        }
        if (trees == null) {
            throw new IllegalArgumentException("Argument 'trees' of API.enterAndCheck is null");
        }
        ListBuffer<JCCompilationUnit> list = new ListBuffer<JCCompilationUnit>();
        list.addAll(trees);
        return enterAndCheck(list.toList());
    }
    
    /** Enters and typechecks the provided compilation unit ASTs.  The elements
     * of the list should all be JmlCompilationUnit nodes.
     * @param list a list of the ASTs to be checked
     * @return the number of errors encountered
     * @throws IOException
     */
    protected int enterAndCheck(@NonNull List<JCCompilationUnit> list) throws IOException {
        JmlCompiler jcomp = (JmlCompiler)JmlCompiler.instance(context);
        JmlTree.Maker maker = JmlTree.Maker.instance(context);
        for (JCCompilationUnit jcu: list) {
            for (JCTree t: jcu.defs) {
                if (t instanceof JmlClassDecl && ((JmlClassDecl)t).typeSpecs == null) JmlParser.filterTypeBodyDeclarations((JmlClassDecl)t,context,maker);
            }
            for (JmlClassDecl t: ((JmlCompilationUnit)jcu).parsedTopLevelModelTypes) {
                if (t.typeSpecs == null) JmlParser.filterTypeBodyDeclarations(t,context, maker);
            }
        }

        JavaCompiler dc =
            jcomp.processAnnotations(
                    jcomp.enterTrees(jcomp.stopIfError(CompileState.PARSE, list)),
                com.sun.tools.javac.util.List.<String>nil());
        dc.flow(dc.attribute(dc.todo));
        int errs = Log.instance(context).nerrors;
        Log.instance(context).nerrors = 0;
        return errs;
    }

    /** Parses each java file and its specs returning a list of the ASTs for corresponding
     * java files; the spec files are automatically found according to JML rules 
     * (do not include them in the arguments);  the ASTs of the spec files are contained in the 
     * JmlCompilationUnit.specsSequence.  Error messages are reported separately
     * through the diagnostic listener;
     * if there are errors, a parse tree may be incomplete.  The trees are not
     * type-checked and do not have any name resolution applied.
     * @param files the java.io.File objects of the input .java files
     * @return a list of corresponding ASTs
     */
    //@ requires \nonnullelements(files);
    //@ requires isOpen;
    //@ ensures isOpen;
    //@ ensures files.length == \result.size();
    //@ ensures (* output elements are non-null *);
    public @NonNull java.util.List<JmlCompilationUnit> parseFiles(@NonNull File... files) {
        JmlCompiler c = (JmlCompiler)JmlCompiler.instance(context);
        c.inSequence = false;
        Iterable<? extends JavaFileObject> fobjects = ((JavacFileManager)context.get(JavaFileManager.class)).getJavaFileObjects(files);
        ArrayList<JmlCompilationUnit> trees = new ArrayList<JmlCompilationUnit>();
        for (JavaFileObject fileObject : fobjects)
            trees.add((JmlCompilationUnit)c.parse(fileObject));
        return trees;
    }
    
    /** Parses each input, finding its specs returning a list of the ASTs corresponding to the
     * java files; the spec files are automatically found according to JML rules 
     * (do not include them in the arguments);  the ASTs of the spec files are contained in the 
     * JmlCompilationUnit.specsSequence.  Error messages are reported separately
     * through the diagnostic listener;
     * if there are errors, a parse tree may be incomplete.  The trees are not
     * type-checked and do not have any name resolution applied.
     * @param inputs a varags list or an array of the JavaFileObjects to use as inputs
     * @return a list of corresponding ASTs
     */
    //@ requires \nonnullelements(inputs);
    //@ requires isOpen;
    //@ ensures isOpen;
    //@ ensures inputs.length == \result.size();
    //@ ensures (* output elements are non-null *);
    public @NonNull java.util.List<JmlCompilationUnit> parseFiles(@NonNull JavaFileObject... inputs) {
        JmlCompiler c = (JmlCompiler)JmlCompiler.instance(context);
        c.inSequence = false;
        ArrayList<JmlCompilationUnit> trees = new ArrayList<JmlCompilationUnit>();
        for (JavaFileObject fileObject : inputs)
            trees.add((JmlCompilationUnit)c.parse(fileObject));
        return trees;
    }
    
    /** Parses each input, finding its specs returning a list of the ASTs corresponding to the
     * java files; the spec files are automatically found according to JML rules 
     * (do not include them in the arguments);  the ASTs of the spec files are contained in the 
     * JmlCompilationUnit.specsSequence.  Error messages are reported separately
     * through the diagnostic listener;
     * if there are errors, a parse tree may be incomplete.  The trees are not
     * type-checked and do not have any name resolution applied.
     * @param inputs a Collection of the JavaFileObjects to use as inputs
     * @return a list of corresponding ASTs
     */
    //@ requires \nonnullelements(inputs);
    //@ requires isOpen;
    //@ ensures isOpen;
    //@ ensures inputs.length == \result.size();
    //@ ensures (* output elements are non-null *);
    public @NonNull java.util.List<JmlCompilationUnit> parseFiles(@NonNull Collection<? extends JavaFileObject> inputs) {
        JmlCompiler c = (JmlCompiler)JmlCompiler.instance(context);
        c.inSequence = false;
        ArrayList<JmlCompilationUnit> trees = new ArrayList<JmlCompilationUnit>();
        for (JavaFileObject fileObject : inputs)
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
    public @NonNull JmlCompilationUnit parseSingleFile(@NonNull File file) {
        JmlCompiler c = (JmlCompiler)JmlCompiler.instance(context);
        c.inSequence = true;
        Iterable<? extends JavaFileObject> fobjects = ((JavacFileManager)context.get(JavaFileManager.class)).getJavaFileObjects(file);
        return ((JmlCompilationUnit)c.parse(fobjects.iterator().next()));
    } // FIXME - check that this works for .jml files
    
    /** Produces a parse tree for the given text; the text must represent a
     * compilation unit for a .java file or a specification file.  The name 
     * is the file path to associate with the text and must include directories
     * corresponding to the purported package holding the java class.  The trees are not
     * type-checked and do not have any name resolution applied and are not made
     * part of the compilation context.
     * @param name the filename to associate with the text (but not the package)
     * @param content the textual content to parse
     * @return the parse tree for the file
     */
    // FIXME - resolve whether the package name must be present
    // TODO: Would like to automatically set the filename, but can't since the
    // JavaFileObject has to be created before parsing and it is immutable
    //@ requires name.length() > 0;
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull JmlCompilationUnit parseString(@NonNull String name, @NonNull String content) throws Exception {
        if (name == null || name.length() == 0) throw new IllegalArgumentException();
        JmlCompiler c = (JmlCompiler)JmlCompiler.instance(context);
        JavaFileObject file = makeJFOfromString(name,content);
        c.inSequence = true;  // true so that no searching for spec files happens
        Iterable<? extends JavaFileObject> fobjects = List.<JavaFileObject>of(file);
        JmlCompilationUnit jcu = ((JmlCompilationUnit)c.parse(fobjects.iterator().next()));
        return jcu;
    }
    
    /** Parses, creates symbol table symbols and typechecks the given set of files.
     *  This method may be called multiple times to add new classes to the symbol
     *  table entries. However if any file depends on another file, it will look for
     *  it on the sourcepath (or specspath). Typically those paths are set to include
     *  the files that are listed in the arguments.
     * @param files the set of files to parse and check
     * @throws java.io.IOException
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public void parseAndCheck(File... files) throws java.io.IOException {
        JmlCompiler c = (JmlCompiler)JmlCompiler.instance(context);
        main.setupOptions();
        c.inSequence = false;
        Iterable<? extends JavaFileObject> sourceFileObjects = ((JavacFileManager)context.get(JavaFileManager.class)).getJavaFileObjects(files);
        ListBuffer<JavaFileObject> list = ListBuffer.<JavaFileObject>lb();
        for (JavaFileObject jfo : sourceFileObjects) list.append(jfo);
        c.processAnnotations(c.enterTrees(c.stopIfError(CompileState.PARSE,c.parseFiles(list.toList()))),
                main.classnames.toList());
        c.flow(c.attribute(c.todo));
    }
    
    // TODO: need an easier way to find out if there are errors from parseAndCheck or enterAndCheck
    // TODO: do we need parseAndCheck for JavaFileObject arguments; for Collection arguments?
    
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

    /** Retrieves the symbol table entry for a given Class name, based on files already
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
    
    /** Retrieves the symbol table entry for a given class name as a member
     * of the given class, based on files already
     * parsed and present in the symbol table.
     * @param csym the owning class
     * @param name the (simple) name of the nested class
     * @return the class symbol or null if it is not found
     */
    public @Nullable ClassSymbol getClassSymbol(@NonNull ClassSymbol csym, @NonNull String name) {
        Scope.Entry e = csym.members().lookup(Names.instance(context).fromString(name));
        if (e == null || e.sym == null) return null;
        while (e.sym != null && e.sym.owner == csym) {
            if (e.sym instanceof ClassSymbol) return (ClassSymbol)e.sym;
            e = e.next();
        }
        return null;
    }
    
    /** Retrieves the symbol table entry for a given method name as a member
     * of the given class, based on files already
     * parsed and present in the symbol table.
     * @param csym the owning class
     * @param name the (simple) name of the method
     * @return the method symbol or null if it is not found
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable MethodSymbol getMethodSymbol(@NonNull ClassSymbol csym, @NonNull String name) {
        Scope.Entry e = csym.members().lookup(Names.instance(context).fromString(name));
        if (e == null || e.sym == null) return null;
        while (e.sym != null && e.sym.owner == csym) {
            if (e.sym instanceof MethodSymbol) return (MethodSymbol)e.sym;
            e = e.next();
        }
        return null;
    } // FIXME - need a way to handle multiple methods with the same name
    
    /** Retrieves the symbol table entry for a given variable name as a member
     * of the given class, based on files already
     * parsed and present in the symbol table.
     * @param csym the owning class
     * @param name the (simple) name of the variable
     * @return the variable symbol or null if it is not found
     */
    public @Nullable VarSymbol getVarSymbol(@NonNull ClassSymbol csym, @NonNull String name) {
        Scope.Entry e = csym.members().lookup(Names.instance(context).fromString(name));
        if (e == null || e.sym == null) return null;
        while (e.sym != null && e.sym.owner == csym) {
            if (e.sym instanceof VarSymbol) return (VarSymbol)e.sym;
            e = e.next();
        }
        return null;
    }
    
    /** Returns the symbol for a class declaration (if type checked)
     * @param decl the type-checked ast node
     * @return the corresponding symbol
     */
    public @Nullable ClassSymbol getSymbol(@NonNull JmlClassDecl decl) {
        return decl.sym;
    }
    
    /** Returns the symbol for a method declaration (if type checked)
     * @param decl the type-checked ast node
     * @return the corresponding symbol
     */
    public @Nullable MethodSymbol getSymbol(@NonNull JmlMethodDecl decl) {
        return decl.sym;
    }
    
    /** Returns the symbol for a variable declaration (if type checked)
     * @param decl the type-checked ast node
     * @return the corresponding symbol
     */
    public @Nullable VarSymbol getSymbol(@NonNull JmlVariableDecl decl) {
        return decl.sym;
    }
    
    /** Returns the AST for a given class (not compilation unit)
     * 
     * @param qualifiedName the fully-qualified name of the class whose AST is wanted
     * @return the AST for that class
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull JmlClassDecl getClassDecl(@NonNull String qualifiedName) {
        return getJavaDecl(getClassSymbol(qualifiedName));
    }
        
    /** Returns the declaration (the AST) corresponding to the given
     * class, if there is one.
     * @param csym the class symbol
     * @return the corresponding AST, or null
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public JmlClassDecl getJavaDecl(ClassSymbol csym) {
        JCTree tree = JmlEnter.instance(context).getClassEnv(csym).tree;
        return (JmlClassDecl)tree;
    }
    
    /** Returns the declaration (the AST) corresponding to the given
     * method, if there is one.
     * @param msym the method symbol
     * @return the corresponding AST, or null
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable JmlMethodDecl getJavaDecl(MethodSymbol msym) {
        JmlClassDecl cdecl = getJavaDecl((ClassSymbol)msym.owner);
        for (JCTree t: cdecl.defs) {
            if (t instanceof JmlMethodDecl && ((JmlMethodDecl)t).sym == msym) {
                return (JmlMethodDecl)t;
            }
        }
        return null;
    }
    
    /** Returns the declaration (the AST) corresponding to the given
     * field, if there is one.
     * @param vsym the field symbol
     * @return the corresponding AST, or null
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable JmlVariableDecl getJavaDecl(VarSymbol vsym) {
        JmlClassDecl cdecl = getJavaDecl((ClassSymbol)vsym.owner);
        for (JCTree t: cdecl.defs) {
            if (t instanceof JmlVariableDecl && ((JmlVariableDecl)t).sym == vsym) {
                return (JmlVariableDecl)t;
            }
        }
        return null;
    }
    
    /** Sets a command-line option to the given value 
     * @param name the option name, including the leading - sign
     * @param value the value to give the option
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public void setOption(String name, String value) {
        Options.instance(context).put(name,value);
        main.setupOptions();
    }

    /** Sets a command-line option to true 
     * @param name the option name, including the leading - sign
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public void setOption(String name) {
        Options.instance(context).put(name,"");
        main.setupOptions();
    }
    
    /** Removes a command-line option 
     * @param name the option name, including the leading - sign
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public void removeOption(String name) {
        Options.instance(context).remove(name);
    }
    
    /** Gets the value of a command-line option (null if not set)
     * @param name the option name, including the leading - sign
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable String getOption(String name) {
        return Options.instance(context).get(name);
    }
    
    
    /** A cached object to search parse trees (not thread safe since static) */
    static protected Finder finder = new Finder();
    
    /** A class that searches parse trees for nodes with a given position range */
    protected static class Finder extends JmlTreeScanner {
        /** Find the node within the given tree that encompasses the given
         * start and end position.
         * @param tree the root of the tree
         * @param startpos the starting char position (from begining of file)
         * @param endpos the ending position
         * @return the best matching node
         */
        public JCTree find(JmlCompilationUnit tree, int startpos, int endpos) {
            this.startpos = startpos;
            this.endpos = endpos;
            this.tree = tree;
            this.scanMode = AST_JML_MODE;
            scan(tree);
            return found;
        }
        
        int startpos;
        int endpos;
        JmlCompilationUnit tree;
        JCTree found = null;
        JmlMethodDecl parentMethod = null;
        
        public void scan(JCTree node) {
            if (node == null) return;
            int sp = node.getStartPosition();
            if (sp == Position.NOPOS && node instanceof JmlMethodInvocation) sp = ((JmlMethodInvocation)node).pos;
            int ep = node.getEndPosition(tree.endPositions);
            // Do this specially because the range of a MethodDecl node does not include the specs
            if (node instanceof JmlMethodDecl) {
                JCTree ftree = found;
                super.scan(node);
                if (found != ftree) parentMethod = (JmlMethodDecl)node;
            } else if (node instanceof JmlVariableDecl) {
                JCTree ftree = found;
                super.scan(node);
                if (found == ftree && sp <= startpos && endpos <= ep) {
                    found = node;
                }
            } else if (sp <= startpos && endpos <= ep) {
                found = node;
                //System.out.println(startpos + " " + endpos + " " + sp + " " + ep + " " + node.getClass());
                super.scan(node);  // Call this to scan child nodes
            } // If the desired range is not within the node's range, we
              // don't even process the children
        }
    }

    /** Finds a node in the AST that minimally includes the given character position range
     * @param tree the compilation unit to search (must have endPositions set)
     * @param startpos the starting character position
     * @param endpos the ending character position
     * @return the node identified
     */
    protected JCTree findNode(JmlCompilationUnit tree, int startpos, int endpos) {
        return finder.find(tree,startpos,endpos);
    }
    
    /** The method on which ESC was run most recently */
    protected MethodSymbol mostRecentProofMethod = null; // FIXME - does this need to be static?
    
    protected BasicProgram mostRecentProgram = null; // FIXME - document
    
    protected IProver mostRecentProver = null; // FIXME
    
    // TODO: document
    public String getCEValue(int pos, int end, String text, String fileLocation) {
        String msg = "Seeking character range " + pos + " to " + end + " in " + fileLocation.toString()
            + "\n";
        fileLocation = fileLocation.replace('\\','/');
        if (mostRecentProofMethod == null) {
            return "No proof in which to evaluate the selection";
        }
        JmlCompilationUnit tree = (JmlCompilationUnit)Enter.instance(context).getEnv((TypeSymbol)mostRecentProofMethod.owner).toplevel;
        if (!tree.sourcefile.getName().replace('\\','/').equals(fileLocation)) {
            //System.out.println("Did not match " + tree.sourcefile.toString());
            boolean found = false;
            {
                JmlCompilationUnit stree = tree.specsCompilationUnit;
                if (stree.sourcefile.getName().replace('\\','/').equals(fileLocation)) {
                    tree = stree;
                    found = true;
                }
                //System.out.println("Did not match " + stree.sourcefile.toString());
            }
            if (!found) {
                System.out.println("No Match for " + tree.specsCompilationUnit.sourcefile.getName());
            }
        }
        JCTree node = findNode(tree,pos,end);
        JmlMethodDecl parentMethod = finder.parentMethod;
        if (parentMethod.sym != mostRecentProofMethod) return "Selected text is not within the method of the most recent proof (which is " + mostRecentProofMethod + ")";
        String out;
        if (node instanceof JmlVariableDecl) {
            // This happens when we have selected a method parameter or the variable within a declaration
            // continue
            out = "Found declaration: " + ((JmlVariableDecl)node).name.toString() + "\n";
        } else {
            if (!(node instanceof JCTree.JCExpression)) return "Selected text is not an expression (" + node.getClass() + "): " + text;
            out = "Found expression node: " + node.toString() + "\n";
        }
        ICounterexample ce = getProofResult(mostRecentProofMethod).counterexample();
        if (ce == null) {
        	out = "There is no counterexample information";
        } else {
        	JCTree logical = mostRecentProgram.toLogicalForm.get(node);
        	if (logical == null) {
        		out = out + "No corresponding logical form";
        	} else {
        		//out = out + "Logical form: " + logical.toString() + "\n";
        		String value = ce.get(logical);
        		if (value == null) value = ce.get(logical.toString());
        		if (value == null) {
        			out = out + "No value found";
        		} else {
        			out = out + "Value: " + value;
        		}
        	}
        }
        return out;
    }
    
    /** Executes static checking on the given method; assumes that all 
     * relevant ASTs have been typechecked
     * @param msym the method to check
     * @return the result of the proof attempt
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public IProverResult doESC(MethodSymbol msym) {
        JmlMethodDecl decl = getJavaDecl(msym);
        JmlEsc esc = JmlEsc.instance(context);
        esc.proveMethod(decl);
        mostRecentProofMethod = msym;
        mostRecentProgram = esc.mostRecentProgram;
        mostRecentProver = esc.mostRecentProver;
        
        return getProofResult(msym);
    }
    
    /** Executes static checking on the methods of the given class; assumes that all 
     * relevant ASTs have been typechecked
     * @param csym the class to check
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public void doESC(ClassSymbol csym) {
        mostRecentProofMethod = null;
        JmlClassDecl decl = getJavaDecl(csym);
        JmlEsc.instance(context).visitClassDef(decl);
    }
    
    /** The proof result of the most recent proof attempt for the given
     * method, or null if there has been none.
     * @param msym the method in question
     * @return the proof result
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable IProverResult getProofResult(MethodSymbol msym) {
        return JmlEsc.instance(context).proverResults.get(msym);
    }
    
    /** Returns the basic block program for the given method
     * @param msym the method in question
     * @return the basic block program, (somewhat) pretty printed
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public String getBasicBlockProgram(MethodSymbol msym) {
        JmlMethodDecl tree = getJavaDecl(msym);
        JmlClassDecl cdecl = getJavaDecl((ClassSymbol)msym.owner);
        BasicProgram program = BasicBlocker.convertToBasicBlocks(context, tree, JmlSpecs.instance(context).getSpecs(msym).cases.deSugared, cdecl);
        return program.write("BASIC BLOCK PROGRAM FOR " + msym.owner.getQualifiedName() + "." + msym.toString() + "\n\n");
    }
    
    /** Adds the given class and all its supertypes (recursively) to the given list.
     * @param csym the class or interface in question
     * @param list the list to add to
     */
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
    
    /** Adds the method and all the methods it overrides (in classes or interfaces)
     * to the given list
     * @param msym the method in question
     * @param list the list to add the methods to
     */
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
    
    /** Returns the type specs for the given class symbol,
     * including all inherited specs
     * 
     * @param sym the class symbol whose specs are wanted
     * @return the specs for that class
     */
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
    
    /** Returns the specs for a given method, including specs of all overridden
     * methods. Note that the names of parameters of various methods may be different,
     * and hence the specs will need some renaming in order to be used together.
     * 
     * @param msym the method symbol whose specs are wanted
     * @return the specs for that method
     */
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
    
    // FIXME - should this be inherited specs; what about parameter name renaming?
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
    
    /** Returns a node factory for the current compilation context.
     * @return a node factory
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull JmlTree.Maker nodeFactory() {
        JmlAttr.instance(context);  // Avoids circular tool registration problems
        return JmlTree.Maker.instance(context);
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
     */ // FIXME - allow the option of showing composite specs?
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
        main.context = null;
        main = null;
    }
    
    //@ public model boolean isOpen; private represents isOpen = main != null;

    /** Creates a JavaFileObject instance from a pseudo filename and given content
     * @param name the name to give the 'file'
     * @param content the content to give the file
     * @return the resulting JavaFileObject
     */ // FIXME - comment on whether the package path is needed
    public JavaFileObject makeJFOfromString(String name, String content) throws Exception {
        return new StringJavaFileObject(name,content);
    }
    
    /** Creates a JavaFileObject instance from a real file, by name
     * @param filepath the path to the file
     * @return the resulting JavaFileObject
     */
    public JavaFileObject makeJFOfromFilename(String filepath) {
        JavacFileManager dfm = (JavacFileManager)context.get(JavaFileManager.class);
        return dfm.getFileForInput(filepath);
    }
    
    /** Creates a JavaFileObject instance from a File object
     * @param file the file to wrap
     * @return the resulting JavaFileObject
     */
    public JavaFileObject makeJFOfromFile(File file) {
        JavacFileManager dfm = (JavacFileManager)context.get(JavaFileManager.class);
        return dfm.getRegularFile(file);
    }
    
    /** This class encapsulates a String as a JavaFileObject, making it a pseudo-file
     */
    protected static class StringJavaFileObject extends SimpleJavaFileObject {
        
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
         * @param content the content of the pseudo file
         * @throws Exception if a URI cannot be created
         */ // FIXME - sort out the package part of the path
        public StringJavaFileObject(/*@ nullable */String filename, /*@ non_null */String content) throws Exception {
            // This takes three slashes because the filename is supposed to be absolute.
            // In our case this is not a real file anyway, so we pretend it is absolute.
            super(filename == null ? uritest : new URI("file:///" + filename),
                    filename == null || filename.endsWith(".java") ? Kind.SOURCE : Kind.OTHER);
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
