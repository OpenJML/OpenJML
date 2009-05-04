package org.jmlspecs.openjml;

import java.io.File;
import java.io.StringWriter;
import java.util.ArrayList;

import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;

import org.jmlspecs.annotations.NonNull;
import org.jmlspecs.annotations.Nullable;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.main.JavaCompiler.CompileState;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

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
 * There is also a static method, execute, that is a public entry point to the
 * various tools (jml checker, jmldoc, ...) that openjml provides.  It performs 
 * a one-time processing of files, without making the classes and ASTs available,
 * just like a command-line execution would do.
 * 
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
    protected Context context = null;
    
    //@ initially main != null;
    //@ initially context != null;
    
    /** Creates a new compilation context.
     * @param args the command-line options and initial set of files with which
     * to load the compilation environment
     */
    public API(@NonNull String ... args) throws Exception {
        main = new Main(args);
        context = main.context;
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
    //@ ensures files.size() == \result.size();
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
    public JmlCompilationUnit parseSingleFile(File file) {
        JmlCompiler c = (JmlCompiler)JmlCompiler.instance(context);
        c.inSequence = true;
        Iterable<? extends JavaFileObject> fobjects = ((JavacFileManager)context.get(JavaFileManager.class)).getJavaFileObjects(file);
        return ((JmlCompilationUnit)c.parse(fobjects.iterator().next()));
    }
    
    /** Parses, creates symbol table symbols and typechecks the given set of files.
     *  This method may be called multiple times to add new classes to the symbol
     *  table entries.  Other files may be parsed and entered if they are dependencies
     *  of the files given as arguments.
     * @param files the set of files to parse and check
     * @throws java.io.IOException
     */
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
    public @Nullable ClassSymbol getClassSymbol(@NonNull String qualifiedName) {
        Name n = Names.instance(context).fromString(qualifiedName);
        return Symtab.instance(context).classes.get(n);
    }
    
    /** Retrieves the symbol table entry for a given package name, based on files already
     * parsed and present in the symbol table.
     * @param qualifiedName the dot separated package name
     * @return the package symbol or null if it is not found
     */
    public @Nullable PackageSymbol getPackageSymbol(@NonNull String qualifiedName) {
        Name n = Names.instance(context).fromString(qualifiedName);
        return Symtab.instance(context).packages.get(n);
    }
    
    /** Returns the type specs for the given class symbol
     * 
     * @param sym the class symbol whose specs are wanted
     * @return the specs for that class
     */
    public @NonNull TypeSpecs getSpecs(@NonNull ClassSymbol sym) {
        return JmlSpecs.instance(context).get(sym);
    }
    
    /** Returns the specs for a given method
     * 
     * @param sym the method symbol whose specs are wanted
     * @return the specs for that method
     */
    public @NonNull JmlMethodSpecs getSpecs(@NonNull MethodSymbol sym) {
        return JmlSpecs.instance(context).getSpecs(sym);
    }
    
    /** Returns the specs for a given method in denested form
     * 
     * @param sym the method symbol whose specs are wanted
     * @return the specs for that method
     */
    public @NonNull JmlMethodSpecs getDenestedSpecs(@NonNull MethodSymbol sym) {
        return JmlSpecs.instance(context).getDenestedSpecs(sym);
    }
    
    /** Returns the specs for a given field
     * 
     * @param sym the field symbol whose specs are wanted
     * @return the specs for that field
     */
    public @NonNull FieldSpecs getSpecs(@NonNull VarSymbol sym) {
        return JmlSpecs.instance(context).getSpecs(sym);
    }
    // FIXME - what about nested classes?  what separator?
    /** Returns the AST for a given class (not compilation unit)
     * 
     * @param qualifiedName the fully-qualified name of the class whose AST is wanted
     * @return the AST for that class
     */
    public @NonNull JmlClassDecl getClassAST(@NonNull String qualifiedName) {
        ClassSymbol sym = getClassSymbol(qualifiedName);
        TypeSpecs t = getSpecs(sym);
        return t.decl;
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
    public @NonNull String prettyPrint(@NonNull JCTree ast, boolean likeSource) throws Exception {
        StringWriter s = new StringWriter();
        JmlPretty.instance(s,likeSource).print(ast);
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
    public void close() {
        JmlCompiler.instance(context).close();
        context = null;
        main = null;
    }
}
