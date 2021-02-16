package org.jmlspecs.openjml;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.Map;

import javax.tools.DiagnosticListener;
import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.annotation.Pure;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.Main.IProgressListener;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverResult;

import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Options;

public interface IAPI {
     
    //@ public model boolean isOpen; private represents isOpen = main != null;


    /** Returns the string describing the version of OpenJML that is this
     * set of classes.
     * @return the version of this instance of OpenJML
     */
    public @NonNull String version();


    /** The compilation context for this API object */
    //@ ensures \result == context;
    @Pure
    public @Nullable Context context();

    /** The compiler object for this context. */
    @Pure
    public Main main();

    /** A partial (abstract) implementation of a progress listener to hear
     * progress on this API's operations.
     */
    public static abstract class AbstractProgressListener implements IProgressListener {
        protected Context context;
        
        public AbstractProgressListener() {
        }
        
        /** Called by the subscribed object when a diagnostic report is made */
        @Override
        public abstract boolean report(int level, String message);

        // FIXME - can we get rid of this? in the meantime, it must be called to set the context to match that of the compilation context being listened to
        @Override
        public void setContext(Context context) { this.context = context; }
    }
    
    public static interface IProofResultListener {
        
        void reportProofResult(MethodSymbol msym, IProverResult result);
        default IProofResultListener setListener(IProofResultListener listener) { return null; }
    }

    /** Sets a progress listener that hears any progress reports (e.g. names of
     * files as they are parsed).  Any previous listener is forgotten (there is
     * just one listener at a time).
     * @param p The listener
     */
    public void setProgressListener(/*@ nullable */ Main.IProgressListener p);
    
    /** Sets a listener for ESC proof results as they are generated. Any previous
     * listener is returned and forgotten (there is just one listener at a time, 
     * unless they are explicitly chained).
     * @param p the listener
     */
    public IProofResultListener setProofResultListener(@Nullable IProofResultListener p);

    /** This method initializes the Options instance of the current compilation
     * context. If the options argument is not null, its content is used
     * to completely initialize the Options instance; if options is null, then
     * the options are initialized by reading
     * the options specified in the environment (System properties +
     * openjml properties files). Then the specified args are processed to make any 
     * further adjustments to the options. Any errors are reported through the
     * log mechanism. Any non-options in the args list (e.g. files) are 
     * warned about and ignored. 
     * */
    public void initOptions(@Nullable Options options, @NonNull String ... args);
    
    /** Adds additional command-line options to the current context. Any errors
     * are reported through the diagnostics Log.
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public void addOptions(String... args);
    
    /** Adds a custom option (not checked as a legitimate command-line option);
     * may have an argument after a = symbol */
    public void addUncheckedOption(String arg);

    /** Gets the value of a command-line option (null if not set)
     * @param name the option name, including the leading - sign
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable
    String getOption(String name);

    public void abort();
    
    /** Executes the command-line version of OpenJML, in a newly initialized
     * Main, with a new compilation context, returning the exit code.
     * The arguments are used to initialize the options and files just as
     * described for initOptions().
     * @param options an instance of options to use
     * @param args additional command-line arguments and files to process
     * @return the exit code (0 is success; other values are various kinds of errors)
     */
    //@ requires isOpen && args != null && \nonnullarguments(args);
    //@ ensures isOpen;
    public int execute(@Nullable Options options, @NonNull String ... args);
    
    /** Executes the command-line version of OpenJML, in a newly initialized
     * Main, with a new compilation context, returning the exit code.
     * The arguments are used to initialize the options and files just as
     * described for initOptions() and the constructor for Main().
     * @param writer the PrintWriter to receive general output
     * @param diagListener a listener to receive reports of diagnostics (e.g. parse or typechecking errors and warnings)
     * @param args the command-line arguments
     * @return the exit code (0 is success; other values are various kinds of errors)
     */
    public int execute(@NonNull PrintWriter writer, @Nullable DiagnosticListener<JavaFileObject> diagListener, @Nullable Options options, @NonNull String ... args);
    
    /** Executes the jmldoc tool on the given command-line arguments. This is 
     * NOT CURRENTLY IMPLEMENTED and the API may change. */
    public int jmldoc(@NonNull String... args);
    
    /** Does not change the ASTs except to delete all type and name resolution information,
     * so that typecheck() can be run again. This operation might be appropriate if an AST has 
     * been modified, but without complete type information, so that typechecking has to be
     * performed again. Ordinarily, the typecheck() operation does not re-typecheck subtrees
     * that already have a type defined.
     */
    public void clearTypes(Collection<? extends JCCompilationUnit> trees);
    
    /** Returns true if the class has been type-checked */
    public boolean isTypechecked(ClassSymbol csym);
    
    /** Returns true if the class has been type-checked */
    public boolean isTypechecked(String qualifiedName);
    
    /** Enters and typechecks the provided already-parsed compilation unit ASTs.  The elements
     * of the list should all be JmlCompilationUnit nodes. The operation is
     * performed in the current compilation context, wihth currently set options.
     * It may add new compilation units to some already checked, but currently
     * may not check units that have already been checked.
     * @param trees a varargs list or an array of the ASTs to be checked
     * @return the number of errors encountered
     * @throws IOException
     */
    public int typecheck(@NonNull JmlCompilationUnit... trees)
            throws IOException;

    /** Enters and typechecks the provided already-parsed compilation unit ASTs.  The elements
     * of the list should all be JmlCompilationUnit nodes. The operation is
     * performed in the current compilation context, wihth currently set options.
     * It may add new compilation units to some already checked, but currently
     * may not check units that have already been checked.
     * @param trees a collection (java.util.Collection) of the ASTs to be checked
     * @return the number of errors encountered
     * @throws IOException
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public int typecheck(
            @NonNull Collection<? extends JmlCompilationUnit> trees)
            throws java.io.IOException;

    /** Enters and typechecks the provided already-parsed compilation unit ASTs;
     * The elements
     * of the list must all be JmlCompilationUnit nodes (this signature says JCCompilationUnit
     * to be compatible with the JavaCompiler API). The operation is
     * performed in the current compilation context, wihth currently set options.
     * It may add new compilation units to some already checked, but currently
     * may not check units that have already been checked.
     * @param list a list (com.sun.tools.javac.util.List) of the ASTs to be checked
     * @return the number of errors encountered
     * @throws IOException
     */
    public int typecheck(@NonNull List<? extends JCCompilationUnit> list) throws IOException;
    
    /** Parses each java file and its specs returning a list of the ASTs for corresponding
     * java files; the spec files are automatically found according to JML rules; 
     * the ASTs of the spec files are contained in the 
     * JmlCompilationUnit.specsSequence.  Error messages are reported separately
     * through the diagnostic listener;
     * if there are errors, a parse tree may be incomplete.  The trees are not
     * type-checked and do not have any name resolution applied.
     * @param files the names of the input .java or .jml files
     * @return a list of corresponding ASTs
     */
    //@ requires \nonnullelements(files);
    //@ requires isOpen;
    //@ ensures isOpen;
    //@ ensures files.length == \result.size();
    //@ ensures (* output elements are non-null *);
    public /*@ non_null */ 
    java.util.List<JmlCompilationUnit> parseFiles(@NonNull String... filenames);

    /** Parses each java file and its specs returning a list of the ASTs for corresponding
     * java files; the spec files are automatically found according to JML rules; 
     * the ASTs of the spec files are contained in the 
     * JmlCompilationUnit.specsSequence.  Error messages are reported separately
     * through the diagnostic listener;
     * if there are errors, a parse tree may be incomplete.  The trees are not
     * type-checked and do not have any name resolution applied.
     * @param inputs a collection of JavaFileObject objects representing inputs
     * @return a list of corresponding ASTs
     */
    public /*@ non_null */ 
    java.util.List<JmlCompilationUnit> parseFiles(@NonNull Collection<? extends JavaFileObject> inputs);
    
    /** Parses each java file and its specs returning a list of the ASTs for corresponding
     * java files; the spec files are automatically found according to JML rules; 
     * the ASTs of the spec files are contained in the 
     * JmlCompilationUnit.specsSequence.  Error messages are reported separately
     * through the diagnostic listener;
     * if there are errors, a parse tree may be incomplete.  The trees are not
     * type-checked and do not have any name resolution applied.
     * @param files a list of java.io.File inputs
     * @return a list of corresponding ASTs
     */
    //@ requires \nonnullelements(files);
    //@ requires isOpen;
    //@ ensures isOpen;
    //@ ensures files.length == \result.size();
    //@ ensures (* output elements are non-null *);
    public /*@ non_null */
    java.util.List<JmlCompilationUnit> parseFiles(
            @NonNull File... files);

    /** Parses each java file and its specs returning a list of the ASTs for corresponding
     * java files; the spec files are automatically found according to JML rules; 
     * the ASTs of the spec files are contained in the 
     * JmlCompilationUnit.specsSequence.  Error messages are reported separately
     * through the diagnostic listener;
     * if there are errors, a parse tree may be incomplete.  The trees are not
     * type-checked and do not have any name resolution applied.
     * @param inputs an array of JavaFileObject inputs
     * @return a list of corresponding ASTs
     */
    //@ requires \nonnullelements(inputs);
    //@ requires isOpen;
    //@ ensures isOpen;
    //@ ensures inputs.length == \result.size();
    //@ ensures (* output elements are non-null *);
    public /*@ non_null */ java.util.List<JmlCompilationUnit> parseFiles(@NonNull JavaFileObject... inputs);
    
    /** Produces a parse tree for a single file without any specifications; the
     * file may be either a .java or a .jml file.  The trees are not
     * type-checked and do not have any name resolution applied and are not made
     * part of the compilation context.
     * @param file the file to be parsed
     * @return the parse tree for the file
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull
    JmlCompilationUnit parseSingleFile(@NonNull JavaFileObject jfo);

    /** Produces a parse tree for a single file without any specifications; the
     * file may be either a .java or a specification file.  The trees are not
     * type-checked and do not have any name resolution applied and are not made
     * part of the compilation context.
     * @param filename the name of the file to be parsed
     * @return the parse tree for the file
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull
    JmlCompilationUnit parseSingleFile(@NonNull String filename);
    
    /** Produces a parse tree for the given text; the text must represent a
     * compilation unit for a .java file or a specification file.  The name 
     * is the file path to associate with the text and must include directories
     * corresponding to the purported package holding the java class.  The trees are not
     * type-checked and do not have any name resolution applied and are not made
     * part of the compilation context.
     * @param name the filename to associate with the text
     * @param content the textual content to parse
     * @return the parse tree for the file
     */
    // FIXME - resolve whether the package name must be present
    // TODO: Would like to automatically set the filename, but can't since the
    // JavaFileObject has to be created before parsing and it is immutable
    //@ requires name.length() > 0;
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull
    JmlCompilationUnit parseString(@NonNull String name,
            @NonNull String content) throws Exception;

    /** Parse input text as a Java/JML expression; the isJML parameter must
     * be true if the expression contains JML constructs; it is false if the
     * expression is a Java expression considered to be outside a JML
     * annotation.
     */
    public JCExpression parseExpression(CharSequence text,
            boolean isJML);

    /** Parse input text as a Java/JML statement; the isJML parameter must
     * be true if the expression contains JML constructs; it is false if the
     * expression is a Java expression considered to be outside a JML
     * annotation.
     */
    public JCStatement parseStatement(CharSequence text, boolean isJML);

    /** Parses, creates symbol table symbols and typechecks the given set of files.
     *  This method may be called multiple times to add new classes to the symbol
     *  table entries. However if any file depends on another file B, file B is sought
     *  on the sourcepath or the specspath. Typically those paths are set to include
     *  the files that are listed in the arguments.
     * @param files the set of files to parse and check (including referenced files)
     * @throws java.io.IOException
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public void parseAndCheck(File... files)
            throws java.io.IOException;


    /** Finds the source object, if any, corresponding to the specifications
     * for the input Java AST, according to the JML language rules. The result 
     * may be the same input file that resulted in the given compilation unit,
     * if the specs are in the java file itself and not in a .jml file.
     * @param jmlcu a Java source AST (not a specification AST)
     * @return the file object of the specifications
     */
    public @Nullable
    JavaFileObject findSpecs(JmlCompilationUnit jmlcu);

    /** Attaches specifications to a Java source AST. The second argument may
     * be identical to the first, in which case the JML annotations directly in
     * Java source AST are used as the specifications for the Java class. If the
     * second argument is different, annotations in the Java AST are ignored and
     * those in the specified specsSource AST are used instead. 
     * @param javaSource the Java source
     * @param specsSource the specifications AST to attach to the Java source. 
     */ // TODO: instead of or in addition to any existing specs?
    public void attachSpecs(JmlCompilationUnit javaSource, @Nullable JmlCompilationUnit specsSource);
    
    /** Creates a JavaFileObject instance from a pseudo filename and given content
     * @param name the name to give the 'file'
     * @param content the content to give the file
     * @return the resulting JavaFileObject
     */ // FIXME - comment on whether the package path is needed
    public JavaFileObject makeJFOfromString(String name, String content) throws Exception;
    
    /** Creates a JavaFileObject instance from a real file, by name
     * @param filepath the path to the file, either absolute or relative to the current working directory
     * @return the resulting JavaFileObject
     */
    public JavaFileObject makeJFOfromFilename(String filepath);
    
    /** Creates a JavaFileObject instance from a File object
     * @param file the file to wrap
     * @return the resulting JavaFileObject
     */
    public JavaFileObject makeJFOfromFile(File file);
    

    /** Retrieves the symbol table entry for a given package name, based on files already
     * parsed and present in the symbol table.
     * @param qualifiedName the dot separated package name
     * @return the package symbol or null if it is not found
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable
    PackageSymbol getPackageSymbol(@NonNull String qualifiedName);

    /** Retrieves the symbol table entry for a given Class name, based on files already
     * parsed and present in the symbol table; value is not usaable unless
     * isTypechecked(qualifiedName) is true.
     * @param qualifiedName the dot and dollar (for nested classes) separated 
     * class name
     * @return the class symbol or null if it is not found
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable
    ClassSymbol getClassSymbol(@NonNull String qualifiedName);

    /** Retrieves the symbol table entry for a given class name as a member
     * of the given class, based on files already
     * parsed and present in the symbol table.
     * @param csym the owning class
     * @param name the (simple) name of the nested class
     * @return the class symbol or null if it is not found
     */
    public @Nullable
    ClassSymbol getClassSymbol(@NonNull ClassSymbol csym,
            @NonNull String name);

    /** Retrieves the symbol table entry for a given method name as a member
     * of the given class, based on files already
     * parsed and present in the symbol table.
     * @param csym the owning class
     * @param name the (simple) name of the method
     * @return the method symbol or null if it is not found
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable
    MethodSymbol getMethodSymbol(@NonNull ClassSymbol csym,
            @NonNull String name); // FIXME - need a way to handle multiple methods with the same name

    /** Retrieves the symbol table entry for a given variable name as a member
     * of the given class, based on files already
     * parsed and present in the symbol table.
     * @param csym the owning class
     * @param name the (simple) name of the variable
     * @return the variable symbol or null if it is not found
     */
    public @Nullable
    VarSymbol getVarSymbol(@NonNull ClassSymbol csym,
            @NonNull String name);

    /** Returns the symbol for a class declaration (if type checked)
     * @param decl the type-checked ast node
     * @return the corresponding symbol
     */
    public @Nullable
    ClassSymbol getSymbol(@NonNull JmlClassDecl decl);

    /** Returns the symbol for a method declaration (if type checked)
     * @param decl the type-checked ast node
     * @return the corresponding symbol
     */
    public @Nullable
    MethodSymbol getSymbol(@NonNull JmlMethodDecl decl);

    /** Returns the symbol for a variable declaration (if type checked)
     * @param decl the type-checked ast node
     * @return the corresponding symbol
     */
    public @Nullable
    VarSymbol getSymbol(@NonNull JmlVariableDecl decl);

    /** Returns the AST for a given class (not compilation unit)
     * 
     * @param qualifiedName the fully-qualified name of the class whose AST is wanted
     * @return the AST for that class
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull
    JmlClassDecl getClassDecl(@NonNull String qualifiedName);

    /** Returns the declaration (the AST) corresponding to the given
     * class, if there is one.
     * @param csym the class symbol
     * @return the corresponding AST, or null
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public JmlClassDecl getClassDecl(ClassSymbol csym);

    /** Returns the declaration (the AST) corresponding to the given
     * method, if there is one.
     * @param msym the method symbol
     * @return the corresponding AST, or null
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable
    JmlMethodDecl getMethodDecl(MethodSymbol msym);

    /** Returns the declaration (the AST) corresponding to the given
     * field, if there is one.
     * @param vsym the field symbol
     * @return the corresponding AST, or null
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable
    JmlVariableDecl getVarDecl(VarSymbol vsym);

    // TODO: document
    public String getCEValue(int pos, int end, String text,
            String fileLocation);

    public API.Finder findMethod(JmlCompilationUnit tree, int pos, int end, String text,
            String fileLocation);

    // FIXME _ need a way to determine if a CU has been typechecked (successfully)
    
    /** Executes static checking on the given method; assumes that all 
     * relevant ASTs have been typechecked (both the argument and any
     * methods that it references by direct calls or in its specs)
     * @param msym the method to check
     * @return the result of the proof attempt
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public IProverResult doESC(MethodSymbol msym);

    /** Executes static checking on the methods of the given class; assumes that all 
     * relevant ASTs have been typechecked
     * @param csym the class to check
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public void doESC(ClassSymbol csym);

//    /** The proof result of the most recent proof attempt for the given
//     * method, or null if there has been none.
//     * @param msym the method in question
//     * @return the proof result
//     */
//    //@ requires isOpen;
//    //@ ensures isOpen;
//    public @Nullable
//    IProverResult getProofResult(MethodSymbol msym);
//
//    public @Nullable Map<MethodSymbol,IProverResult> getProofResults();

    /** Returns the type specs for the given class symbol
     * 
     * @param sym the class symbol whose specs are wanted
     * @return the specs for that class
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull
    TypeSpecs getSpecs(@NonNull ClassSymbol sym);

    /** Returns the type specs for the given class symbol,
     * including all inherited specs
     * 
     * @param sym the class symbol whose specs are wanted
     * @return the specs for that class
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public java.util.List<TypeSpecs> getAllSpecs(
            @NonNull ClassSymbol sym);

    /** Returns the specs for a given method
     * 
     * @param sym the method symbol whose specs are wanted
     * @return the specs for that method
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public /*@ non_null */
    JmlSpecs.MethodSpecs getSpecs(@NonNull MethodSymbol sym);

    /** Returns the specs for a given method, including specs of all overridden
     * methods. Note that the names of parameters of various methods may be different,
     * and hence the specs will need some renaming in order to be used together.
     * 
     * @param msym the method symbol whose specs are wanted
     * @return the list of specs for that method
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public java.util.List<JmlSpecs.MethodSpecs> getAllSpecs(
            @NonNull MethodSymbol msym);

    // FIXME - should this be inherited specs; what about parameter name renaming?
    /** Returns the specs for a given method in denested form
     * 
     * @param sym the method symbol whose specs are wanted
     * @return the specs for that method
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull
    JmlMethodSpecs getDenestedSpecs(@NonNull MethodSymbol sym);

    /** Returns the specs for a given field
     * 
     * @param sym the field symbol whose specs are wanted
     * @return the specs for that field
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull
    FieldSpecs getSpecs(@NonNull VarSymbol sym);

    /** Returns a node factory for the current compilation context.
     * @return a node factory
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public /*@ non_null */
    JmlTree.Maker nodeFactory();

    /** Prints out a given parse tree (or subtree).
     * 
     * @param ast the ast to print
     * @return a string containing the output
     * @throws Exception
     */
    // FIXME - allow the option of showing composite specs?
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull
    String prettyPrint(@NonNull JCTree ast)
            throws java.io.IOException;

    // FIXME - clarify the difference between the above and below call, and what prettyPrint of lists does.
    /** Prints out a given parse tree (or subtree), attempting to render
     * the JML as compilable source.
     * 
     * @param ast the ast to print
     * @return a string containing the output
     * @throws Exception
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull
    String prettyPrintJML(@NonNull JCTree ast)
            throws java.io.IOException;

    /** Prints out a list of parse trees, separated by the given separator String.
     * 
     * @param astlist a list of asts to print
     * @param sep  a String that is written out as a separator
     * @return a string containing the output
     * @throws Exception
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull
    String prettyPrint(
            /*@ non_null */ java.util.List<? extends JCTree> astlist,
            @NonNull String sep) throws java.io.IOException;

    /** Closes this instance of the compiler, releasing internal memory;
     * no further use of the instance is permitted (and will likely result in
     * exceptions thrown).
     */
    //@ requires isOpen;
    //@ assignable isOpen;
    //@ ensures !isOpen;
    public void close();

}