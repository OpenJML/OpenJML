package org.jmlspecs.openjml;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;

import javax.tools.DiagnosticListener;
import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.annotation.Pure;
import org.jmlspecs.openjml.API.StringJavaFileObject;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.Main.IProgressReporter;
import org.jmlspecs.openjml.proverinterface.IProverResult;

import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;

public interface IAPI {
    
    /** Returns the string describing the version of OpenJML that is this
     * set of classes.
     * @return the version of this instance of OpenJML
     */
    public @NonNull String version();


    /** The compilation context for this API object */
    //@ ensures \result == context;
    @Pure
    public @Nullable Context context();

    public static abstract class AbstractProgressReporter implements IProgressReporter {
        protected Context context;
        
        public AbstractProgressReporter() {
        }
        
        @Override
        public abstract boolean report(int ticks, int level, String message);

        @Override
        public void setContext(Context context) { this.context = context; }
    }

    /** Sets a progress listener that hears any progress reports (e.g. names of
     * files as they are parsed).  Any previous listener is forgotten (there is
     * just one listener at a time).
     * @param p The listener
     */
    public void setProgressReporter(@Nullable Main.IProgressReporter p);

    /** Executes the command-line version of OpenJML, returning the exit code.
     * All output and diagnostics are written to System.out.
     * @param args the command-line arguments
     * @return the exit code (0 is success; other values are various kinds of errors)
     */
    // FIXME - does compile retain options???
    //@ requires isOpen && args != null && \nonnullarguments(args);
    //@ ensures isOpen;
    public int execute(@NonNull String ... args);
    
    /** Executes the command-line version of OpenJML, returning the exit code.
     * @param writer the PrintWriter to receive general output
     * @param diagListener a listener to receive reports of diagnostics (e.g. parse or typechecking errors and warnings)
     * @param args the command-line arguments
     * @return the exit code (0 is success; other values are various kinds of errors)
     */
    public int execute(@NonNull PrintWriter writer, @Nullable DiagnosticListener<JavaFileObject> diagListener, @NonNull String ... args);
    
    /** Executes the jmldoc tool on the given command-line arguments. */
    public int jmldoc(@NonNull String... args);
    
    /** Enters and typechecks the provided compilation unit ASTs.  The elements
     * of the list should all be JmlCompilationUnit nodes.
     * @param trees a varargs list or an array of the ASTs to be checked
     * @return the number of errors encountered
     * @throws IOException
     */
    public int typecheck(@NonNull JmlCompilationUnit... trees)
            throws IOException;

    /** Enters and typechecks the provided compilation unit ASTs.
     * @param trees a collection of the ASTs to be checked
     * @return the number of errors encountered
     * @throws IOException
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public int typecheck(
            @NonNull Collection<? extends JmlCompilationUnit> trees)
            throws java.io.IOException;

    /** Enters and typechecks the provided compilation unit ASTs.  The elements
     * of the list should all be JmlCompilationUnit nodes.
     * @param list a list of the ASTs to be checked
     * @return the number of errors encountered
     * @throws IOException
     */
    public int typecheck(@NonNull List<JCCompilationUnit> list) throws IOException;
    
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
    public @NonNull java.util.List<JmlCompilationUnit> parseFiles(@NonNull String... filenames);

    public @NonNull java.util.List<JmlCompilationUnit> parseFiles(@NonNull Collection<? extends JavaFileObject> inputs);
    
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
    public @NonNull
    java.util.List<JmlCompilationUnit> parseFiles(
            @NonNull File... files);

    /* (non-Javadoc)
     * @see org.jmlspecs.openjml.IAPI#parseFiles(javax.tools.JavaFileObject)
     */
    //@ requires \nonnullelements(inputs);
    //@ requires isOpen;
    //@ ensures isOpen;
    //@ ensures inputs.length == \result.size();
    //@ ensures (* output elements are non-null *);
    public @NonNull java.util.List<JmlCompilationUnit> parseFiles(@NonNull JavaFileObject... inputs);
    
    /** Produces a parse tree for a single file without any specifications; the
     * file may be either a .java or a specification file.  The trees are not
     * type-checked and do not have any name resolution applied and are not made
     * part of the compilation context.
     * @param file the file to be parsed
     * @return the parse tree for the file
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull
    JmlCompilationUnit parseSingleFile(@NonNull JavaFileObject jfo); // FIXME - check that this works for .jml files

    public @NonNull
    JmlCompilationUnit parseSingleFile(@NonNull File file); // FIXME - check that this works for .jml files

    /** Produces a parse tree for a single file without any specifications; the
     * file may be either a .java or a specification file.  The trees are not
     * type-checked and do not have any name resolution applied and are not made
     * part of the compilation context.
     * @param filename the file to be parsed
     * @return the parse tree for the file
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @NonNull
    JmlCompilationUnit parseSingleFile(@NonNull String filename); // FIXME - check that this works for .jml files

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
    public @NonNull
    JmlCompilationUnit parseString(@NonNull String name,
            @NonNull String content) throws Exception;

    public JCExpression parseExpression(CharSequence text,
            boolean isJML);

    public JCStatement parseStatement(CharSequence text, boolean isJML);

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
    

    /** Parses, creates symbol table symbols and typechecks the given set of files.
     *  This method may be called multiple times to add new classes to the symbol
     *  table entries. However if any file depends on another file B, file B is sought
     *  on the sourcepath or the specspath. Typically those paths are set to include
     *  the files that are listed in the arguments.
     * @param files the set of files to parse and check
     * @throws java.io.IOException
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public void parseAndCheck(File... files)
            throws java.io.IOException;

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
     * parsed and present in the symbol table.
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
    public JmlClassDecl getJavaDecl(ClassSymbol csym);

    /** Returns the declaration (the AST) corresponding to the given
     * method, if there is one.
     * @param msym the method symbol
     * @return the corresponding AST, or null
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable
    JmlMethodDecl getJavaDecl(MethodSymbol msym);

    /** Returns the declaration (the AST) corresponding to the given
     * field, if there is one.
     * @param vsym the field symbol
     * @return the corresponding AST, or null
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable
    JmlVariableDecl getJavaDecl(VarSymbol vsym);

    /** Sets a command-line option to the given value 
     * @param name the option name, including the leading - sign
     * @param value the value to give the option
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public void setOption(String name, String value);

    /** Sets a command-line option to true 
     * @param name the option name, including the leading - sign
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public void setOption(String name);

    /** Removes a command-line option 
     * @param name the option name, including the leading - sign
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public void removeOption(String name);

    /** Gets the value of a command-line option (null if not set)
     * @param name the option name, including the leading - sign
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable
    String getOption(String name);

    // TODO: document
    public String getCEValue(int pos, int end, String text,
            String fileLocation);

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

    /** The proof result of the most recent proof attempt for the given
     * method, or null if there has been none.
     * @param msym the method in question
     * @return the proof result
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public @Nullable
    IProverResult getProofResult(MethodSymbol msym);

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
    public @NonNull
    JmlSpecs.MethodSpecs getSpecs(@NonNull MethodSymbol sym);

    /** Returns the specs for a given method, including specs of all overridden
     * methods. Note that the names of parameters of various methods may be different,
     * and hence the specs will need some renaming in order to be used together.
     * 
     * @param msym the method symbol whose specs are wanted
     * @return the specs for that method
     */
    //@ requires isOpen;
    //@ ensures isOpen;
    public java.util.List<JmlSpecs.MethodSpecs> getAllSpecs(
            @NonNull MethodSymbol msym);

    // FIXME - should this be inherited specs; what about parameter name renaming?
    // FIXME - is this public?
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
    public @NonNull
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
            @NonNull java.util.List<? extends JCTree> astlist,
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