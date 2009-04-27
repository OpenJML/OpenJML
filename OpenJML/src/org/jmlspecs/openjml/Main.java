package org.jmlspecs.openjml;

import java.io.File;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.reflect.Method;
import java.util.ArrayList;

import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;

import org.jmlspecs.annotations.*;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;

import sun.misc.resources.Messages;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlFlow;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.main.CommandLine;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.main.JavaCompiler.CompileState;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JavacMessages;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;

/**
 * This class is the main entry point for the JML tool. It uses the javac
 * compiler, but overrides some of the functionality here in order to register
 * tools for the compiler to use that are extensions with JML functionality of
 * the usual tools. Also the handling of JML-specific options is initialized
 * here.  This class also contains the programmatic API for calling the compiler
 * or for obtaining ASTs.
 */
public class Main extends com.sun.tools.javac.main.Main {

    /** The compilation unit context associated with this instance of Main
     * (for the programmatic API); for the command-line API it is simply 
     * the most recent value of the context, and is used that way in testing. */
    protected Context context;
    
    /** This is a cached copy of the output writer, for use when
     * direct writing is needed (such as printing out help information) before
     * the Log facility is registered.
     */
    //@edu.umd.cs.findbugs.annotations.NonNull
    @NonNull
    protected PrintWriter out;
    
    /**
     * Construct a compiler instance.  Errors go to stderr.
     */
    @edu.umd.cs.findbugs.annotations.SuppressWarnings("NM_SAME_SIMPLE_NAME_AS_SUPERCLASS")
    public Main() {
        this(applicationName, new PrintWriter(System.err, true));
    }

    /**
     * Construct a compiler instance.
     * @param name the name to use for the application
     * @param out  the PrintWriter to which to send information and error messages
     */
    public Main(/*@ non_null */String name, /*@ non_null */PrintWriter out) {
        super(name,out);
        this.out = out;  // FIXME - would not need this if the super class declared out protected
    }

    /** The external entry point - simply calls compiler(args) and exits with the
     * exit code returned.
     * @param args the command-line arguments
     */
    //@ requires args != null && \nonnullelements(args);
    public static void main(String[] args) throws Exception {
        if (args.length > 0 && args[0].equals("-Xjdb")) {
            // Copied directly from com.sun.tools.javac.Main and not tested
            String[] newargs = new String[args.length + 2];
            Class<?> c = Class.forName("com.sun.tools.example.debug.tty.TTY");
            Method method = c.getDeclaredMethod ("main", new Class[] {args.getClass()});
            method.setAccessible(true);
            System.arraycopy(args, 1, newargs, 3, args.length - 1);
            newargs[0] = "-connect";
            newargs[1] = "com.sun.jdi.CommandLineLaunch:options=-esa -ea:com.sun.tools...";
            newargs[2] = "org.jmlspecs.openjml.Main";
            method.invoke(null, new Object[] { newargs });
          } else {
            System.exit(compiler(args));
          }
    }
    
    /** The default application name */
    //@edu.umd.cs.findbugs.annotations.NonNull
    @NonNull
    final public static String applicationName = "jml";
    
    /** The option string for requesting help information */
    //@edu.umd.cs.findbugs.annotations.NonNull
    @NonNull
    final public static String helpOption = "-help";
    
    /** The option string for requesting interactive mode */
    //@edu.umd.cs.findbugs.annotations.NonNull
    @NonNull
    final public static String interactiveOption = "-i";

    /** Invokes the compiler on the given command-line arguments; errors go to
     * stdout.
     * @param args the command-line arguments
     * @return     the exit code, as returned to the shell - 0 is success
     */
    //@ requires args != null && \nonnullelements(args);
    public static int compiler(String[] args) {
        return compiler(args,false);  // The boolean: true - errors to stdErr, false - errors to stdOut
    }

    /** A programmatic interface to the compiler that returns the exit code, but
     * does not itself call System.exit.  [This is called compiler rather than
     * compile as in com.sun.tools.javac.Main because we also have to override
     * com.sun.tools.javac.main.Main.compile ]
     * @param args the command-line arguments
     * @param useStdErr if true, errors go to stderr; if false they go to stdout
     * @return the exit code as sent to the shell (0 is success)
     */ 
    //@ requires args != null && \nonnullelements(args);
    public static int compiler(String[] args, boolean useStdErr) {
        //System.out.println("STARTING");
        int errorcode = 1; //com.sun.tools.javac.main.Main.EXIT_ERROR;
        try {
            if (args == null) {
                Context context = new Context(); // This is a temporary context just for this error message.
                                    // It is not the one used for the options and compilation
                Log log = Log.instance(context);
                JavacMessages.instance(context).add(Utils.messagesJML);
                log.error("jml.main.null.args","org.jmlspecs.openjml.Main.main");
                errorcode = 2; // com.sun.tools.javac.main.Main.EXIT_CMDERR;
            } else {
                // We have to interpret the -useJavaCompiler option before we start
                // the compiler (which does the normal option processing).
                // Since this is rare, we'll require that it be the first
                // option.
                boolean useJavaCompiler = args.length > 0 &&
                        args[0].equals(JmlOptionName.USEJAVACOMPILER.optionName());
                if (useJavaCompiler) {
                    errorcode = com.sun.tools.javac.Main.compile(args);
                } else if (args.length > 0 && args[0].equals(interactiveOption)) {
                    // interactive mode
                    errorcode = new org.jmlspecs.openjml.Interactive().run(args);
                    if (Utils.jmldebug || errorcode != 0) System.out.println("ENDING with exit code " + errorcode); 
                } else {
                    com.sun.tools.javac.main.Main compiler = 
                        new org.jmlspecs.openjml.Main(applicationName, 
                                new PrintWriter(useStdErr ? System.err : System.out, true));
                    errorcode = compiler.compile(args);
                    if (Utils.jmldebug || errorcode != 0) System.out.println("ENDING with exit code " + errorcode);
                }
            }
        } catch (Exception e) {
            // Most exceptions are caught prior to this, so this will happen only for the
            // most catastrophic kinds of failure such as failures to initialize
            // properly.  (You can test this by programmatically throwing an exception in the try
            // block above.)
            Context context = new Context(); // This is a temporary context just for this error message.
                                               // It is not the one used for the options and compilation
            Log log = Log.instance(context);
            JavacMessages.instance(context).add(Utils.messagesJML);
            log.error("jml.toplevel.exception",e);
            e.printStackTrace(System.err);
            errorcode = 3; //com.sun.tools.javac.main.Main.EXIT_SYSERR;
        }
        return errorcode;
    }


    /** This method is overwritten so that the JML compiler can register its
     *  own tools for the various phases.  This fits in just the right place in 
     *  the compiler initialization and invocation sequence, but I'm not sure how
     *  fragile it is with updates and reorganizations of the code.
     *  
     *  @param args the command-line arguments
     *  @param context the compilation context to use
     *  @return the value to use as the command-line exit code
     */
    //@ requires args != null && \nonnullelements(args);
    //@ requires context != null;
    @Override
    public int compile(String[] args, Context context) {
        this.context = context;
        int exit = 0;
        if (args.length == 0) {
            register(context);
            exit = super.compile(args,context);
            helpJML();
        } else {
            register(context);
            // Note that the Java option processing happens in compile below.
            // Those options are not read at the time of the register call,
            // but the register call has to happen before compile is called.
            exit = super.compile(args,context);
            if (Options.instance(context).get(helpOption) != null) {
                helpJML();
            }
        }
//        JmlSpecs specs = JmlSpecs.instance(context); // This is just for debugging
//        specs.printDatabase();
        return exit;
    }
        
    /** This is a utility method to print out all of the JML help information */
    protected void helpJML() {
        out.print(JmlOptionName.helpInfo());
        out.flush();
    }
    
    /** This method scans the input sequence of command-line arguments, 
     * processing any that are recognized as JML options.  Those options
     * are registered in the Options map.  The String[] returned contains
     * all of the command-line arguments in the input, except those recognized
     * as JML options.
     * @param args the input command-line arguments
     * @param options the Options map in which recognized options are recorded
     * @return all arguments not recognized as JML
     */
    //@ requires \nonnullelements(args);
    //@ ensures \result != null && \nonnullelements(\result);
    String[] processJmlArgs(@NonNull String [] args, @NonNull Options options) {
        ArrayList<String> newargs = new ArrayList<String>();
        int i = 0;
        while (i<args.length) {
            i = processJmlArg(args,i,options,newargs);
        }
        return newargs.toArray(new String[newargs.size()]);
    }
    
    /** Processes a single JML command-line option and any arguments.
     * 
     * @param args the full array of command-line arguments
     * @param i    the index of the argument to be processed
     * @param options the options object to be adjusted as JML options are found
     * @param remainingArgs any arguments that are not JML options
     * @return the index of the next argument to be processed
     */
    //@ requires \nonnullelement(args);
    //@ requires (* elements of remainingArgs are non-null *);
    //@ requires 0<= i && i< args.length;
    //@ ensures \result > i;
    int processJmlArg(@NonNull String[] args, int i, @NonNull Options options, @NonNull java.util.List<String> remainingArgs ) {
        String res = "";
        String s = args[i++];
        OptionInterface o = JmlOptionName.find(s);
        if (o == null) {
            int k = s.indexOf('=');
            if (k != -1) {
                o = JmlOptionName.find(s.substring(0,k));
                if (o != null) {
                    res = s.substring(k+1,s.length());
                    if ("false".equals(res)) res = null;
                    else if ("true".equals(res)) res = "";
                    else if (!o.hasArg()) {
                        // FIXME - problem -  ignoring argument
                    }
                }
            }
            if (s.equals(helpOption)) options.put(s,"");
        } else if (o.hasArg()) {
            res = args[i++];
        }
        if (o == null) {
            remainingArgs.add(s);
        } else {
            // An empty string is the value of the option if it takes no arguments
            // That is, for boolean options, "" is true, null is false
            options.put(s,res);
        }
        return i;
    }

    /* We override this method in order to process the JML command-line 
     * arguments and to do any tool-specific initialization
     * after the command-line arguments are processed.  
     */   // FIXME - we are hacking the availability of 'context' here in a non-thread-safe way;
        // but note that Main treats options in a non-thread safe way
    // @edu.umd.cs.findbugs.annotations.SuppressWarnings("ST_WRITE_TO_STATIC_FROM_INSTANCE_METHOD")
    @Override
    public List<File> processArgs(String[] args) {
        Context context = this.context; // At least cache it here at the beginning
        args = processJmlArgs(args,Options.instance(context));
        List<File> files = super.processArgs(args);
        Utils.jmldebug = Options.instance(context).get(JmlOptionName.JMLDEBUG.optionName()) != null; 
        JmlSpecs.instance(context).initializeSpecsPath();
        if (!JmlOptionName.isOption(context,JmlOptionName.NOINTERNALRUNTIME)) {
            JmlSpecs.instance(context).appendRuntime();
        }
        return files;
    }
        
    /** This registers the JML versions of many of the tools (e.g. scanner, parser,
     * specifications database,...) used by the compiler.  They must be registered
     * before the Java versions are invoked, since in most cases singleton
     * values are lazily created.  Note also that since tools can only be registered
     * into the context once, circular dependencies can arise from pairs of tools
     * that use each other, if you are not careful.
     * @param context the compilation context into which to register the tools
     */
    public void register(/*@ non_null @*/ Context context) {
        this.context = context;// A hack so that context is available in processArgs()
        registerTools(context,out);
    }
    
    /** Called to register the JML internal tools that replace the tools used
     * in the Java compiler.
     * @param context the compiler context in which the tools are to be used
     * @param out the PrintWriter used for error and informational messages
     */
    static public void registerTools(/*@ non_null */ Context context, PrintWriter out) {

        // This is done later, but we do it here so that the Log is
        // available if tool registration (or argument processing) needs the
        // Log.  However, note that if the Log is actually instantiated before
        // Java arguments are read, then it is not set consistently with those 
        // options.
        context.put(Log.outKey,out);

        // These have to be first in case there are error messages during 
        // tool registration.
        JavacMessages.instance(context).add(Utils.messagesJML); // registering an additional source of JML-specific error messages

        // These register JML versions of the various tools.  ALL OF THESE MUST
        // REGISTER FACTORIES AND NOT CREATE ACTUAL INSTANCES.  Creating instances
        // will trigger a cascade of tool instance generation, which can create
        // tools (such as the Log) before the Options are processed, and can
        // trigger some circular dependencies in the constructors of the various
        // tools.
        // Any initialization of these tools that needs to be done based on 
        // options should be performed in processArgs() in this method.
        JmlSpecs.preRegister(context); // registering the specifications repository
        JmlParser.JmlFactory.preRegister(context); // registering a Jml-specific factory from which to generate JmlParsers
        JmlScanner.JmlFactory.preRegister(context); // registering a Jml-specific factory from which to generate JmlScanners
        JmlTree.Maker.preRegister(context); // registering a JML-aware factory for generating JmlTree nodes
        JmlCompiler.preRegister(context);
        JmlEnter.preRegister(context);
        JmlResolve.preRegister(context);
        JmlMemberEnter.preRegister(context);
        JmlFlow.preRegister(context);
        JmlAttr.preRegister(context);  // registering a JML-aware type checker
        JmlPretty.preRegister(context);
    }

    /** This is overridden so that serious internal bugs are reported as OpenJML
     * rather than Javac bugs.
     */
    //@Override
    protected void bugMessage(Throwable ex) {
        System.err.println("Internal JML bug - please report.  Build" + JavaCompiler.version());
        ex.printStackTrace(System.out);
    }
    
    
    // EXTERNAL API FOR PROGRAMATIC ACCESS TO JML COMPILER INTERNALS
    // FIXME - pretty printing needs lots of work
    // FIXME - internal classes for holding specs are not yet finalized
    
    /** Creates and initializes a compiler instance for programmatic use
     * @param args the command line arguments that setup options such as 
     * the class path and the location of specification files; any class file
     * names are ignored; annotation processors should be listed here.
     */
    public Main(@NonNull String[] args) throws Exception {
        this();
        initialize(args);
    }
    
    /** The argument is the array of command-line arguments without files - options only.
     * This should not be called by a client, but only internally.
     * 
     * @param args the array of command-line arguments used to setup options
     * 
     */
    protected Main initialize(@NonNull String[] args) throws Exception {
        context = new Context();
        JavacFileManager.preRegister(context); // can't create it until Log has been set up
        setOptions(Options.instance(context));
        filenames = new ListBuffer<File>();
        classnames = new ListBuffer<String>();
        register(context);
        processArgs(CommandLine.parse(args));
        // FIXME - warn about ignored files? or process them?
        return this;
    }
    
    public Context context() {
        return context;
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
    
    /** Produces a parse tree for a single file wihtout any specifications; the
     * file may be either a .java or a specification file.  The trees are not
     * type-checked and do not have any name resolution applied.
     * @param file the file to be parsed
     * @return the parse tree for the file
     */
    public JmlCompilationUnit parseFile(File file) {
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
                classnames.toList());
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
    }
}
