/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */

package org.jmlspecs.openjml;

import static com.sun.tools.javac.main.Option.WERROR;

import org.openjml.IAPI;

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.lang.reflect.Method;

import javax.tools.DiagnosticListener;
import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;

import org.openjml.*;

import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.*;
import com.sun.tools.javac.comp.*;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.main.Arguments;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.main.JmlCompiler;
import com.sun.tools.javac.parser.JmlFactory;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.resources.CompilerProperties.Errors; // Generated from .properties files
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JavacMessages;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;

/**
 * This class is the main entry point for the JML tool.
 */
public class Main extends com.sun.tools.javac.main.Main {

    /** This is a PrintWriter that prodcues no output */
    public static class NullPrintWriter extends java.io.PrintWriter {
        public NullPrintWriter() { super(System.out); }
        public void println() {}
        public void write(char[] buf, int off, int len) {}
        public void write(String s, int off, int len) {}
        public void write(int c) {}
    }

    /** Holds the value of an environment variable that is the path to
     *  the installation directory for openjml. In a release installation,
     *  install, solvers are the same (as of this writing). and specs is install/specs
     *  In a development environment, they are different -- OPENJML_INSTALL is the OpenJMLsrc folder, holding openjml, openjml-java etc.
     */
    public static final String install = System.getenv("OPENJML_INSTALL");
    /** Absolute path to the folder that holds the library specifications */
    public static final String specs = (System.getenv("OPENJML_SPECS") != null ? System.getenv("OPENJML_SPECS") : System.getenv("OPENJML_INSTALL") + "/specs");
    /** Absolute path to the folder holding Solvers-macos, etc. */
    public static final String solvers = System.getenv("OPENJML_SOLVERS") != null ? System.getenv("OPENJML_SOLVERS") : System.getenv("OPENJML_INSTALL");

    /** An additional exit code, along with those in the super class */
    public static final int EXIT_CANCELED = -1;

    /** The compilation unit context associated with this instance of Main
     * (for the programmatic API); for the command-line API it is simply 
     * the most recent value of the context, and is used that way in testing. 
     * This value cannot be changed after initialize() is called.
     */
    private Context context;

    //@ non_null
    public org.openjml.MockFiles mockFiles = new org.openjml.MockFiles();

    /** True if compilation/static-checking has been canceled, by setting this field in some exception handler. 
     *  Used in an interactive environment. */
    public volatile boolean canceled = false;

    /** Instances of this class are used to abruptly terminate long-running JML operations;
     *  catch clauses typically set the Main.canceled field
     */
    public static class JmlCanceledException extends RuntimeException {
        private static final long serialVersionUID = 1L;
        public JmlCanceledException(String message) {
            super(message);
        }
    }


    /** This listener is notified of progress messages.
     * Currently only one listener is allowed at a time.
     * Some listener is required; initialized to one that emits nothing
     */
    /*@ non_null*/ 
    public IAPI.IProgressListener progressListener  = new PrintProgressReporter(new NullPrintWriter());


    /** This class is a progress listener that prints the progress messages to 
     * a given OutputStream.
     */
    public static class PrintProgressReporter implements IAPI.IProgressListener {
        protected PrintWriter pw;
        protected int verbosity;

        public PrintProgressReporter(OutputStream out) {
            pw = new PrintWriter(out);
        }

        public PrintProgressReporter(PrintWriter w) {
            pw = w != null ? w : new PrintWriter(System.out);
        }

        /** Returns true if there has been a cancellation request */
        @Override
        public boolean report(int level, String message) {
            if (level <= verbosity) {
                pw.println(message);
                pw.flush();
            }
            return false;
        }

        @Override
        public void worked(int ticks) {}

        @Override
        public void setVerbose(int verbosity) { this.verbosity = verbosity; }
    }

    /**
     * Construct a compiler instance; all options are set to values read from
     * the environment.  
     * All output goes to stderr.
     */
    public Main() throws java.io.IOException {
        this(Strings.applicationName, new PrintWriter(System.err, true));
    }

    /** Construct a compiler instance, with designated output writers */
    public Main(/*@ non_null */String applicationName, 
            /*@ non_null */PrintWriter out, /*@ non_null */PrintWriter err) 
                    throws java.io.IOException {
        super(applicationName,out,err);
    }

    /** Construct a compiler instance, with designated output writer */
    public Main(/*@ non_null */String applicationName, 
            /*@ non_null */PrintWriter out) throws java.io.IOException {
        super(applicationName,out,out);
    }

    /** The key for storing this instance in the context */
    public static Context.Key<Main> key = new Context.Key<Main>();

    /** Returns the singleton instance of Main for the given context */
    public static Main instance(Context context) {
        return context.get(key);
    }

    /** Returns a reference to the compilation context. */
    public /*@nullable*/ Context context() {
        return this.context;
    }

    /** Creates a Context, initializes fields and registers (factories for) all the JML toolchain components */
    public Context initialize(
            /*@ nullable*/ DiagnosticListener<? extends JavaFileObject> diagListener) {

        Context context = new Context(); // creates a new Context for this compilation
        context.put(key, this);
        progressListener = new PrintProgressReporter(out());

        // Put this early so any early diagnostics are sent to the listener
        if (diagListener != null) context.put(DiagnosticListener.class, diagListener);
        register(context, stdOut);

        // Now fetch option values from global properties and env. variables
        JmlOptions.setOptionsFromProperties(Utils.findProperties(context), context);
        this.context = context;
        return context;
    }

    /** Returns the stdout PrintWriter */
    public PrintWriter out() {
        return stdOut;
    }

    /** The external entry point - simply calls execute(args) and exits with the
     * exit code returned.
     * @param args the command-line arguments
     */
    //@ requires args != null && \nonnullelements(args);
    public static void main(String... args) {
        if (args.length > 0 && args[0].equals("-Xjdb")) {
            // This branch connects a debugger
            try {
                // Note TODO: Copied directly from com.sun.tools.javac.Main and not tested
                String[] newargs = new String[args.length + 2];
                Class<?> c = Class.forName("com.sun.tools.example.debug.tty.TTY");
                Method method = c.getDeclaredMethod ("main", new Class<?>[] {args.getClass()});
                method.setAccessible(true);
                System.arraycopy(args, 1, newargs, 3, args.length - 1);
                newargs[0] = "-connect";
                newargs[1] = "com.sun.jdi.CommandLineLaunch:options=-esa -ea:com.sun.tools...";
                newargs[2] = "org.jmlspecs.openjml.Main";
                method.invoke(null, new Object[] { newargs });
            } catch (Exception e) {
                System.out.println("Main exiting with exception");
                e.printStackTrace(System.out);
                System.exit(Result.SYSERR.exitCode);
            }
        } else {
            System.exit(execute(args, false));  // The boolean: true - errors to stdErr, false - errors to stdOut
        }
    }

    /** Invokes the compiler on the given command-line arguments; errors go to stdout.
     * @param args the command-line arguments
     * @return     the exit code, as returned to the shell - 0 is success
     */
    //@ requires args != null && \nonnullelements(args);
    public static int execute(String... args) {
        return execute(args,false);  // The boolean: true - errors to stdErr, false - errors to stdOut
    }

    /** Invokes the compiler on the given command-line arguments; all output goes to the given PrintWriter */
    public static int execute(PrintWriter pw, String... args) {
        return execute(pw, null, null, args);
    }

    /** A programmatic interface to the compiler that returns the exit code, but
     * does not itself call System.exit.  [This is called execute rather than
     * compile as in com.sun.tools.javac.Main because we also have to override
     * com.sun.tools.javac.main.Main.compile ]
     * @param args the command-line arguments
     * @param useStdErr if true, errors go to stderr; if false they go to stdout
     * @return the exit code as sent to the shell (0 is success)
     */ 
    //@ requires args != null && \nonnullelements(args);
    public static int execute(String[] args, boolean useStdErr) {
        if (args != null) {
            for (String a: args) {
                if (Strings.jmldocOption.equals(a)) {
                    return 4; // FIXME  - org.jmlspecs.openjml.jmldoc.Main.execute(args);
                }
            }
        }
        return execute(new PrintWriter(useStdErr ? System.err : System.out, true), null, null, args);
    }

    /** Static method to do the work of Main.
     * 
     * @param writer where to write output that is not sent to the diagnosticListener
     * @param diagListener a listener to hear any compiler diagnostics produced
     * @param options the default set of options to use (including system properties)
     * @param args the command-line arguments
     * @return the exit code
     */
    public static int execute(/*@ non_null*/ PrintWriter writer, /*@ nullable*/ DiagnosticListener<? extends JavaFileObject> diagListener, /*@nullable*/ Options options, /*@non_null*/ String[] args) {
        JavaCompiler.versionRBName = "org.jmlspecs.openjml.version"; // Version string is read from version.properties
        int errorcode = com.sun.tools.javac.main.Main.Result.ERROR.exitCode; // 1
        try {
            if (args == null) {
                uninitializedLog().error("jml.main.null.args","org.jmlspecs.openjml.Main.main");
                errorcode = com.sun.tools.javac.main.Main.Result.CMDERR.exitCode; // 2
            } else {
                // We have to interpret the -java option before we start
                // the compiler (which does the normal option processing).
                // Since this is rare, we'll require that it be the first
                // option.
                boolean useJavaCompiler = args.length > 0 &&
                        args[0].equals(JmlOption.USEJAVACOMPILER.optionName());
                if (useJavaCompiler) {
                    String[] newargs = new String[args.length-1];
                    System.arraycopy(args,1,newargs,0,newargs.length);
                    // Pure java compile -- ignores the options, writer, diagListener parameters
                    Utils.setNoJML(true);
                    errorcode = com.sun.tools.javac.Main.compile(newargs);
                } else {
                    // We create an instance of main through which to call the
                    // actual compile method. Note though that the compile method
                    // does its own initialization (in the super class). Thus the
                    // context and any option processing in the constructor call
                    // are thrown away. That is also why we do the hack of saving
                    // the options to a private variable, just to be able to
                    // apply them in the compile() call below.
                    Main compiler = new Main(Strings.applicationName, writer);
                    Context context = compiler.initialize(diagListener);

                    // MAINTENANCE: This section copied from the super class, so we can use the context just created
                    Result result = compiler.compile(args, context);
                    try {
                        // A fresh context was created above, so the file manager can be safely closed:
                        JavaFileManager fileManager = context.get(JavaFileManager.class);
                        if (fileManager != null)
                            fileManager.close();
                    } catch (IOException ex) {
                        compiler.bugMessage(ex);
                    }

                    errorcode = result.exitCode;
                    if (JmlOption.VERBOSENESS.getInt(context) >= Utils.JMLVERBOSE || Options.instance(context).isSet("-verbose")) {
                        writer.println("ENDING with exit code " + errorcode);
                    }
                    compiler.close();
                }
            }
        } catch (JmlCanceledException e) {
            // Error message already issued
            errorcode = Result.CMDERR.exitCode; // FIXME - why not Result.CANCELLED
        } catch (Exception e) {
            // Most exceptions are caught prior to this, so this will happen only for the
            // most catastrophic kinds of failure such as failures to initialize
            // properly.  (You can test this by programmatically throwing an exception in the try
            // block above.)
            uninitializedLog().error("jml.toplevel.exception",e);
            e.printStackTrace(System.err);
            errorcode = com.sun.tools.javac.main.Main.Result.SYSERR.exitCode; // 3
        } finally {
            writer.flush();
        }
        return errorcode;
    }

//    // TODO - needs review when API and Eclipse plugin are fixed
//    /** Executes the given command-line, but within the same instance of Main;
//     * the instance of Main is completely reinitialized, with a new context.
//     * @param writer
//     * @param diagListener
//     * @param options
//     * @param args
//     * @return
//     */
//    public int executeNS(/*@non_null*/ PrintWriter writer, /*@nullable*/ DiagnosticListener<? extends JavaFileObject> diagListener, /*@nullable*/ Options options, /*@non_null*/ String[] args) {
//        int errorcode = com.sun.tools.javac.main.Main.Result.ERROR.exitCode; // 1
//        try {
//            if (args == null) {
//                uninitializedLog().error("jml.main.null.args","org.jmlspecs.openjml.Main.main");
//                errorcode = com.sun.tools.javac.main.Main.Result.CMDERR.exitCode; // 2
//            } else {
//                // We create an instance of main through which to call the
//                // actual compile method. Note though that the compile method
//                // does its own initialization (in the super class). Thus the
//                // context and any option processing in the constructor call
//                // are thrown away. That is also why we do the hack of saving
//                // the options to a private variable, just to be able to
//                // apply them in the compile() call below.
//                initialize(diagListener);
//                // The following line does an end-to-end compile, in a fresh context
//                errorcode = compile(args).exitCode; // context and new options are created in here
//                if (errorcode > Result.CMDERR.exitCode || 
//                        Utils.instance(context()).jmlverbose > Utils.PROGRESS) {
//                    writer.println("ENDING with exit code " + errorcode); // TODO - not sure we want this - but we'll need to change the tests
//                }
//            }
//        } catch (JmlCanceledException e) {
//            // Error message already issued
//            errorcode = EXIT_CANCELED; // Indicates being cancelled
//        } catch (Exception e) {
//            // Most exceptions are caught prior to this, so this will happen only for the
//            // most catastrophic kinds of failure such as failures to initialize
//            // properly.  (You can test this by programmatically throwing an exception in the try
//            // block above.)
//            uninitializedLog().error("jml.toplevel.exception",e);
//            e.printStackTrace(System.err);
//            errorcode = com.sun.tools.javac.main.Main.Result.SYSERR.exitCode; // 3
//        }
//        return errorcode;
//    }

    private IAPI.IProofResultListener prl;

//    // TODO - needs review when API and Eclipse plugin are fixed
//    public int executeNS(/*@non_null*/ PrintWriter writer, /*@nullable*/ DiagnosticListener<? extends JavaFileObject> diagListener, IAPI.IProofResultListener prListener, /*@nullable*/ Options options, /*@non_null*/ String[] args) {
//        int errorcode = com.sun.tools.javac.main.Main.Result.ERROR.exitCode; // 1
//        try {
//            if (args == null) {
//                uninitializedLog().error("jml.main.null.args","org.jmlspecs.openjml.Main.main");
//                errorcode = com.sun.tools.javac.main.Main.Result.CMDERR.exitCode; // 2
//            } else {
//                // We create an instance of main through which to call the
//                // actual compile method. Note though that the compile method
//                // does its own initialization (in the super class). Thus the
//                // context and any option processing in the constructor call
//                // are thrown away. That is also why we do the hack of saving
//                // the options to a private variable, just to be able to
//                // apply them in the compile() call below.
//                initialize(diagListener);
//                setProofResultListener(prListener);  // FIXME - this is wiped away in the compile() below, along with the initialization just above???
//                prl = prListener;                    // FIXME - necessitating this end run with prl
//
//                // The following lines do an end-to-end compile, in a fresh context
//                errorcode = compile(args).exitCode; // context and new options are created in here
//                if (errorcode > Result.CMDERR.exitCode || 
//                        Utils.instance(context()).jmlverbose > Utils.PROGRESS) {
//                    writer.println("ENDING with exit code " + errorcode); // TODO - not sure we want this - but we'll need to change the tests
//                }
//            }
//        } catch (JmlCanceledException e) {
//            // Error message already issued
//            errorcode = EXIT_CANCELED; // Indicates being cancelled
//        } catch (Exception e) {
//            // Most exceptions are caught prior to this, so this will happen only for the
//            // most catastrophic kinds of failure such as failures to initialize
//            // properly.  (You can test this by programmatically throwing an exception in the try
//            // block above.)
//            uninitializedLog().error("jml.toplevel.exception",e);
//            e.printStackTrace(System.err);
//            errorcode = com.sun.tools.javac.main.Main.Result.SYSERR.exitCode; // 3
//        }
//        return errorcode;
//    }

    /** This is a convenience method to initialize just enough that we can log
     * an error or warning message for issues that arise before the compiler
     * is properly initialized.
     * @return a Log instance to use
     */
    static protected Log uninitializedLog() {
        // This is a temporary context just for logging error messages when
        // overall initialization fails.
        // It is not the one used for the compilation
        // It does use Options: checks whether rawDIagnostics is set and sets the diagFormatter correspondingly 
        Context context = new Context();
        JavacMessages.instance(context).add(Strings.messagesJML);
        return Log.instance(context);
    }

    /** This method is overridden so that the JML compiler can register its
     *  own tools for the various phases. The Context argument is required in order
     *  to override the parent class methods, but the value for 'context' must be 
     *  the same as 'this.context', if this.context is already set.
     */
    @Override
    public Main.Result compile(String[] args, Context context) {
        this.context = context;

        // FIXME setProofResultListener(prl);
        boolean hasArgs = args.length != 0;
        args = JmlOptions.instance(context).processJmlArgs(args, Options.instance(context), null);
        // args is now the original 'args' without JML arguments -- leaving  any Java options and files
        if (JmlOptions.instance(context).get("-?") != null) return Result.OK; // Help output is already written
        if (args.length == 0) {
            if (hasArgs) {
                Log.instance(context).error(Errors.NoSourceFiles);
                return Result.CMDERR;
            } else {
                JmlOptions.instance(context).allHelp(false);
                return Result.CMDERR;
            }
        }

        // Note that the Java option processing happens in compile method call below.
        // All the JML tool registration has to happen before compile is called (which should have happened in initialize()).
        canceled = false;
 
        // This is the method that spawns all the work
        // 'args' must contain just Java options and filepaths; JML options have been processed above
        // The exit result will be Result.OK if there are no outright errors
        // If there are just warnings and verification failures, this super call will give Result.OK
        Main.Result exit;
        try {
            exit = super.compile(args, context);
        } catch (JmlCanceledException e) {
            // Cancel fired between methods: JmlCanceledException escaped check() via rethrow.
            return Result.CANCELLED;
        }
        // Cancel fired mid-method: PropagatedException was caught inside check(), which set
        // canceled=true and returned normally; super.compile() completed, but the run was aborted.
        if (canceled) return Result.CANCELLED;

        // Adjust the javac output to include verification failures, and adjust the exit code as well
        int numVerifyWarnings = Utils.instance(context).verifyWarnings;
        //System.out.println("EXITCODE " + numVerifyWarnings + " " + exit.exitCode + " " + JmlOption.EXITVERIFY.value(context) + " " + JmlOption.EXITVERIFY.getInt(context));
        if (numVerifyWarnings != 0) {
            // FIXME - why this guard
            if (!log.hasDiagnosticListener()) JavaCompiler.instance(context).printCount("verify", numVerifyWarnings);
            if (exit.exitCode == 0) {
                // Use the verification failure exit code if there are verification warnings
                // Note: If -Werror is present and there are no warnings and there are verification failures
                // the output will still be Result.VERIFY, not Result.ERROR
                exit = Result.VERIFY;
                try {
                    int z = JmlOption.EXITVERIFY.getInt(context); // User specified exit code for verification failures
                    for (Result x: Result.values()) { if (x.exitCode == z) { exit = x; break; }}
                    if (exit.exitCode != z) throw new RuntimeException();
                } catch (Exception e) {
                    // Invalid values are checked when the command-line is parsed, or when addOptions is called.
                    // So this defensive code is only called if something in the body of openjml sets the option without
                    // calling EXITVERIFY.check()
                    Utils.instance(context).error("jml.message","Invalid value for " + JmlOption.EXITVERIFY + ": " + JmlOption.EXITVERIFY.value(context));
                    exit = Result.CMDERR;
                }
            }
        }
        return exit;
    }

    /** Called programmatically (e.g. from test suites) with URI-keyed mock file
     * interception via {@link org.openjml.MockAwareFileManager}.
     * The set of source files to process must appear in {@code args} as usual;
     * {@code mockFiles} provides in-memory content keyed by URI so that test or
     * dirty (unsaved) files can be type-checked without writing to disk.
     * Pass {@code null} if there are no dirty files. */
    public Main.Result compile(String[] args, org.openjml.MockFiles mockFiles)  {
        try {
            this.mockFiles = (mockFiles != null) ? mockFiles : new org.openjml.MockFiles();
            if (args.length == 0) args = new String[]{"-g"}; // Avoids exiting with help info when there are no arguments
            return compile(args, context());
        } catch (JmlInternalAbort e) {
            log.error("jml.message", "Unrecoverable compilation problem");
            if (System.getenv("STACK") != null) e.printStackTrace(System.out);
            return Main.Result.CMDERR;
        } finally {
            this.mockFiles = new org.openjml.MockFiles();
        }
    }

    /** Do anything that needs adjustment after options are processed but
     * before compilation actually begins. Note that for standard command-line use 
     * the Javac classes do not need any resetting, but the API allows setting or
     * resetting options in multiple calls, so any cached option values will
     * need to be reset.
     */
    // FIXME -- resolve the use of Check.resetHandlers -- it sets lint options incorrectly in normal use
    public void postOptionProcessing() {
        JmlOptions.instance(context).setupOptions();

         // Only implemented for the simple compile policy
        Options.instance(context).put("compilePolicy", "simple");
        JmlCompiler.instance(context).compilePolicy = com.sun.tools.javac.main.JavaCompiler.CompilePolicy.SIMPLE;

        // Handlers are created during tool registration, which in OpenJML has to be before
        // options are read. In some cases the tools cache values of options.
        // So they have to be adjusted for the actual values of the options.
        Check.instance(context).resetHandlers(); // Caches values of lint settings // Instantiates JmlCompiler
        ClassFinder.instance(context).resetOptions(context); // Caches verbose, -Xprefer and others

        if (Utils.debug("options")) JmlOptions.instance(context).dumpOptions();
    }

    /** This registers the JML versions of many of the tools (e.g. scanner, parser,
     * specifications database,...) used by the compiler.  They must be registered
     * before the Java versions are invoked, since in most cases singleton
     * values are lazily created.  Note also that since tools can only be registered
     * into the context once, circular dependencies can arise from pairs of tools
     * that use each other, if you are not careful.
     * @param context the compilation context into which to register the tools
     */
    public static void register(/*@ non_null @*/ Context context, PrintWriter stdOut) {

        // Notes on tool instantiation:
        // JavacMessages is needed in order to write out any (javac) error messages, such as might happen in processing options
        // JavacMessage automatically reads in the messages bundle when it is created
        // JavacMessages reads an option -- so JmlOptions must be registered before JavacMessages is instantiated
        // Similarly Log reads an option; so Log instantiates JavacMessages
        // Thus both Log and JavacMessages must have their diagFormatter reset after options are processed
        // and any messages printed during option processing will not use any formatter specified on the command-line

        JmlOptions.preRegister(context); // Creates a JmlOptions instance (not a factory) -- must precede getting JavacMessages
        // because JavacMessages access Options
        MockAwareFileManager.preRegister(context); // creates a file manager factory - required for processing options

        // The next call creates the compiler tool chain. The problem is that some Java components cache values of options
        // during tool creation, rather than tool use. All the registration of JML tools is by Context factories, so no Javac tool
        // is actually instantiated until lazily asked for via an instance(context) call.

        // We register the output writer for the Log first because in registering JmlArguments,
        // Arguments is registered, which instantiates a Log. Accordingly, we cannot set a 
        // log (or stdOut/stdErr) based on command-line arguments.
        context.put(Log.outKey,stdOut); // This is reregistered later in super.Main

        // Instantiating JavacMessages reads in the messages defined for jdk.compiler
        // Here we add the JML messages.
        // But there is a problem: JavacMessages reads an option from Options (so JmlOptions must already be registered),
        // but Java option processing needs the messages read in order to emit any error messages.
        // So in creating a JavaCompiler the JavacMessage.diagFormatter is reset based on any options.
        JavacMessages.instance(context).add(Strings.messagesJML);
        JmlOptions.JmlArguments.register(context); // This call is not a factory. It creates a JmlArguments object
        // and also instantiates Log and (Jml)Options.

        // These register JML versions of the various tools.  
        // All register factories that will make the version of the
        // tool when instance() is called for that (Java) tool. It does not matter what
        // order these are called in. However, it can matter what order tools are 
        // instantiated in the constructors of the various tools: construction of a given 
        // tool can require instantiation of other tools, and loops can result.

        // It can be important that tools are instantiated only after all Java options are
        // processed, because some tools will cache values of options.

        JmlTypes.preRegister(context);
        JmlOperators.preRegister(context);
        JmlSpecs.preRegister(context);
        JmlFactory.preRegister(context);
        JmlScanner.JmlScannerFactory.preRegister(context);
        JmlTree.Maker.preRegister(context);
        JmlCompiler.preRegister(context);
        JmlEnter.preRegister(context);
        JmlResolve.preRegister(context);
        JmlFlow.preRegister(context);
        JmlMemberEnter.preRegister(context);
        JmlAttr.preRegister(context);
        JmlCheck.preRegister(context);
        JmlPretty.preRegister(context);
        JmlDeferredAttr.preRegister(context);
        JmlAttr.JmlArgumentAttr.preRegister(context);
        // Command-line specified extensions are registered after options are processed

        // Since we can only set a context value once, we create this listener that just delegates to 
        // another listener, and then change the delegate when we need to, using setProofResultListener().
        context.put(IAPI.IProofResultListener.class, 
                new IAPI.IProofResultListener() {
            IAPI.IProofResultListener delegate = null;
            @Override
            public void reportProofResult(MethodSymbol sym, IProverResult res) { if (delegate != null) delegate.reportProofResult(sym,res); }
            @Override
            public IAPI.IProofResultListener setListener(IAPI.IProofResultListener listener) { 
                IAPI.IProofResultListener d = delegate; delegate = listener; return d; 
            }
        });
    }

    /** Sets the listener to which reports of proof results are sent. */
    public IAPI.IProofResultListener setProofResultListener(IAPI.IProofResultListener listener) {
        return context().get(IAPI.IProofResultListener.class).setListener(listener);
    }

    /** This is overridden so that serious internal bugs are reported as OpenJML
     * rather than Javac bugs.
     */
    @Override
    protected void bugMessage(Throwable ex) {
        stdOut.println("Internal JML bug - please report.  Build" + JavaCompiler.version());
        ex.printStackTrace(stdOut);
    }


    // EXTERNAL API FOR PROGRAMATIC ACCESS TO JML COMPILER INTERNALS

    /** Adds additional options to those already present (or changes 
     * previous settings). */
    public void addOptions(String... args) {
        Context context = context();
        if (!(Options.instance(context) instanceof JmlOptions)) return;
        args = JmlOptions.instance(context).addOptions(args);
        // FIXME - should we be using Arguments to parse and process args?
        for (int i = 0; i < args.length; i++) {
            if (i+1 >= args.length) {
                Options.instance(context).put(args[i],"true");
            } else if (args[i+1].length() == 0 || args[i+1].charAt(0) != '-') {
                Options.instance(context).put(args[i],args[i+1]);
                i++;
            } else {
                Options.instance(context).put(args[i],"true");
            }
        }
    }

    /** Adds a custom option (not checked as a legitimate command-line option);
     * may have an argument after a = symbol */
    public void addUncheckedOption(String arg) {
        JmlOptions.instance(context()).addUncheckedOption(arg);
    }

    /** Attempt to free cached values; this instance of main will
     * be unusable after this call
     */
    public void close() {
        // FIXME - perhaps somehow use the non-visible ReusableContext
        context = null;
    }

    /** An Enum type that gives a choice of various tools to be executed. */
    public static enum Cmd {
        PARSE("parse"), CHECK("check"), ESC("esc"), RAC("rac"), DEP("dep"), JMLDOC("doc"), COMPILE("compile"), INFER("infer");
        String name;
        public String toString() { return name; }
        private Cmd(String name) { this.name = name; }
    }
}
