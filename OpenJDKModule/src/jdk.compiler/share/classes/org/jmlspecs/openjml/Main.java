/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */

package org.jmlspecs.openjml;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.lang.reflect.Method;
import java.net.URL;
import java.nio.file.FileSystems;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.nio.file.Paths;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Properties;

import javax.tools.DiagnosticListener;
import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.esc.MethodProverSMT;
import org.jmlspecs.openjml.proverinterface.IProverResult;

import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.*;
import com.sun.tools.javac.comp.*;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.main.CommandLine;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.main.JmlCompiler;
import com.sun.tools.javac.main.Option;
import com.sun.tools.javac.main.Main.Result;
import com.sun.tools.javac.parser.JmlFactory;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCNewArray;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.JavacMessages;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Options;

/**
 * This class is the main entry point for the JML tool. It uses the javac
 * compiler, but overrides some of the functionality here in order to register
 * tools for the compiler to use that are extensions with JML functionality of
 * the usual tools. Also the handling of JML-specific options is initialized
 * here.  For programmatic access to the facilities of openjml, use the methods
 * of the API class.
 * 
 * <P>
 *  NOTE ON OUTPUT:
 *  <P>
 * Output is produced by this program in a variety of ways, through mechanisms
 * that enable it to be captured for various means of display by the wrapping
 * UI.
 * <P>
 * Log - there is one Log instance per context, retrieved by Log.instance(context).
 * It has a number of writers:
 * <UL>
 * <LI> log.noticeWriter - general information, often guarded by tests of the 
 *   verbose flag
 * <LI> log.warnWriter - for compiler/JML/ESC warnings
 * <LI> log.errWriter - for compiler/JML/ESC errors
 * 
 * <LI> The IProgressReporter - this is used for messages that report progress back
 * to the UI (textual or graphic).
 * 
 * <LI> Diagnostic listener - this listens for warnings and errors, as written to
 * log.warnWriter and log.errWriter.
 * </UL>
 * <P>
 * The output of the log goes to the registered instance of Log [ by 
 * context.put(logKey, new Log(...)) ].  If no log is registered, a default log
 * is used, which sends all channels of information to the PrintWriter registered
 * under context.put(outKey,...).  There is a constructor for a Log that allows
 * the notice, warning and error output to be directed to different PrintWriters.
 * <P>
 * If there is no DiagnosticListener registered, the warning and error outputs
 * are treated as described above.  If there is a DiagnosticListener, then the
 * diagnostic output is sent to that listener instead.
 * <P>
 * For OpenJML:
 * <UL><LI>command-line tool: no diagnostic listener is defined; Log output can be
 * directed to either System.out or System.err by a command-line option
 * <LI>Eclipse: a diagnostic listener is defined that converts warnings and errors
 * into Eclipse markers; Log output is captured by a PrintWriter that directs
 * the output to the Eclipse console.
 * </UL><P>
 * Progress Reporting: Various tools within OpenJML report progress (e.g. as
 * individual files are parsed).  The progress messages are tiered:
 * <UL> 
 * <LI> level 1: low volume, appropriate for text and normal output
 * <LI> level 2: transient progress messages
 * <LI> level 3: verbose only
 * </UL>
 * A tool can receive these progress reports by
 * registering as a delegate via
 * 
 * TODO - check and complete the documentation above
 */
public class Main extends com.sun.tools.javac.main.Main {
    
    // FIXME - get rid of this when we figure out how to control the entry point of the jdk image 
    public static boolean useJML = false;
    
    /** An additional exit code, along with those in the super class */
    public static final int EXIT_CANCELED = -1;

    /** The compilation unit context associated with this instance of Main
     * (for the programmatic API); for the command-line API it is simply 
     * the most recent value of the context, and is used that way in testing. */
    protected Context context;
    
    /** True if compilation has been canceled, by setting this field in some exception handler. */
    public boolean canceled = false;
    
    public Utils utils;
    
    /** Instances of this class are used to abruptly terminate long-running;
     *  catch clauses typically set the Main.canceled field
     * JML operations.
     */
    public static class JmlCanceledException extends RuntimeException {
        private static final long serialVersionUID = 1L;
        public JmlCanceledException(String message) {
            super(message);
        }
    }
    
    /** The diagListener provided when an instance of Main is constructed.
     * The listener will be notified when any diagnostic is generated.
     */
    /*@nullable*/
    protected DiagnosticListener<? extends JavaFileObject> diagListener;
    
    
    // TODO - review use of and document these progress reporters; perhaps move them
    
    public DelegatingProgressListener progressDelegator = new DelegatingProgressListener();

    /** An interface for progress information; the implementation reports progress
     * by calling report(...); clients will receive notification of progress
     * events by implementing this interface and registering the listener with
     * progressDelegate.setDelegate(IProgressReporter).
     *
     */
    public static interface IProgressListener {
        void setContext(Context context);
        boolean report(int level, String message);
        void worked(int ticks);
    }

    /*@nullable*/ /** If nonnull, this listener is notified of progress messages */
    static public java.util.function.Supplier<IProgressListener> progressListener;
    
    /** The compilation Context only allows one instance to be registered for
     * a given class and that instance cannot be changed.
     * So we register an instance of DelegatingProgressListener;
     * then we can change the delegate registered in DelegatingProgressListener
     * to our heart's content. 
     * <P>
     * This class is a Listener that simply passes on reports to its own listeners.
     * It currently only allows one delegate.
     */
    static public class DelegatingProgressListener implements IProgressListener {
        /** The delegate to which this class passes reports. */
        private IProgressListener delegate;
        /** The callback that is called when the application has progress to report */
        public boolean report(int level, String message) {
            if (delegate != null) return delegate.report(level,message);
            return false;
        }
        
        public void worked(int ticks) {
            if (delegate != null) delegate.worked(ticks);
        }
        
        /** Returns true if there is a listener. */
        /*@pure*/
        public boolean hasDelegate() { return delegate != null; }
        
        /** Sets a listener, overriding previous setting; may be null to erase a listener. */
        public void setDelegate(/*@nullable*/ IProgressListener d) {
            delegate = d;
        }
        
        /** Sets the compilation context (passed on to listeners) */
        @Override
        public void setContext(Context context) {
            if (delegate!= null) delegate.setContext(context);
        }
    }
    
    // TODO - review use of level and jmlverbose
    /** This class is a progress listener that prints the progress messages to 
     * a given OutputStream.
     */
    public static class PrintProgressReporter implements IProgressListener {
        protected PrintWriter pw;
        protected Context context;
        
        public PrintProgressReporter(Context context, OutputStream out) {
            pw = new PrintWriter(out);
            this.context = context;
        }
        
        public PrintProgressReporter(Context context, PrintWriter w) {
            pw = w;
            this.context = context;
        }
        
        @Override
        public boolean report(int level, String message) {
            if (level <= 1 || (context != null && Utils.instance(context).jmlverbose >= Utils.JMLVERBOSE)) {
                pw.println(message);
                pw.flush();
            }
            return false;
        }
        
        @Override
        public void worked(int ticks) {}

        @Override
        public void setContext(Context context) { this.context = context; }
    }

    
    
    /**
     * Construct a compiler instance; all options are set to values read from
     * the environment.  
     * Errors go to stderr.
     */
    public Main() throws java.io.IOException {
        this(Strings.applicationName, new PrintWriter(System.err, true));
    }

    /**
     * Construct an initialized compiler instance; all options are set 
     * according to values from the options and args arguments.
     * @param applicationName the name to use for the application
     * @param out  the PrintWriter to which to send information and error messages
     * @param diagListener the listener to receive problem and warning reports
     * @param options the default set of options (adjusted by the command-line
     * args); if null, then default values are read from the environment
     * @param args command-line options
     */
    public Main(/*@ non_null */String applicationName, 
                /*@ non_null */PrintWriter out) 
        throws java.io.IOException {
        super(applicationName,out);
    }
    
    protected Context initialize(
                /*@nullable*/ DiagnosticListener<? extends JavaFileObject> diagListener) {
        check(); // Aborts if the environment does not support OpenJML
        this.diagListener = diagListener;
        this.context = new Context();
        JavacFileManager.preRegister(this.context);
        utils = Utils.instance(this.context);
        return this.context;
    }
    
    public PrintWriter out() {
        return stdOut;
    }
    
    /** Checks that the tool is being run with an adequate JVM - and exits abruptly if not */
    public void check() {
        // FIXME
    }

    /** The external entry point - simply calls execute(args) and exits with the
     * exit code returned.
     * @param args the command-line arguments
     */
    //@ requires args != null && \nonnullelements(args);
    public static void main(String[] args) {
        System.out.println("openjml main");
        useJML = true;
        if (args.length > 0 && args[0].equals("-Xjdb")) {
        	try {
        		// Note: Copied directly from com.sun.tools.javac.Main and not tested
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
        		e.printStackTrace(System.out);
        		System.exit(3);
        	}
        } else {
            System.exit(execute(args, false));  // The boolean: true - errors to stdErr, false - errors to stdOut
        }
    }
    
    // TODO: Move these? Get them from Option?
    
    /** The option string for requesting help information */
    /*@non_null*/
    final public static String helpOption = "-help";
    
    /** The option string for running jmldoc */
    /*@non_null*/
    final public static String jmldocOption = "-doc";

    /** Invokes the compiler on the given command-line arguments; errors go to
     * stdout.
     * @param args the command-line arguments
     * @return     the exit code, as returned to the shell - 0 is success
     */
    //@ requires args != null && \nonnullelements(args);
    public static int execute(String[] args) {
        if (args != null) {
            for (String a: args) {
                if (jmldocOption.equals(a)) {
                    return 4; // FIXME  - org.jmlspecs.openjml.jmldoc.Main.execute(args);
                }
            }
        }
        return execute(args,false);  // The boolean: true - errors to stdErr, false - errors to stdOut
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
                if (jmldocOption.equals(a)) {
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
    public static int execute(/*@non_null*/ PrintWriter writer, /*@nullable*/ DiagnosticListener<? extends JavaFileObject> diagListener, /*@nullable*/ Options options, /*@non_null*/ String[] args) {
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
                    // Pure java compile -- ignores the 'options' parameter
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

                    // MAINTENANCE: This section copied from the super class, so we can use the context jsut created
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
                    if (Utils.instance(compiler.context()).jmlverbose >= Utils.JMLVERBOSE) {
                        writer.println("ENDING with exit code " + errorcode);
                    }
                }
            }
        } catch (JmlCanceledException e) {
            // Error message already issued
            errorcode = Result.CMDERR.exitCode;
        } catch (Exception e) {
            // Most exceptions are caught prior to this, so this will happen only for the
            // most catastrophic kinds of failure such as failures to initialize
            // properly.  (You can test this by programmatically throwing an exception in the try
            // block above.)
            uninitializedLog().error("jml.toplevel.exception",e);
            e.printStackTrace(System.err);
            errorcode = com.sun.tools.javac.main.Main.Result.SYSERR.exitCode; // 3
        }
        return errorcode;
    }
    
    // TODO - needs review when API and Eclipse plugin are fixed
    /** Executes the given command-line, but within the same instance of Main;
     * the instance of Main is completely reinitialized, with a new context.
     * @param writer
     * @param diagListener
     * @param options
     * @param args
     * @return
     */
    public int executeNS(/*@non_null*/ PrintWriter writer, /*@nullable*/ DiagnosticListener<? extends JavaFileObject> diagListener, /*@nullable*/ Options options, /*@non_null*/ String[] args) {
        int errorcode = com.sun.tools.javac.main.Main.Result.ERROR.exitCode; // 1
        try {
            if (args == null) {
                uninitializedLog().error("jml.main.null.args","org.jmlspecs.openjml.Main.main");
                errorcode = com.sun.tools.javac.main.Main.Result.CMDERR.exitCode; // 2
            } else {
                // We create an instance of main through which to call the
                // actual compile method. Note though that the compile method
                // does its own initialization (in the super class). Thus the
                // context and any option processing in the constructor call
                // are thrown away. That is also why we do the hack of saving
                // the options to a private variable, just to be able to
                // apply them in the compile() call below.
                initialize(diagListener);
                // The following line does an end-to-end compile, in a fresh context
                errorcode = compile(args).exitCode; // context and new options are created in here
                if (errorcode > Result.CMDERR.exitCode || 
                        Utils.instance(context()).jmlverbose > Utils.PROGRESS) {
                    writer.println("ENDING with exit code " + errorcode); // TODO - not sure we want this - but we'll need to change the tests
                }
            }
        } catch (JmlCanceledException e) {
            // Error message already issued
            errorcode = EXIT_CANCELED; // Indicates being cancelled
        } catch (Exception e) {
            // Most exceptions are caught prior to this, so this will happen only for the
            // most catastrophic kinds of failure such as failures to initialize
            // properly.  (You can test this by programmatically throwing an exception in the try
            // block above.)
            uninitializedLog().error("jml.toplevel.exception",e);
            e.printStackTrace(System.err);
            errorcode = com.sun.tools.javac.main.Main.Result.SYSERR.exitCode; // 3
        }
        return errorcode;
    }
    
    private IAPI.IProofResultListener prl;
    
    // TODO - needs review when API and Eclipse plugin are fixed
    public int executeNS(/*@non_null*/ PrintWriter writer, /*@nullable*/ DiagnosticListener<? extends JavaFileObject> diagListener, IAPI.IProofResultListener prListener, /*@nullable*/ Options options, /*@non_null*/ String[] args) {
        int errorcode = com.sun.tools.javac.main.Main.Result.ERROR.exitCode; // 1
        try {
            if (args == null) {
                uninitializedLog().error("jml.main.null.args","org.jmlspecs.openjml.Main.main");
                errorcode = com.sun.tools.javac.main.Main.Result.CMDERR.exitCode; // 2
            } else {
                // We create an instance of main through which to call the
                // actual compile method. Note though that the compile method
                // does its own initialization (in the super class). Thus the
                // context and any option processing in the constructor call
                // are thrown away. That is also why we do the hack of saving
                // the options to a private variable, just to be able to
                // apply them in the compile() call below.
                initialize(diagListener);
                setProofResultListener(prListener);  // FIXME - this is wiped away in the compile() below, along with the initialization just above???
                prl = prListener;                    // FIXME - necessitating this end run with prl
                
                // The following lines do an end-to-end compile, in a fresh context
                errorcode = compile(args).exitCode; // context and new options are created in here
                if (errorcode > Result.CMDERR.exitCode || 
                        Utils.instance(context()).jmlverbose > Utils.PROGRESS) {
                    writer.println("ENDING with exit code " + errorcode); // TODO - not sure we want this - but we'll need to change the tests
                }
            }
        } catch (JmlCanceledException e) {
            // Error message already issued
            errorcode = EXIT_CANCELED; // Indicates being cancelled
        } catch (Exception e) {
            // Most exceptions are caught prior to this, so this will happen only for the
            // most catastrophic kinds of failure such as failures to initialize
            // properly.  (You can test this by programmatically throwing an exception in the try
            // block above.)
            uninitializedLog().error("jml.toplevel.exception",e);
            e.printStackTrace(System.err);
            errorcode = com.sun.tools.javac.main.Main.Result.SYSERR.exitCode; // 3
        }
        return errorcode;
    }

    /** This is a convenience method to initialize just enough that we can log
     * an error or warning message for issues that arise before the compiler
     * is properly initialized.
     * @return a Log instance to use
     */
    static protected Log uninitializedLog() {
        // This is a temporary context just for logging error messages when
        // overall initialization fails.
        // It is not the one used for the compilation
        // It does use Options
        Context context = new Context();
        JavacMessages.instance(context).add(Strings.messagesJML);
        return Log.instance(context);
    }
    
    /** This method is overridden so that the JML compiler can register its
     *  own tools for the various phases. 
     */
    @Override
    public Main.Result compile(String[] args, Context context) {
        this.context = context;
        register(context);
        setProofResultListener(prl);
        args = JmlOptions.instance(context).processJmlArgs(args, Options.instance(context), null);
        // Note that the Java option processing happens in compile method call below.
        // Those options are not read at the time of the register call,
        // but the register call has to happen before compile is called.
        canceled = false;
        Main.Result exit = super.compile(args,context);
        return exit;
    }

//    // TODO _ document
//    public java.util.List<String> computeDependencyClosure(java.util.List<String> files) {
//        // fill out dependencies
//        java.util.List<String> newargs = new ArrayList<String>();
////        Dependencies d = Dependencies.instance(context);
//        Set<String> done = new HashSet<String>();
//        java.util.List<String> todo = new LinkedList<String>();
//        //JavacFileManager jfm = (JavacFileManager)context.get(JavaFileManager.class);; // FIXME - this causes Lint to be initialized before the Java options are registered
//        for (String s: files) {
//            // FIXME - don't hardcode this list of suffixes here
//            if (Utils.instance(context).hasValidSuffix(s)) {
//                todo.add(s);
//            }
//        }
//        while (!todo.isEmpty()) {
//            String o = todo.remove(0);
//            if (done.contains(o)) continue;
//            done.add(o);
////            if (o.getName().endsWith(".java")) newargs.add("C:" + o.toUri().getPath()); // FIXME - a hack to get the full path
//            if (o.endsWith(".java")) newargs.add(o); // FIXME FOR REAL - this needs to be made sane
////            Set<JavaFileObject> affected = d.getAffected(o);
////            if (affected != null) {
////                todo.addAll(affected);
////                //Log.instance(context).noticeWriter.println("Adding " + affected.size() + " dependencies for " + o);
////            }
//        }
//        return newargs;
//    }
    

    /** This registers the JML versions of many of the tools (e.g. scanner, parser,
     * specifications database,...) used by the compiler.  They must be registered
     * before the Java versions are invoked, since in most cases singleton
     * values are lazily created.  Note also that since tools can only be registered
     * into the context once, circular dependencies can arise from pairs of tools
     * that use each other, if you are not careful.
     * @param context the compilation context into which to register the tools
     */
    public void register(/*@ non_null @*/ Context context) {
        this.context = context; // TODO - when might these be different to start with?
        if (progressDelegator != null) progressDelegator.setContext(context);
        context.put(IProgressListener.class,progressDelegator);
        context.put(key, this);
        registerTools(context,stdOut,diagListener);
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
    
    public void setProofResultListener(IAPI.IProofResultListener listener) {
        context.get(IAPI.IProofResultListener.class).setListener(listener);
    }

    public static Context.Key<Main> key = new Context.Key<Main>();
    
    public static Main instance(Context context) {
        return context.get(key);
    }

    /** Returns a reference to the API's compilation context. */
    public /*@nullable*/ Context context() {
        return context;
    }
    
    /** Called to register the JML internal tools that replace the tools used
     * in the Java compiler.
     * @param context the compiler context in which the tools are to be used
     * @param out the PrintWriter used for error and informational messages
     * @param diagListener if not null, a listener that will receive reports
     *    of warnings and errors
     */
    public static <S> void registerTools(/*@non_null*/ Context context, 
            /*@non_null*/ PrintWriter out, 
            /*@nullable*/ DiagnosticListener<S> diagListener) {

        // We register the output writer for the Log first so that it is
        // available if tool registration (or argument processing) needs the
        // Log.  However, note that if the Log itself is actually instantiated before
        // Java arguments are read, then it is not set consistently with those 
        // options.
        context.put(Log.outKey,out);
        
        if (diagListener != null) context.put(DiagnosticListener.class, diagListener);

        // These have to be first in case there are error messages during 
        // tool registration.
        // registering an additional source of JML-specific error messages
        JmlOptions.preRegister(context); // Must precede JavacMessages
        JavacMessages.instance(context).add(Strings.messagesJML);
        JmlOptions.JmlArguments.register(context);
        
        // These register JML versions of the various tools.  Some just
        // register factories in which no actual instances are created until 
        // instance(context) is called on the particular tool.  Creating instances
        // may trigger a cascade of tool instance generation, which can create
        // tools (such as the Log) before the Options are processed and can
        // trigger some circular dependencies in the constructors of the various
        // tools.
        // Any initialization of these tools that needs to be done based on 
        // options should be performed in setupOptions().
        JmlTypes.preRegister(context);
        JmlOperators.preRegister(context);
        JmlSpecs.preRegister(context); // registering the specifications repository
        JmlFactory.preRegister(context); // registering a Jml-specific factory from which to generate JmlParsers
        JmlScanner.JmlFactory.preRegister(context); // registering a Jml-specific factory from which to generate JmlScanners
        JmlTree.Maker.preRegister(context); // registering a JML-aware factory for generating JmlTree nodes
        JmlCompiler.preRegister(context);
        JmlEnter.preRegister(context);
        JmlResolve.preRegister(context);
        JmlFlow.preRegister(context);
        JmlMemberEnter.preRegister(context);
        JmlAttr.preRegister(context);  // registering a JML-aware type checker
        JmlCheck.preRegister(context);
        JmlPretty.preRegister(context);
        JmlDeferredAttr.preRegister(context); // registers when created
        // Extensions are registered after options are processed
    }
    
    /** This is overridden so that serious internal bugs are reported as OpenJML
     * rather than Javac bugs.
     */
    @Override
    protected void bugMessage(Throwable ex) {
        stdErr.println("Internal JML bug - please report.  Build" + JavaCompiler.version());
        ex.printStackTrace(stdErr);
    }
    
    
    // EXTERNAL API FOR PROGRAMATIC ACCESS TO JML COMPILER INTERNALS

    // TODO - REVIEW IN FUTURE
//    public boolean initializingOptions = false;
//    
//    /** This method initializes the Options.instance(context) instance of
//     * Options class. If the options argument is not null, its content is used
//     * to initialize Options.instance(context); if options is null, then
//     * Options.instance(context) is initialized by reading
//     * the options specified in the environment (System properties +
//     * openjml properties files). Then the specified args are processed to make any 
//     * further adjustments to the options. Any errors are reported through the
//     * log mechanism. Any non-options in the args list (e.g. files) are 
//     * warned about and ignored. 
//     */
//    public void initializeOptions(/*@nullable*/ Options options, /*@non_null*/ String... args) {
//        initializingOptions = true;
//        Options opts = Options.instance(context);
//        if (options == null) {
//            coreDefaultOptions(opts);
//            setInitialOptions(opts, args);
//            Properties properties = Utils.findProperties(context);
//            setPropertiesFileOptions(opts, properties);
//        } else {
//            opts.putAll(options);
//        }
//
//        if (args != null) try { // Do the following even if there are no args, because other setup is done as well (e.g. extensions)
//            Collection<File> files = processArgs(CommandLine.parse(ENV_OPT_NAME, List.from(args)));
//            if (files != null && !files.isEmpty()) {
//                warning(context, "jml.ignore.extra.material",files.iterator().next().getName());
//            }
//        } catch (java.io.IOException e) {
//            Log.instance(context).error("jml.process.args.exception", e.toString());
//        }
//        initializingOptions = false;
//    }    
    // TODO - Review these - are they used?
//    /** Sets default initial options to the Options instance that is the 
//     * argument (does not change the compilation context Options directly);
//     * edit this method to set any defaults that would not be set by other
//     * means.
//     */
//    protected void coreDefaultOptions(Options opts) {
//        opts.put(JmlOption.LOGIC.optionName(), "ALL");
//        opts.put(JmlOption.PURITYCHECK.optionName(), null);
//    }
//    
//    protected void setInitialOptions(Options opts, String ... args) {
//        for (int i=0; i<args.length; i++){
//            String s = args[i];
//            if (JmlOption.PROPERTIES_DEFAULT.optionName().equals(s)) {
//                if (i+1 < args.length) {
//                    opts.put(JmlOption.PROPERTIES_DEFAULT.optionName(), args[i+1]);
//                } else {
//                    utils.warning("jml.expected.parameter",s);
//                }
//            }
//        }
//    }
    
    
    /** Adds additional options to those already present (which may change 
     * previous settings). */
    public void addOptions(String... args) {
        JmlOptions.instance(context).addOptions(args);
    }
    
    /** Adds a custom option (not checked as a legitimate command-line option);
     * may have an argument after a = symbol */
    public void addUncheckedOption(String arg) {
        JmlOptions.instance(context).addUncheckedOption(arg);
    }

    public boolean setupOptions() {
        return JmlOptions.instance(context).setupOptions();
    }

    // FIXME - move this somewhere more appropriate?
    /** Appends the internal runtime directory to the -classpath option.
     */
    static protected void appendRuntime(Context context) {
        
        String jmlruntimePath = null;
       
        /** This property is just used in testing. */ // TODO - check this
        String sy = Options.instance(context).get(Strings.defaultRuntimeClassPath);
        if (sy != null) {
            jmlruntimePath = sy;
        }

        // Look for jmlruntime.jar in the classpath itself
       
        if (jmlruntimePath == null) {
            URL url = ClassLoader.getSystemResource(Strings.runtimeJarName);
            if (url != null) {
                jmlruntimePath = url.getFile();
                if (jmlruntimePath.startsWith("file:/")) {
                    jmlruntimePath = jmlruntimePath.substring("file:/".length());
                }
            }
        }
       
        // Otherwise look for something in the same directory as something on the classpath
       
        String classpath = System.getProperty("java.class.path");
        if (jmlruntimePath == null) {
            String[] ss = classpath.split(java.io.File.pathSeparator);
            for (String s: ss) {
                if (s.endsWith(".jar")) {
                    try {
                        File f = new File(s).getCanonicalFile().getParentFile();
                        if (f != null) {
                            f = new File(f,Strings.runtimeJarName);
                            if (f.isFile()) {
                                jmlruntimePath = f.getPath();
                                break;
                            }
                        }
                    } catch (IOException e) {
                        // Just skip
                    }
                } else {
                    File f = new File(new File(s),Strings.runtimeJarName);
                    if (f.isFile()) {
                        jmlruntimePath = f.getPath();
                        break;
                    }
                }
            }
        }
       
        // The above all presume some variation on the conventional installation
        // of the command-line tool.  In the development environment, those
        // presumptions do not hold.  So in that case we use the appropriate
        // bin directories directly. We make sure that we get both of them: 
        // the annotations and runtime utilties.
        // This also takes care of the case in which the openjml.jar file is in
        // the class path under a different name.

        if (jmlruntimePath == null) {
            URL url = ClassLoader.getSystemResource(Strings.jmlAnnotationPackage.replace('.','/'));
            if (url != null) {
                try {
                    String s = url.getPath();
                    if (s.startsWith("file:")) s = s.substring("file:".length());
                    int b = (s.length()> 2 && s.charAt(0) == '/' && s.charAt(2) == ':') ? 1 : 0;
                    int k = s.indexOf("!");
                    if (k >= 0) {
                        s = s.substring(b,k);
                    } else {
                        s = s.substring(b);
                        s = new File(s).getParentFile().getParentFile().getParent();
                    }
                    if (new File(s).exists()) {
                        jmlruntimePath = s;
                    }

                    url = ClassLoader.getSystemResource(Strings.jmlSpecsPackage.replace('.','/'));
                    if (url != null) {
                        s = url.getPath();
                        if (s.startsWith("file:")) s = s.substring("file:".length());
                        b = (s.length()> 2 && s.charAt(0) == '/' && s.charAt(2) == ':') ? 1 : 0;
                        k = s.indexOf("!");
                        if (k >= 0) {
                            s = s.substring(b,k);
                        } else {
                            s = s.substring(b);
                            s = new File(s).getParentFile().getParentFile().getParent();
                        }
                        if (new File(s).exists() && !s.equals(jmlruntimePath)) {
                            jmlruntimePath = jmlruntimePath + java.io.File.pathSeparator + s;
                        }
                    }
                } catch (Exception e) {
                    // Just skip
                }
            }
        }

        if (jmlruntimePath == null) {
            // This is for the case of running the GUI in the development environment
            String srt = System.getProperty(Strings.eclipseSpecsProjectLocation); // FIXME _ probably can replace this with finding a plugin
            srt = srt + "/../OpenJML/OpenJML/bin-runtime";
            File f = new File(srt);
            if (f.exists() && f.isDirectory()) {
                jmlruntimePath = srt;
            }

        }

        if (jmlruntimePath != null) {
            Utils.instance(context).note(true, "Using internal runtime " + jmlruntimePath);
            String cp = Options.instance(context).get("-classpath");
            if (cp == null) cp = System.getProperty("java.class.path");
            cp = cp==null ? jmlruntimePath : (cp + java.io.File.pathSeparator + jmlruntimePath);
            Options.instance(context).put("-classpath",cp);
            Utils.instance(context).note(true, "Classpath: " + Options.instance(context).get("-classpath"));
        } else {
            Utils.instance(context).warning("jml.no.internal.runtime");
        }
    }

    /** An Enum type that gives a choice of various tools to be executed. */
    public static enum Cmd {
        CHECK("check"), ESC("esc"), RAC("rac"), DEP("dep"), JMLDOC("doc"), COMPILE("compile"), INFER("infer");
        String name;
        public String toString() { return name; }
        private Cmd(String name) { this.name = name; }
    }

}
