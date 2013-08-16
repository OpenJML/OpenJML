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
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.TreeSet;

import javax.annotation.processing.Processor;
import javax.tools.DiagnosticListener;
import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.annotation.Pure;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlCheck;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlFlow;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.main.CommandLine;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.parser.ExpressionExtension;
import com.sun.tools.javac.parser.JmlFactory;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JavacMessages;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
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
    
    public static final int EXIT_CANCELED = -1;

    /** The compilation unit context associated with this instance of Main
     * (for the programmatic API); for the command-line API it is simply 
     * the most recent value of the context, and is used that way in testing. */
    protected Context context;
    
    /** The diagListener provided when an instance of Main is constructed.
     * The listener will be notified when any diagnostic is generated.
     */
    @Nullable
    protected DiagnosticListener<? extends JavaFileObject> diagListener;
    
    /** Instances of this class are used to abruptly terminate long-running
     * JML operations.
     * @author David R. Cok
     */
    public static class JmlCanceledException extends RuntimeException {
        private static final long serialVersionUID = 1L;
        public JmlCanceledException(String message) {
            super(message);
        }
    }
    
    // TODO - review use of and document these progress reporters; perhaps move them
    
    public DelegatingProgressListener progressDelegate = new DelegatingProgressListener();

    /** An interface for progress information; the implementation reports progress
     * by calling report(...); clients will receive notification of progress
     * events by implementing this interface and registering the listener with
     * progressDelegate.setDelegate(IProgressReporter).
     *
     */
    public static interface IProgressListener {
        void setContext(Context context);
        boolean report(int ticks, int level, String message);
    }
    
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
        public boolean report(int ticks, int level, String message) {
            if (delegate != null) return delegate.report(ticks,level,message);
            return false;
        }
        
        /** Returns true if there is a listener. */
        @Pure
        public boolean hasDelegate() { return delegate != null; }
        
        /** Sets a listener; may be null to erase a listener. */
        public void setDelegate(@Nullable IProgressListener d) {
            delegate = d;
        }
        
        /** Sets the compilation context (passed on to listeners) */
        @Override
        public void setContext(Context context) { if (delegate!= null) delegate.setContext(context); }
    }
    
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
        public boolean report(int ticks, int level, String message) {
            if (level <= 1 || (context != null && Utils.instance(context).jmlverbose >= Utils.JMLVERBOSE)) {
                pw.println(message);
                pw.flush();
            }
            return false;
        }

        @Override
        public void setContext(Context context) { this.context = context; }
    }

    
    
    /**
     * Construct a compiler instance; all options are set to values read from
     * the environment.  
     * Errors go to stderr.
     */
    // @edu.umd.cs.findbugs.annotations.SuppressWarnings("NM_SAME_SIMPLE_NAME_AS_SUPERCLASS")
    public Main() throws java.io.IOException {
        this(Strings.applicationName, new PrintWriter(System.err, true), null, null);
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
                /*@ non_null */PrintWriter out, 
                @Nullable DiagnosticListener<? extends JavaFileObject> diagListener,
                @Nullable Options options,
                String... args) 
        throws java.io.IOException {
        super(applicationName,out);
        initialize(out,diagListener,options,args);
    }
    
    protected void initialize( 
                /*@ non_null */PrintWriter out, 
                @Nullable DiagnosticListener<? extends JavaFileObject> diagListener,
                @Nullable Options options,
                String... args) {
        check(); // Aborts if the environment does not support OpenJML
        this.out = out;
        this.diagListener = diagListener;
        context = new Context();
        JavacFileManager.preRegister(context); // can't create it until Log has been set up
        register(context);
        if (args == null) args = emptyArgs;
        initializeOptions(options,args); // Creates a new Options instance and initializes it per the arguments
    }
    
    public PrintWriter out() {
        return out;
    }
    
    /** Checks that the tool is being run with an adequate JVM - and exits abruptly if not */
    public void check() {
        javax.lang.model.element.ElementKind[] kinds = javax.lang.model.element.ElementKind.values();
        if (kinds[kinds.length-1] == javax.lang.model.element.ElementKind.OTHER) {
            System.out.println("OpenJML is being run with a Java 6 or earlier VM, which is not supported.");
            System.exit(99);
        }
    }

    /** The external entry point - simply calls execute(args) and exits with the
     * exit code returned.
     * @param args the command-line arguments
     */
    //@ requires args != null && \nonnullelements(args);
    public static void main(String[] args) throws Exception {
        if (args.length > 0 && args[0].equals("-Xjdb")) {
            // Note: Copied directly from com.sun.tools.javac.Main and not tested
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
            System.exit(execute(args));
        }
    }
    
    // TODO: Move these? Get them from Option?
    
    /** The option string for requesting help information */
    @NonNull
    final public static String helpOption = "-help";
    
    /** The option string for running jmldoc */
    @NonNull
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
                    return org.jmlspecs.openjml.jmldoc.Main.execute(args);
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
    public static int execute(@NonNull PrintWriter writer, @Nullable DiagnosticListener<? extends JavaFileObject> diagListener, @Nullable Options options, @NonNull String[] args) {
        int errorcode = com.sun.tools.javac.main.Main.EXIT_ERROR; // 1
        try {
            if (args == null) {
                uninitializedLog().error("jml.main.null.args","org.jmlspecs.openjml.Main.main");
                errorcode = com.sun.tools.javac.main.Main.EXIT_CMDERR; // 2
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
                    if (options != null) {
                        uninitializedLog().warning("jml.ignoring.options");
                    }
                    errorcode = com.sun.tools.javac.Main.compile(newargs);
                } else {
                    // We create an instance of main through which to call the
                    // actual compile method. Note though that the compile method
                    // does its own initialization (in the super class). Thus the
                    // context and any option processing in the constructor call
                    // are thrown away. That is also why we do the hack of saving
                    // the options to a private variable, just to be able to
                    // apply them in the compile() call below.
                    Main compiler = new Main(Strings.applicationName, writer, diagListener, options, emptyArgs);
                    savedOptions = Options.instance(compiler.context());
                    // The following line does an end-to-end compile, in a fresh context
                    errorcode = compiler.compile(args); // context and new options are created in here
                    if (errorcode > EXIT_CMDERR || 
                            Utils.instance(compiler.context()).jmlverbose > Utils.PROGRESS) {
                        writer.println("ENDING with exit code " + errorcode);
                    }
                }
            }
        } catch (JmlCanceledException e) {
            // Error message already issued
            errorcode = EXIT_CMDERR;
        } catch (Exception e) {
            // Most exceptions are caught prior to this, so this will happen only for the
            // most catastrophic kinds of failure such as failures to initialize
            // properly.  (You can test this by programmatically throwing an exception in the try
            // block above.)
            uninitializedLog().error("jml.toplevel.exception",e);
            e.printStackTrace(System.err);
            errorcode = com.sun.tools.javac.main.Main.EXIT_SYSERR; // 3
        }
        return errorcode;
    }
    
    /** Executes the given command-line, but within the same instance of Main;
     * the instance of Main is completely reinitialized, with a new context.
     * @param writer
     * @param diagListener
     * @param options
     * @param args
     * @return
     */
    public int executeNS(@NonNull PrintWriter writer, @Nullable DiagnosticListener<? extends JavaFileObject> diagListener, @Nullable Options options, @NonNull String[] args) {
        int errorcode = com.sun.tools.javac.main.Main.EXIT_ERROR; // 1
        try {
            if (args == null) {
                uninitializedLog().error("jml.main.null.args","org.jmlspecs.openjml.Main.main");
                errorcode = com.sun.tools.javac.main.Main.EXIT_CMDERR; // 2
            } else {
                // We create an instance of main through which to call the
                // actual compile method. Note though that the compile method
                // does its own initialization (in the super class). Thus the
                // context and any option processing in the constructor call
                // are thrown away. That is also why we do the hack of saving
                // the options to a private variable, just to be able to
                // apply them in the compile() call below.
                savedOptions = Options.instance(context());
                initialize(writer, diagListener, options, emptyArgs);
                // The following line does an end-to-end compile, in a fresh context
                errorcode = compile(args); // context and new options are created in here
                if (errorcode > EXIT_CMDERR || 
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
            errorcode = com.sun.tools.javac.main.Main.EXIT_SYSERR; // 3
        }
        return errorcode;
    }

    /** This is a convenience method to initialize just enough that we can log
     * an error or warning message for issues that arise before the compiler
     * is properly initialized.
     * @return a Log instance to use
     */
    static protected Log uninitializedLog() {
        Context context = new Context(); // This is a temporary context just for this error message.
        // It is not the one used for the options and compilation
        JavacMessages.instance(context).add(Strings.messagesJML);
        return Log.instance(context);
    }
    
    /** Just used to communicate a set of options from execute(...) to 
     * compile(...), since it cannot be passed through the super call.
     */
    static private Options savedOptions = null;

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
    //@Override
    //public int compile(String[] args, Context context) {

    @Override
    public int compile(String[] args,
                Context context,
                List<JavaFileObject> fileObjects,
                Iterable<? extends Processor> processors) {

        this.context = context;
        register(context);
        initializeOptions(savedOptions);
        // Note that the Java option processing happens in compile method call below.
        // Those options are not read at the time of the register call,
        // but the register call has to happen before compile is called.
        int exit = super.compile(args,context,fileObjects,processors);
        if (args.length == 0 || Options.instance(context).get(helpOption) != null) {
            helpJML(out);
        }
        return exit;
    }
        
    /** This is a utility method to print out all of the JML help information */
    protected void helpJML(PrintWriter w) {
        w.print(JmlOption.helpInfo());
        w.flush();
    }
    
    /** This method scans the input sequence of command-line arguments, 
     * processing any that are recognized as JML options.  Those options
     * are registered in the Options map.  The String[] returned contains
     * all of the command-line arguments in the input, omitting those recognized
     * as JML options.
     * @param args the input command-line arguments
     * @param options the Options map in which recognized options are recorded
     * @return all arguments not recognized as JML
     */
    //@ requires \nonnullelements(args);
    //@ ensures \result != null && \nonnullelements(\result);
    String[] processJmlArgs(@NonNull String [] args, @NonNull Options options, ListBuffer<File> jmlfiles) {
        java.util.List<String> newargs = new ArrayList<String>();
        java.util.List<String> files = new ArrayList<String>();
        int i = 0;
        while (i<args.length) {
            i = processJmlArg(args,i,options,newargs,files);
        }
        //newargs.addAll(computeDependencyClosure(files));
        newargs.addAll(files);
        File f;
        Iterator<String> iter = newargs.iterator();
        while (iter.hasNext()) {
            String s = iter.next();
            if (s.endsWith(".jml") && (f=new File(s)).exists()) {
                jmlfiles.add(f);
                iter.remove();
            }
        }
        return newargs.toArray(new String[newargs.size()]);
    }
    
    // TODO _ document
    public java.util.List<String> computeDependencyClosure(java.util.List<String> files) {
        // fill out dependencies
        java.util.List<String> newargs = new ArrayList<String>();
//        Dependencies d = Dependencies.instance(context);
        Set<String> done = new HashSet<String>();
        java.util.List<String> todo = new LinkedList<String>();
        //JavacFileManager jfm = (JavacFileManager)context.get(JavaFileManager.class);; // FIXME - this causes Lint to be initialized before the Java options are registered
        for (String s: files) {
            // FIXME - don't hardcode this list of suffixes here
            if (Utils.instance(context).hasValidSuffix(s)) {
                todo.add(s);
            }
        }
        while (!todo.isEmpty()) {
            String o = todo.remove(0);
            if (done.contains(o)) continue;
            done.add(o);
//            if (o.getName().endsWith(".java")) newargs.add("C:" + o.toUri().getPath()); // FIXME - a hack to get the full path
            if (o.endsWith(".java")) newargs.add(o); // FIXME FOR REAL - this needs to be made sane
//            Set<JavaFileObject> affected = d.getAffected(o);
//            if (affected != null) {
//                todo.addAll(affected);
//                //Log.instance(context).noticeWriter.println("Adding " + affected.size() + " dependencies for " + o);
//            }
        }
        return newargs;
    }
    
    /** Processes a single JML command-line option and any arguments.
     * 
     * @param args the full array of command-line arguments
     * @param i    the index of the argument to be processed
     * @param options the options object to be adjusted as JML options are found
     * @param remainingArgs any arguments that are not JML options
     * @return the index of the next argument to be processed
     */
    //@ requires \nonnullelements(args);
    //@ requires (* elements of remainingArgs are non-null *);
    //@ requires 0<= i && i< args.length;
    //@ ensures \result > i;
    int processJmlArg(@NonNull String[] args, int i, @NonNull Options options, @NonNull java.util.List<String> remainingArgs, @NonNull java.util.List<String> files ) {
        String res = "";
        String s = args[i++];
        if (s == null || s.isEmpty()) return i; // For convenience, allow but ignore null or empty arguments
        IOption o = JmlOption.find(s);
        while (o!=null && o.synonym()!=null) {
            s = o.synonym();
            o = JmlOption.find(s);
        }
        if (o == null) {
            int k = s.indexOf('=');
            if (k != -1) {
                res = s.substring(k+1,s.length());
                s = s.substring(0,k);
                o = JmlOption.find(s);
                if (o != null) {
                    if (o.hasArg()) {}
                    else if ("false".equals(res)) res = null;
                    else if ("true".equals(res)) res = "";
                    else {
                        res = "";
                        Log.instance(context).warning("jml.ignoring.parameter",s);
                    }
                }
            }
            if (s.equals(helpOption)) options.put(s,"");
        } else if (o.hasArg()) {
            if (i < args.length) {
                res = args[i++];
            } else {
                res = "";
                Log.instance(context).warning("jml.expected.parameter",s);
            }
        }
        if (o == null) {
            remainingArgs.add(s);
        } else if (JmlOption.DIR.optionName().equals(s) || JmlOption.DIRS.optionName().equals(s)) {
            java.util.List<File> todo = new LinkedList<File>();
            todo.add(new File(res));
            if (JmlOption.DIRS.optionName().equals(s)) {
                while (i<args.length && (res=args[i]).length() > 0 && res.charAt(0) != '-') {
                    todo.add(new File(res));
                    i++;
                }
            }
            Utils utils = Utils.instance(context);
            while (!todo.isEmpty()) {
                File file = todo.remove(0);
                if (file.isDirectory()) {
                    for (File ff: file.listFiles()) {
                        todo.add(ff);
                    }
                } else if (!file.isFile()) {
                    Log.instance(context).warning("jml.command.line.arg.not.a.file",file);
                } else if (utils.hasJavaSuffix(file.getName())) { // FIXME - for now just ignoring .jml files - should replace it with the corresponding .java file to be sure both are checked together
                    files.add(file.toString());
                }
            }
        } else {
            // An empty string is the value of the option if it takes no arguments
            // That is, for boolean options, "" (or any non-null) is true, null is false
            options.put(s,res);
        }
        return i;
    }
    
    /** This method is called after options are read, but before tools are 
     * registered and before compilation actually begins; 
     * here any additional option checking or
     * processing can be performed.
     */
    // This should be able to be called without difficulty whenever any option
    // is changed
    public boolean setupOptions() {
        // CAUTION: Do not initialize any of the tools in here
        // If, for example, JmlSpecs gets initialized, then Target will
        // get initialized and it will grab the current version of -target
        // before all the options are set
        Options options = Options.instance(context);
        Utils utils = Utils.instance(context);

        String t = options.get(JmlOption.JMLTESTING.optionName());
        Utils.testingMode =  ( t != null && !t.equals("false"));
        
        utils.jmlverbose = Utils.NORMAL;
        String levelstring = options.get(JmlOption.VERBOSENESS.optionName());
        if (levelstring != null) {
            utils.jmlverbose = Integer.parseInt(levelstring);
        }
        
        if (utils.jmlverbose >= Utils.PROGRESS) {
            // We check for an existing delegate, because if someone is calling
            // OpenJML programmatically, they may have set one up already.
            // Note, though that this won't udo the setting, if verbosity is
            // turned off.
            if (!progressDelegate.hasDelegate()) progressDelegate.setDelegate(new PrintProgressReporter(context,out));
        }
        
        if (options.get(JmlOption.USEJAVACOMPILER.optionName()) != null) {
            Log.instance(context).noticeWriter.println("The -java option is ignored unless it is the first command-line argument"); // FIXME - change to a warning
        }
        
        Cmd cmd = Cmd.CHECK; // default
        String val = options.get(JmlOption.COMMAND.optionName());
        try {
            if (val != null) cmd = Cmd.valueOf(val.toUpperCase());
        } catch (IllegalArgumentException e) {
            Log.instance(context).error("jml.bad.command",val);
            return false;
        }
        utils.rac = cmd == Cmd.RAC;
        utils.esc = cmd == Cmd.ESC;
        utils.check = cmd == Cmd.CHECK;
        utils.compile = cmd == Cmd.COMPILE;
        boolean picked = utils.rac||utils.esc||utils.check||utils.compile;
        if (!picked && cmd != null) {
            Log.instance(context).error("jml.unimplemented.command",cmd);
            return false;
        }
        if (!picked) utils.check = true;

        String keysString = options.get(JmlOption.KEYS.optionName());
        utils.commentKeys = new HashSet<String>();
        if (keysString != null) {
            String[] keys = keysString.split(",");
            for (String k: keys) utils.commentKeys.add(k);
        }
        
        if (utils.esc) utils.commentKeys.add("ESC"); 
        if (utils.rac) utils.commentKeys.add("RAC"); 
        JmlSpecs.instance(context).initializeSpecsPath();

        if (options.get(JmlOption.NOINTERNALRUNTIME.optionName()) == null) appendRuntime(context);
        
        String limit = JmlOption.value(context,JmlOption.MAXWARNINGS);
        if (limit == null || limit.equals("all")) {
            utils.maxWarnings = Integer.MAX_VALUE; // no limit is the default
        } else {
            try {
                int k = Integer.parseInt(limit);
                utils.maxWarnings = k <= 0 ? Integer.MAX_VALUE : k;
            } catch (NumberFormatException e) {
                // FIXME _ change to an error
                Log.instance(context).noticeWriter.println("Expected a number or 'all' as argument for -escMaxWarnings: " + limit);
                utils.maxWarnings = Integer.MAX_VALUE;
            }
        }
        
        String check = JmlOption.value(context,JmlOption.FEASIBILITY);
        if (check == null) {
            options.put(JmlOption.FEASIBILITY.optionName(),"all");
        } else if (check.equals("all") || 
                check.equals("preconditions") || 
                check.equals("exit") || 
                check.equals("none")) {
            // continue
        } else {
            Log.instance(context).noticeWriter.println("Expected 'all' or 'none' or 'preconditions' as argument for -checkFeasibility: " + check);
        }
        return true;
}
    


    /** We override this method in order to process the JML command-line 
     * arguments and to do any tool-specific initialization
     * after the command-line arguments are processed.  
     */
    // @edu.umd.cs.findbugs.annotations.SuppressWarnings("ST_WRITE_TO_STATIC_FROM_INSTANCE_METHOD")
    @Override
    public Collection<File> processArgs(String[] args, String[] classNames) {
        Options options = Options.instance(this.context);
        ListBuffer<File> jmlfiles = new ListBuffer<File>();
        args = processJmlArgs(args,options,jmlfiles);
        if (filenames == null) filenames = new TreeSet<File>(); // needed when called from the API
        Collection<File> files = super.processArgs(args,classNames);
        if (files != null) files.addAll(jmlfiles);
        //args.addAll(computeDependencyClosure(files));
        if (!setupOptions()) return null;
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
        if (progressDelegate != null) progressDelegate.setContext(context);
        context.put(IProgressListener.class,progressDelegate);
        registerTools(context,out,diagListener);
    }
    
    /** Called to register the JML internal tools that replace the tools used
     * in the Java compiler.
     * @param context the compiler context in which the tools are to be used
     * @param out the PrintWriter used for error and informational messages
     * @param diagListener if not null, a listener that will receive reports
     *    of warnings and errors
     */
    public static <S> void registerTools(@NonNull Context context, 
            @NonNull PrintWriter out, 
            @Nullable DiagnosticListener<S> diagListener) {

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
        JavacMessages.instance(context).add(Strings.messagesJML); 
        // These register JML versions of the various tools.  These essentially
        // register factories: no actual instances are created until 
        // instance(context) is called on the particular tool.  Creating instances
        // may trigger a cascade of tool instance generation, which can create
        // tools (such as the Log) before the Options are processed and can
        // trigger some circular dependencies in the constructors of the various
        // tools.
        // Any initialization of these tools that needs to be done based on 
        // options should be performed in setupOptions() in this class.
        JmlSpecs.preRegister(context); // registering the specifications repository
        JmlFactory.preRegister(context); // registering a Jml-specific factory from which to generate JmlParsers
        JmlScanner.JmlFactory.preRegister(context); // registering a Jml-specific factory from which to generate JmlScanners
        JmlTree.Maker.preRegister(context); // registering a JML-aware factory for generating JmlTree nodes
        JmlCompiler.preRegister(context);
        JmlEnter.preRegister(context);
        JmlResolve.preRegister(context);
        JmlFlow.preRegister(context);
        JmlMemberEnter.preRegister(context);
        JmlTypes.preRegister(context);
        JmlAttr.preRegister(context);  // registering a JML-aware type checker
        JmlCheck.preRegister(context);
        JmlPretty.preRegister(context);
        Extensions.register(context);
    }
    
    /** This is overridden so that serious internal bugs are reported as OpenJML
     * rather than Javac bugs.
     */
    // @Override
    protected void bugMessage(Throwable ex) {
        out.println("Internal JML bug - please report.  Build" + JavaCompiler.version());
        ex.printStackTrace(out);
    }
    
    
    // EXTERNAL API FOR PROGRAMATIC ACCESS TO JML COMPILER INTERNALS
    
    /** This method initializes the Options.instance(context) instance of
     * Options class. If the options argument is not null, its content is used
     * to initialize Options.instance(context); if options is null, then
     * Options.instance(context) is initialized by reading
     * the options specified in the environment (System properties +
     * openjml properties files). Then the specified args are processed to make any 
     * further adjustments to the options. Any errors are reported through the
     * log mechanism. Any non-options in the args list (e.g. files) are 
     * warned about and ignored. 
     */
    public void initializeOptions(@Nullable Options options, @NonNull String... args) {
        Options opts = Options.instance(context);
        setOptions(opts);
        if (options == null) {
            filenames = new TreeSet<File>();
            classnames = new ListBuffer<String>();
            coreDefaultOptions(opts);
            Properties properties = Utils.findProperties(context);
            for (Map.Entry<Object,Object> p : properties.entrySet()) {
                Object o = p.getKey();
                if (!(o instanceof String)) {
                    Log.instance(context).warning("jml.ignoring.non.string.key", o.getClass());
                    continue;
                }
                String key = (String)o;
                Object value = p.getValue();
                if (!(value instanceof String)) {
                    Log.instance(context).warning("jml.ignoring.non.string.value", o.getClass(),key);
                    continue;
                }
                String v = (String)value;
                if (key.startsWith(Strings.optionPropertyPrefix)) {
                    String rest = key.substring(Strings.optionPropertyPrefix.length());
                    if (v.equals("true")) value = "";
                    else if (v.equals("false")) value  = null;
                    rest = "-" + rest;
                    opts.put(rest, v);
                } else if (key.startsWith("openjml")) {
                    opts.put(key,v);
                } else if (key.startsWith("org.openjml")) {
                    opts.put(key,v);
                } else {
                    opts.put(key,v);
                }
            }

        } else {
            opts.putAll(options);
        }

        if (args != null && args.length > 0) try {
            Collection<File> files = processArgs(CommandLine.parse(args));
            if (files != null && !files.isEmpty()) {
                Log.instance(context).warning("jml.ignore.extra.material",files.iterator().next().getName());
            }
        } catch (java.io.IOException e) {
            Log.instance(context).error("jml.process.args.exception", e.toString());
        }
    }
    
    /** Sets default initial options to the Options instance that is the 
     * argument (does not change the compilation context Options directly);
     * edit this method to set any defaults that would not be set by other
     * means.
     */
    protected void coreDefaultOptions(Options opts) {
        opts.put(JmlOption.LOGIC.optionName(), "AUFLIA");
        opts.put(JmlOption.NOPURITYCHECK.optionName(), "");
    }
    
    /** Adds additional options to those already present (which may change 
     * previous settings). */
    public void addOptions(String... args) {
        processArgs(args);
    }
    
    /** Adds a custom option (not checked as a legitimate command-line option);
     * may have an argument after a = symbol */
    public void addUncheckedOption(String arg) {
        int k = arg.indexOf('=');
        if (k == -1) {
            Options.instance(context).put(arg,"");
        } else {
            String value = arg.substring(k+1);
            if (value.equals("false")) value = null;
            Options.instance(context).put(arg.substring(0,k),value);
        }
    }
    
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
        // bin directories directly. We make sure that we get both of them.
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
                    if (new File(s).exists()) jmlruntimePath = s;

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
                        if (new File(s).exists() && !s.equals(jmlruntimePath)) jmlruntimePath = jmlruntimePath + java.io.File.pathSeparator + s;
                    }
                } catch (Exception e) {
                    // Just skip
                }
            }
        }

        if (jmlruntimePath != null) {
            if (Utils.instance(context).jmlverbose >= Utils.JMLVERBOSE) 
                Log.instance(context).noticeWriter.println("Using internal runtime " + jmlruntimePath);
            String cp = Options.instance(context).get("-classpath");
            if (cp == null) cp = System.getProperty("java.class.path");
            cp = cp==null ? jmlruntimePath : (cp + java.io.File.pathSeparator + jmlruntimePath);
            Options.instance(context).put("-classpath",cp);
            if (Utils.instance(context).jmlverbose >= Utils.JMLVERBOSE) 
                Log.instance(context).noticeWriter.println("Classpath: " + Options.instance(context).get("-classpath"));
        } else {
            Log.instance(context).warning("jml.no.internal.runtime");
        }
    }
    
    /** An empty array used simply to avoid repeatedly creating one. */
    private static final @NonNull String[] emptyArgs = new String[]{};
    
    /** Returns a reference to the API's compilation context. */
    public @Nullable Context context() {
        return context;
    }
    
    /** An Enum type that gives a choice of various tools to be executed. */
    public static enum Cmd { CHECK("check"), ESC("esc"), RAC("rac"), JMLDOC("doc"), COMPILE("compile");
        String name;
        public String toString() { return name; }
        private Cmd(String name) { this.name = name; }
        };


}
