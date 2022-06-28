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
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import javax.annotation.processing.Processor;
import javax.tools.DiagnosticListener;
import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.annotation.Pure;
import org.jmlspecs.openjml.esc.MethodProverSMT;
import org.jmlspecs.openjml.proverinterface.IProverResult;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlCheck;
import com.sun.tools.javac.comp.JmlDeferredAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlFlow;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.main.CommandLine;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.main.JmlCompiler;
import com.sun.tools.javac.main.Option;
import com.sun.tools.javac.parser.JmlFactory;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCNewArray;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JavacMessages;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;

/**
 * This class is the main entry point for the JML tool. It uses the javac
 * compiler, but overrides some of the functionality here in order to register
 * tools for the compiler to use that are extensions with JML functionality of
 * the usual tools. Also the handling of JML-specific options is initialized
 * here. For programmatic access to the facilities of openjml, use the methods
 * of the API class.
 *
 * <P>
 * NOTE ON OUTPUT:
 * <P>
 * Output is produced by this program in a variety of ways, through mechanisms
 * that enable it to be captured for various means of display by the wrapping
 * UI.
 * <P>
 * Log - there is one Log instance per context, retrieved by
 * Log.instance(context). It has a number of writers:
 * <UL>
 * <LI>log.noticeWriter - general information, often guarded by tests of the
 * verbose flag
 * <LI>log.warnWriter - for compiler/JML/ESC warnings
 * <LI>log.errWriter - for compiler/JML/ESC errors
 *
 * <LI>The IProgressReporter - this is used for messages that report progress
 * back to the UI (textual or graphic).
 *
 * <LI>Diagnostic listener - this listens for warnings and errors, as written to
 * log.warnWriter and log.errWriter.
 * </UL>
 * <P>
 * The output of the log goes to the registered instance of Log [ by
 * context.put(logKey, new Log(...)) ]. If no log is registered, a default log
 * is used, which sends all channels of information to the PrintWriter
 * registered under context.put(outKey,...). There is a constructor for a Log
 * that allows the notice, warning and error output to be directed to different
 * PrintWriters.
 * <P>
 * If there is no DiagnosticListener registered, the warning and error outputs
 * are treated as described above. If there is a DiagnosticListener, then the
 * diagnostic output is sent to that listener instead.
 * <P>
 * For OpenJML:
 * <UL>
 * <LI>command-line tool: no diagnostic listener is defined; Log output can be
 * directed to either System.out or System.err by a command-line option
 * <LI>Eclipse: a diagnostic listener is defined that converts warnings and
 * errors into Eclipse markers; Log output is captured by a PrintWriter that
 * directs the output to the Eclipse console.
 * </UL>
 * <P>
 * Progress Reporting: Various tools within OpenJML report progress (e.g. as
 * individual files are parsed). The progress messages are tiered:
 * <UL>
 * <LI>level 1: low volume, appropriate for text and normal output
 * <LI>level 2: transient progress messages
 * <LI>level 3: verbose only
 * </UL>
 * A tool can receive these progress reports by registering as a delegate via
 *
 * TODO - check and complete the documentation above
 */
public class Main extends com.sun.tools.javac.main.Main {

    public static final int                                      EXIT_CANCELED = -1;

    /**
     * The compilation unit context associated with this instance of Main (for
     * the programmatic API); for the command-line API it is simply the most
     * recent value of the context, and is used that way in testing.
     */
    protected Context                                            context;

    public boolean                                               canceled      = false;

    static public java.util.function.Supplier<IProgressListener> progressListener;

    /**
     * The diagListener provided when an instance of Main is constructed. The
     * listener will be notified when any diagnostic is generated.
     */
    @Nullable
    protected DiagnosticListener<? extends JavaFileObject>       diagListener;

    /**
     * Instances of this class are used to abruptly terminate long-running JML
     * operations.
     *
     * @author David R. Cok
     */
    public static class JmlCanceledException extends RuntimeException {
        private static final long serialVersionUID = 1L;

        public JmlCanceledException(final String message) {
            super(message);
        }
    }

    // TODO - review use of and document these progress reporters; perhaps move
    // them

    public DelegatingProgressListener progressDelegator = new DelegatingProgressListener();

    /**
     * An interface for progress information; the implementation reports
     * progress by calling report(...); clients will receive notification of
     * progress events by implementing this interface and registering the
     * listener with progressDelegate.setDelegate(IProgressReporter).
     *
     */
    public static interface IProgressListener {
        void setContext(Context context);

        boolean report(int level, String message);

        void worked(int ticks);
    }

    /**
     * The compilation Context only allows one instance to be registered for a
     * given class and that instance cannot be changed. So we register an
     * instance of DelegatingProgressListener; then we can change the delegate
     * registered in DelegatingProgressListener to our heart's content.
     * <P>
     * This class is a Listener that simply passes on reports to its own
     * listeners. It currently only allows one delegate.
     */
    static public class DelegatingProgressListener
            implements IProgressListener {
        /** The delegate to which this class passes reports. */
        private IProgressListener delegate;

        /**
         * The callback that is called when the application has progress to
         * report
         */
        @Override
        public boolean report(final int level, final String message) {
            if (delegate != null) {
                return delegate.report(level, message);
            }
            return false;
        }

        @Override
        public void worked(final int ticks) {
            if (delegate != null) {
                delegate.worked(ticks);
            }
        }

        /** Returns true if there is a listener. */
        @Pure
        public boolean hasDelegate() {
            return delegate != null;
        }

        /** Sets a listener; may be null to erase a listener. */
        public void setDelegate(@Nullable final IProgressListener d) {
            delegate = d;
        }

        /** Sets the compilation context (passed on to listeners) */
        @Override
        public void setContext(final Context context) {
            if (delegate != null) {
                delegate.setContext(context);
            }
        }
    }

    /**
     * This class is a progress listener that prints the progress messages to a
     * given OutputStream.
     */
    public static class PrintProgressReporter implements IProgressListener {
        protected PrintWriter pw;

        protected Context     context;

        public PrintProgressReporter(final Context context,
                final OutputStream out) {
            pw = new PrintWriter(out);
            this.context = context;
        }

        public PrintProgressReporter(final Context context,
                final PrintWriter w) {
            pw = w;
            this.context = context;
        }

        @Override
        public boolean report(final int level, final String message) {
            if (level <= 1 || (context != null && Utils
                    .instance(context).jmlverbose >= Utils.JMLVERBOSE)) {
                pw.println(message);
                pw.flush();
            }
            return false;
        }

        @Override
        public void worked(final int ticks) {}

        @Override
        public void setContext(final Context context) {
            this.context = context;
        }
    }

    /**
     * Construct a compiler instance; all options are set to values read from
     * the environment. Errors go to stderr.
     */
    // @edu.umd.cs.findbugs.annotations.SuppressWarnings("NM_SAME_SIMPLE_NAME_AS_SUPERCLASS")
    public Main() throws java.io.IOException {
        this(Strings.applicationName, new PrintWriter(System.err, true), null,
                null);
    }

    /**
     * Construct an initialized compiler instance; all options are set according
     * to values from the options and args arguments.
     *
     * @param applicationName
     *            the name to use for the application
     * @param out
     *            the PrintWriter to which to send information and error
     *            messages
     * @param diagListener
     *            the listener to receive problem and warning reports
     * @param options
     *            the default set of options (adjusted by the command-line
     *            args); if null, then default values are read from the
     *            environment
     * @param args
     *            command-line options
     */
    public Main(/* @ non_null */final String applicationName,
            /* @ non_null */final PrintWriter out,
            @Nullable final DiagnosticListener<? extends JavaFileObject> diagListener,
            @Nullable final Options options, final String... args)
            throws java.io.IOException {
        super(applicationName, out);
        initialize(out, diagListener, options, args);
    }

    protected void initialize(/* @ non_null */final PrintWriter out,
            @Nullable final DiagnosticListener<? extends JavaFileObject> diagListener,
            @Nullable final Options options, String... args) {
        check(); // Aborts if the environment does not support OpenJML
        this.out = out;
        this.diagListener = diagListener;
        context = new Context();
        log = uninitializedLog();
        JavacFileManager.preRegister(context); // can't create it until Log has
                                               // been set up
        register(context);
        if (args == null) {
            args = emptyArgs;
        }
        initializeOptions(options, args); // Creates a new Options instance and
                                          // initializes it per the arguments
    }

    public PrintWriter out() {
        return out;
    }

    /**
     * Checks that the tool is being run with an adequate JVM - and exits
     * abruptly if not
     */
    public void check() {
        final javax.lang.model.element.ElementKind[] kinds = javax.lang.model.element.ElementKind
                .values();
        if (kinds[kinds.length
                - 1] == javax.lang.model.element.ElementKind.OTHER) {
            System.out.println(
                    "OpenJML is being run with a Java 6 or earlier VM, which is not supported.");
            System.exit(99);
        }
    }

    /**
     * The external entry point - simply calls execute(args) and exits with the
     * exit code returned.
     *
     * @param args
     *            the command-line arguments
     */
    // @ requires args != null && \nonnullelements(args);
    public static void main(final String[] args) throws Exception {
        if (args.length > 0 && args[0].equals("-Xjdb")) {
            // Note: Copied directly from com.sun.tools.javac.Main and not
            // tested
            final String[] newargs = new String[args.length + 2];
            final Class<?> c = Class
                    .forName("com.sun.tools.example.debug.tty.TTY");
            final Method method = c.getDeclaredMethod("main",
                    new Class[] { args.getClass() });
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
    final public static String helpOption   = "-help";

    /** The option string for running jmldoc */
    @NonNull
    final public static String jmldocOption = "-doc";

    /**
     * Invokes the compiler on the given command-line arguments; errors go to
     * stdout.
     *
     * @param args
     *            the command-line arguments
     * @return the exit code, as returned to the shell - 0 is success
     */
    // @ requires args != null && \nonnullelements(args);
    public static int execute(final String[] args) {
        if (args != null) {
            for (final String a : args) {
                if (jmldocOption.equals(a)) {
                    return 4; // FIXME -
                              // org.jmlspecs.openjml.jmldoc.Main.execute(args);
                }
            }
        }
        return execute(args, false); // The boolean: true - errors to stdErr,
                                     // false - errors to stdOut
    }

    /**
     * A programmatic interface to the compiler that returns the exit code, but
     * does not itself call System.exit. [This is called execute rather than
     * compile as in com.sun.tools.javac.Main because we also have to override
     * com.sun.tools.javac.main.Main.compile ]
     *
     * @param args
     *            the command-line arguments
     * @param useStdErr
     *            if true, errors go to stderr; if false they go to stdout
     * @return the exit code as sent to the shell (0 is success)
     */
    // @ requires args != null && \nonnullelements(args);
    public static int execute(final String[] args, final boolean useStdErr) {
        return execute(
                new PrintWriter(useStdErr ? System.err : System.out, true),
                null, null, args);
    }

    /**
     * Static method to do the work of Main.
     *
     * @param writer
     *            where to write output that is not sent to the
     *            diagnosticListener
     * @param diagListener
     *            a listener to hear any compiler diagnostics produced
     * @param options
     *            the default set of options to use (including system
     *            properties)
     * @param args
     *            the command-line arguments
     * @return the exit code
     */
    public static int execute(@NonNull final PrintWriter writer,
            @Nullable final DiagnosticListener<? extends JavaFileObject> diagListener,
            @Nullable final Options options, @NonNull final String[] args) {
        int errorcode = com.sun.tools.javac.main.Main.Result.ERROR.exitCode; // 1
        try {
            if (args == null) {
                uninitializedLog().error("jml.main.null.args",
                        "org.jmlspecs.openjml.Main.main");
                errorcode = com.sun.tools.javac.main.Main.Result.CMDERR.exitCode; // 2
            } else {
                // We have to interpret the -java option before we start
                // the compiler (which does the normal option processing).
                // Since this is rare, we'll require that it be the first
                // option.
                final boolean useJavaCompiler = args.length > 0 && args[0]
                        .equals(JmlOption.USEJAVACOMPILER.optionName());
                if (useJavaCompiler) {
                    final String[] newargs = new String[args.length - 1];
                    System.arraycopy(args, 1, newargs, 0, newargs.length);
                    if (options != null) {
                        uninitializedLog().warning("jml.ignoring.options");
                    }
                    errorcode = com.sun.tools.javac.Main.compile(newargs);
                } else {
                    // We create an instance of main through which to call the
                    // actual compile method. Note though that the compile
                    // method
                    // does its own initialization (in the super class). Thus
                    // the
                    // context and any option processing in the constructor call
                    // are thrown away. That is also why we do the hack of
                    // saving
                    // the options to a private variable, just to be able to
                    // apply them in the compile() call below.
                    final Main compiler = new Main(Strings.applicationName,
                            writer, diagListener, options, emptyArgs);
                    savedOptions = Options.instance(compiler.context());
                    // The following line does an end-to-end compile, in a fresh
                    // context
                    errorcode = compiler.compile(args).exitCode; // context and
                                                                 // new options
                                                                 // are created
                                                                 // in here

                    if (// errorcode > Result.CMDERR.exitCode ||
                    Utils.instance(compiler
                            .context()).jmlverbose >= Utils.JMLVERBOSE) {
                        writer.println("ENDING with exit code " + errorcode);
                    }
                }
            }
        } catch (final JmlCanceledException e) {
            // Error message already issued
            errorcode = Result.CMDERR.exitCode;
        } catch (final Exception e) {
            // Most exceptions are caught prior to this, so this will happen
            // only for the
            // most catastrophic kinds of failure such as failures to initialize
            // properly. (You can test this by programmatically throwing an
            // exception in the try
            // block above.)
            uninitializedLog().error("jml.toplevel.exception", e);
            e.printStackTrace(System.err);
            errorcode = com.sun.tools.javac.main.Main.Result.SYSERR.exitCode; // 3
        }
        return errorcode;
    }

    /**
     * Executes the given command-line, but within the same instance of Main;
     * the instance of Main is completely reinitialized, with a new context.
     *
     * @param writer
     * @param diagListener
     * @param options
     * @param args
     * @return
     */
    public int executeNS(@NonNull final PrintWriter writer,
            @Nullable final DiagnosticListener<? extends JavaFileObject> diagListener,
            @Nullable final Options options, @NonNull final String[] args) {
        int errorcode = com.sun.tools.javac.main.Main.Result.ERROR.exitCode; // 1
        try {
            if (args == null) {
                uninitializedLog().error("jml.main.null.args",
                        "org.jmlspecs.openjml.Main.main");
                errorcode = com.sun.tools.javac.main.Main.Result.CMDERR.exitCode; // 2
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
                // The following line does an end-to-end compile, in a fresh
                // context
                errorcode = compile(args).exitCode; // context and new options
                                                    // are created in here
                if (errorcode > Result.CMDERR.exitCode || Utils
                        .instance(context()).jmlverbose > Utils.PROGRESS) {
                    writer.println("ENDING with exit code " + errorcode); // TODO
                                                                          // -
                                                                          // not
                                                                          // sure
                                                                          // we
                                                                          // want
                                                                          // this
                                                                          // -
                                                                          // but
                                                                          // we'll
                                                                          // need
                                                                          // to
                                                                          // change
                                                                          // the
                                                                          // tests
                }
            }
        } catch (final JmlCanceledException e) {
            // Error message already issued
            errorcode = EXIT_CANCELED; // Indicates being cancelled
        } catch (final Exception e) {
            // Most exceptions are caught prior to this, so this will happen
            // only for the
            // most catastrophic kinds of failure such as failures to initialize
            // properly. (You can test this by programmatically throwing an
            // exception in the try
            // block above.)
            uninitializedLog().error("jml.toplevel.exception", e);
            e.printStackTrace(System.err);
            errorcode = com.sun.tools.javac.main.Main.Result.SYSERR.exitCode; // 3
        }
        return errorcode;
    }

    private IAPI.IProofResultListener prl;

    public int executeNS(@NonNull final PrintWriter writer,
            @Nullable final DiagnosticListener<? extends JavaFileObject> diagListener,
            final IAPI.IProofResultListener prListener,
            @Nullable final Options options, @NonNull final String[] args) {
        int errorcode = com.sun.tools.javac.main.Main.Result.ERROR.exitCode; // 1
        try {
            if (args == null) {
                uninitializedLog().error("jml.main.null.args",
                        "org.jmlspecs.openjml.Main.main");
                errorcode = com.sun.tools.javac.main.Main.Result.CMDERR.exitCode; // 2
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
                setProofResultListener(prListener); // FIXME - this is wiped
                                                    // away in the compile()
                                                    // below, along with the
                                                    // initialization just
                                                    // above???
                prl = prListener; // FIXME - necessitating this end run with prl

                // The following lines do an end-to-end compile, in a fresh
                // context
                errorcode = compile(args).exitCode; // context and new options
                                                    // are created in here
                if (errorcode > Result.CMDERR.exitCode || Utils
                        .instance(context()).jmlverbose > Utils.PROGRESS) {
                    writer.println("ENDING with exit code " + errorcode); // TODO
                                                                          // -
                                                                          // not
                                                                          // sure
                                                                          // we
                                                                          // want
                                                                          // this
                                                                          // -
                                                                          // but
                                                                          // we'll
                                                                          // need
                                                                          // to
                                                                          // change
                                                                          // the
                                                                          // tests
                }
            }
        } catch (final JmlCanceledException e) {
            // Error message already issued
            errorcode = EXIT_CANCELED; // Indicates being cancelled
        } catch (final Exception e) {
            // Most exceptions are caught prior to this, so this will happen
            // only for the
            // most catastrophic kinds of failure such as failures to initialize
            // properly. (You can test this by programmatically throwing an
            // exception in the try
            // block above.)
            uninitializedLog().error("jml.toplevel.exception", e);
            e.printStackTrace(System.err);
            errorcode = com.sun.tools.javac.main.Main.Result.SYSERR.exitCode; // 3
        }
        return errorcode;
    }

    /**
     * This is a convenience method to initialize just enough that we can log an
     * error or warning message for issues that arise before the compiler is
     * properly initialized.
     *
     * @return a Log instance to use
     */
    static protected Log uninitializedLog() {
        final Context context = new Context();
        // This is a temporary context just for logging error messages when
        // overall initialization fails.
        // It is not the one used for the options and compilation
        JavacMessages.instance(context).add(Strings.messagesJML);
        return Log.instance(context);
    }

    /**
     * Just used to communicate a set of options from execute(...) to
     * compile(...), since it cannot be passed through the super call.
     */
    static private Options savedOptions = null;

    /**
     * This method is overwritten so that the JML compiler can register its own
     * tools for the various phases. This fits in just the right place in the
     * compiler initialization and invocation sequence, but I'm not sure how
     * fragile it is with updates and reorganizations of the code.
     *
     * @param args
     *            the command-line arguments
     * @param context
     *            the compilation context to use
     * @return the value to use as the command-line exit code
     */
    // @ requires args != null && \nonnullelements(args);
    // @ requires context != null;
    // @Override
    // public int compile(String[] args, Context context) {

    @Override
    public Main.Result compile(final String[] args, final Context context,
            final List<JavaFileObject> fileObjects,
            final Iterable<? extends Processor> processors) {

        this.context = context;
        register(context);
        setProofResultListener(prl);
        initializeOptions(savedOptions, null);
        if (args.length == 0
                && (processors == null || !processors.iterator().hasNext())
                && fileObjects.isEmpty()) {
            help();
            return Result.CMDERR;
        }
        // Note that the Java option processing happens in compile method call
        // below.
        // Those options are not read at the time of the register call,
        // but the register call has to happen before compile is called.
        canceled = false;
        Main.Result exit = super.compile(args, context, fileObjects,
                processors);
        // if (Options.instance(context).get(helpOption) != null) {
        // helpJML(out);
        // }
        if (canceled) {
            exit = Result.CANCELLED;
        }
        return exit;
    }

    @Override
    protected void help() {
        Option.HELP.process(optionHelper, "-help");
        final PrintWriter p = optionHelper.getLog()
                .getWriter(WriterKind.NOTICE);
        helpJML(p);
        JmlOptions.instance(context).put(Option.HELP, "");
    }

    /** This is a utility method to print out all of the JML help information */
    protected void helpJML(final PrintWriter w) {
        w.print(JmlOption.helpInfo());
        w.flush();
    }

    /**
     * This method scans the input sequence of command-line arguments,
     * processing any that are recognized as JML options. Those options are
     * registered in the Options map. The String[] returned contains all of the
     * command-line arguments in the input, omitting those recognized as JML
     * options.
     *
     * @param args
     *            the input command-line arguments
     * @param options
     *            the Options map in which recognized options are recorded
     * @return all arguments not recognized as JML
     */
    // @ requires \nonnullelements(args);
    // @ ensures \result != null && \nonnullelements(\result);
    String[] processJmlArgs(@NonNull final String[] args,
            @NonNull final Options options, final ListBuffer<File> jmlfiles) {
        final java.util.List<String> newargs = new ArrayList<String>();
        final java.util.List<String> files = new ArrayList<String>();
        int i = 0;
        while (i < args.length) {
            i = processJmlArg(args, i, options, newargs, files);
        }
        // newargs.addAll(computeDependencyClosure(files));
        newargs.addAll(files);
        File f;
        final Iterator<String> iter = newargs.iterator();
        while (iter.hasNext()) {
            final String s = iter.next();
            if (s.endsWith(Strings.specsSuffix) && (f = new File(s)).exists()) {
                jmlfiles.add(f);
                iter.remove();
            }
        }
        return newargs.toArray(new String[newargs.size()]);
    }

    // TODO _ document
    public java.util.List<String> computeDependencyClosure(
            final java.util.List<String> files) {
        // fill out dependencies
        final java.util.List<String> newargs = new ArrayList<String>();
        // Dependencies d = Dependencies.instance(context);
        final Set<String> done = new HashSet<String>();
        final java.util.List<String> todo = new LinkedList<String>();
        // JavacFileManager jfm =
        // (JavacFileManager)context.get(JavaFileManager.class);; // FIXME -
        // this causes Lint to be initialized before the Java options are
        // registered
        for (final String s : files) {
            // FIXME - don't hardcode this list of suffixes here
            if (Utils.instance(context).hasValidSuffix(s)) {
                todo.add(s);
            }
        }
        while (!todo.isEmpty()) {
            final String o = todo.remove(0);
            if (done.contains(o)) {
                continue;
            }
            done.add(o);
            // if (o.getName().endsWith(".java")) newargs.add("C:" +
            // o.toUri().getPath()); // FIXME - a hack to get the full path
            if (o.endsWith(".java")) {
                newargs.add(o); // FIXME FOR REAL - this
                                // needs to be made sane
                // Set<JavaFileObject> affected = d.getAffected(o);
                // if (affected != null) {
                // todo.addAll(affected);
                // //Log.instance(context).noticeWriter.println("Adding " +
                // affected.size() + " dependencies for " + o);
                // }
            }
        }
        return newargs;
    }

    /**
     * Processes a single JML command-line option and any arguments.
     *
     * @param args
     *            the full array of command-line arguments
     * @param i
     *            the index of the argument to be processed
     * @param options
     *            the options object to be adjusted as JML options are found
     * @param remainingArgs
     *            any arguments that are not JML options
     * @return the index of the next argument to be processed
     */
    // @ requires \nonnullelements(args);
    // @ requires (* elements of remainingArgs are non-null *);
    // @ requires 0<= i && i< args.length;
    // @ ensures \result > i;
    int processJmlArg(@NonNull final String[] args, int i,
            @NonNull final Options options,
            /* @ non_null */ final java.util.List<String> remainingArgs,
            /* @ non_null */ final java.util.List<String> files) {
        String res = "";
        String s = args[i++];
        if (s == null || s.isEmpty()) {
            return i; // For convenience, allow but
                      // ignore null or empty
                      // arguments
        }

        if (s.length() > 1 && s.charAt(0) == '"'
                && s.charAt(s.length() - 1) == '"') {
            s = s.substring(1, s.length() - 1);
        }

        boolean negate = false;
        if (s.startsWith("-no-")) {
            negate = true;
            s = s.substring("-no".length());
        }
        IOption o = JmlOption.find(s);
        while (o != null && o.synonym() != null) {
            s = o.synonym();
            if (s.startsWith("-no-")) {
                negate = !negate;
                s = s.substring("-no".length());
            }
            o = JmlOption.find(s);
        }
        if (o == null) {
            final int k = s.indexOf('=');
            if (k != -1) {
                res = s.substring(k + 1, s.length());
                s = s.substring(0, k);
                o = JmlOption.find(s);
                if (o == null) {
                    // This is not a JML option. Might be misspelled or it might
                    // be a JDK option with an =, which JDK does not support.
                    log.warning("jml.message", "Ignoring command-line argument "
                            + args[i - 1]
                            + " which is either misspelled or is a JDK option using = to set an argument (which JDK does not support)");
                } else if (res.isEmpty()) {
                    // JML option with a naked = sign
                    final Object def = o.defaultValue();
                    res = def == null ? null : def.toString();

                } else {
                    if (o.hasArg()) {
                    } else if ("false".equals(res)) {
                        negate = true;
                    } else if ("true".equals(res)) {
                        res = "";
                    } else {
                        res = "";
                        Log.instance(context).warning("jml.ignoring.parameter",
                                s);
                    }
                }
            }
        } else if (!negate && o.hasArg()) {
            if (o instanceof JmlOption
                    && ((JmlOption) o).enabledDefault != null) {
                res = ((JmlOption) o).enabledDefault;
            } else if (i < args.length) {
                res = args[i++];
                if (res != null && res.length() > 1 && res.charAt(0) == '"'
                        && s.charAt(res.length() - 1) == '"') {
                    res = res.substring(1, res.length() - 1);
                }

            } else {
                res = "";
                Log.instance(context).warning("jml.expected.parameter", s);
            }
        }
        if (o == null) {
            if (s.equals("-help")) {
                help();
            } else {
                remainingArgs.add(s);
            }
        } else if (JmlOption.DIR.optionName().equals(s)
                || JmlOption.DIRS.optionName().equals(s)) {
            final java.util.List<File> todo = new LinkedList<File>();
            todo.add(new File(res));
            if (JmlOption.DIRS.optionName().equals(s)) {
                while (i < args.length && (res = args[i]).length() > 0
                        && res.charAt(0) != '-') {
                    todo.add(new File(res));
                    i++;
                }
            }
            final Utils utils = Utils.instance(context);
            while (!todo.isEmpty()) {
                final File file = todo.remove(0);
                if (file.isDirectory()) {
                    final File[] fileArray = file.listFiles();
                    // Comparator is intentionally reversed, so we push items on
                    // the front of the queue in reverse order
                    Arrays.sort(fileArray, new java.util.Comparator<File>() {
                        @Override
                        public int compare(final File f, final File ff) {
                            return (f.isFile() && ff.isDirectory()) ? 1
                                    : (ff.isFile() && f.isDirectory()) ? -1
                                            : -f.getPath().compareToIgnoreCase(
                                                    ff.getPath());
                        }
                    });
                    for (final File ff : fileArray) {
                        todo.add(0, ff);
                    }
                } else if (file.isFile()) {
                    final String ss = file.toString();
                    if (utils.hasJavaSuffix(ss)) {
                        files.add(ss); // FIXME - if we
                                       // allow .jml
                                       // files on the
                                       // command line,
                                       // we have to
                                       // guard against
                                       // parsing them
                                       // twice
                    }
                } else {
                    try {
                        final String glob = file.toString();
                        final PathMatcher pathMatcher = FileSystems.getDefault()
                                .getPathMatcher("glob:" + glob);

                        final String location = ""; // System.getProperty("user.dir");
                        Files.walkFileTree(Paths.get(location),
                                new SimpleFileVisitor<Path>() {

                                    @Override
                                    public FileVisitResult visitFile(
                                            final Path path,
                                            final BasicFileAttributes attrs)
                                            throws IOException {
                                        if (pathMatcher.matches(path)) {
                                            todo.add(path.toFile());
                                        }
                                        return FileVisitResult.CONTINUE;
                                    }

                                    @Override
                                    public FileVisitResult visitFileFailed(
                                            final Path file,
                                            final IOException exc)
                                            throws IOException {
                                        return FileVisitResult.CONTINUE;
                                    }
                                });
                    } catch (final Exception e) {
                        // FIXME - warn about exception
                        System.out.println(e);
                        // continue
                    }

                }
            }
        } else {
            if (negate) {
                if (o.defaultValue() instanceof Boolean) {
                    JmlOption.setOption(context, o, false);
                } else if (o.defaultValue() == null) {
                    options.put(s, null);
                } else {
                    options.put(s, o.defaultValue().toString());
                }
            } else {
                if (o.defaultValue() instanceof Boolean) {
                    JmlOption.setOption(context, o, true);
                } else {
                    options.put(s, res);
                }
            }
        }

        if (o != null && o.equals(JmlOption.PROPERTIES)) {
            final Properties properties = System.getProperties();
            final String file = JmlOption.value(context, JmlOption.PROPERTIES);
            if (file != null && !file.isEmpty()) {
                try {
                    Utils.readProps(properties, file);
                } catch (final java.io.IOException e) {
                    Log.instance(context).getWriter(WriterKind.NOTICE)
                            .println("Failed to read property file " + file); // FIXME
                                                                              // -
                                                                              // review
                }
                setPropertiesFileOptions(options, properties);
            }
        }
        return i;
    }

    /**
     * This method is called after options are read, but before compilation
     * actually begins; requires tools to be registered, at least Log and
     * Options here any additional option checking or processing can be
     * performed.
     */
    // This should be able to be called without difficulty whenever any option
    // is changed
    public boolean setupOptions() {
        // CAUTION: If tools cache values of options and have their singleton
        // instance created before the options are completely processed, the
        // tool will grab some default version of the option.
        // Crucially, Log does this.

        final Options options = Options.instance(context);
        final Utils utils = Utils.instance(context);

        String t = options.get(JmlOption.JMLTESTING.optionName());
        Utils.testingMode = (t != null && !t.equals("false"));
        final String benchmarkDir = options
                .get(JmlOption.BENCHMARKS.optionName());
        if (benchmarkDir != null) {
            new File(benchmarkDir).mkdir();
        }

        utils.jmlverbose = Utils.NORMAL;

        {
            // Automatically set verboseness to PROGRESS if we are debugging
            // checkFeasibility.
            // So do this determination before we interpret the verboseness
            // option.
            t = options.get(JmlOption.FEASIBILITY.optionName());
            if (t != null) {
                if (t.startsWith("debug")
                        && utils.jmlverbose < Utils.PROGRESS) {
                    utils.jmlverbose = Utils.PROGRESS;
                }
                final int k = t.indexOf(":");
                if (k > 0) {
                    try {
                        MethodProverSMT.startFeasibilityCheck = Integer
                                .parseInt(t.substring(k + 1));
                    } catch (final Exception e) {
                        // continue
                    }
                }
            }
        }

        final String n = JmlOption.VERBOSENESS.optionName().trim();
        String levelstring = options.get(n);
        if (levelstring != null) {
            levelstring = levelstring.trim();
            if (!levelstring.isEmpty()) {
                try {
                    utils.jmlverbose = Integer.parseInt(levelstring);
                } catch (final NumberFormatException e) {
                    Log.instance(context).warning("jml.message",
                            "The value of the " + n + " option or the "
                                    + Strings.optionPropertyPrefix
                                    + n.substring(1)
                                    + " property should be the string representation of an integer: \""
                                    + levelstring + "\"");
                    options.put(n, "1");
                }
            }
        }
        if (options.get("-verbose") != null) {
            // If the Java -verbose option is set, we set -jmlverbose as well
            utils.jmlverbose = Utils.JMLVERBOSE;
        }

        if (utils.jmlverbose >= Utils.PROGRESS) {
            // Why not let the progress listener decide what to print???

            // We check for an existing delegate, because if someone is calling
            // OpenJML programmatically, they may have set one up already.
            // Note, though that this won't undo the setting, if verbosity is
            // turned off.
            // if (!progressDelegator.hasDelegate()) {
            try {
                progressDelegator.setDelegate(
                        progressListener != null ? progressListener.get()
                                : new PrintProgressReporter(context, out));
            } catch (final Exception e) {
                // FIXME - report problem
                // continue without installing a listener
            }
            // }
        } else {
            progressDelegator.setDelegate(null);
        }

        final boolean b = JmlOption.isOption(context,
                JmlOption.USEJAVACOMPILER);
        if (b) {
            Log.instance(context).getWriter(WriterKind.NOTICE).println(
                    // FIXME - change to a warning
                    "The -java option is ignored unless it is the first command-line argument");
        }

        Cmd cmd = Cmd.CHECK; // default
        String val = options.get(JmlOption.COMMAND.optionName());
        try {
            if (val != null) {
                cmd = Cmd.valueOf(val.toUpperCase());
            }
        } catch (final IllegalArgumentException e) {
            Log.instance(context).error("jml.bad.command", val);
            return false;
        }
        utils.cmd = cmd;
        utils.rac = cmd == Cmd.RAC;
        utils.esc = cmd == Cmd.ESC;
        utils.check = cmd == Cmd.CHECK;
        utils.compile = cmd == Cmd.COMPILE;
        utils.infer = cmd == Cmd.INFER;

        /**
         * options for loop invariants inference
         */
        utils.jml2rapid = cmd == Cmd.JML2RAPID;

        val = options.get(JmlOption.ESC_BV.optionName());
        if (val == null || val.isEmpty()) {
            options.put(JmlOption.ESC_BV.optionName(),
                    (String) JmlOption.ESC_BV.defaultValue());
        } else if ("auto".equals(val) || "true".equals(val)
                || "false".equals(val)) {
        } else {
            Log.instance(context).warning("jml.message",
                    "Command-line argument error: Expected 'auto', 'true' or 'false' for -escBV: "
                            + val);
            // Log.instance(context).getWriter(WriterKind.NOTICE).println("Command-line
            // argument error: Expected 'auto', 'true' or 'false' for -escBV: "
            // + val);
            options.put(JmlOption.ESC_BV.optionName(),
                    (String) JmlOption.ESC_BV.defaultValue());
        }

        val = options.get(JmlOption.LANG.optionName());
        if (val == null || val.isEmpty()) {
            options.put(JmlOption.LANG.optionName(),
                    (String) JmlOption.LANG.defaultValue());
        } else if (JmlOption.langPlus.equals(val)
                || JmlOption.langJavelyn.equals(val)
                || JmlOption.langJML.equals(val)) {
        } else {
            Log.instance(context).warning("jml.message",
                    "Command-line argument error: Expected '"
                            + JmlOption.langPlus + "', '" + JmlOption.langJML
                            + "' or '" + JmlOption.langJavelyn + "' for -lang: "
                            + val);
            // Log.instance(context).getWriter(WriterKind.NOTICE).println("Command-line
            // argument error: Expected 'auto', 'true' or 'false' for -escBV: "
            // + val);
            options.put(JmlOption.LANG.optionName(),
                    (String) JmlOption.LANG.defaultValue());
        }

        final String keysString = options.get(JmlOption.KEYS.optionName());
        utils.commentKeys = new HashSet<String>();
        if (keysString != null && !keysString.isEmpty()) {
            final String[] keys = keysString.split(",");
            for (final String k : keys) {
                utils.commentKeys.add(k);
            }
        }

        if (utils.esc) {
            utils.commentKeys.add("ESC");
        }
        if (utils.rac) {
            utils.commentKeys.add("RAC");
        }
        if (JmlOption.langJML
                .equals(JmlOption.value(context, JmlOption.LANG))) {
            utils.commentKeys.add("STRICT");
        }
        utils.commentKeys.add("OPENJML");

        if (JmlOption.isOption(context, JmlOption.INTERNALRUNTIME)) {
            appendRuntime(context);
        }

        final String limit = JmlOption.value(context,
                JmlOption.ESC_MAX_WARNINGS);
        if (limit == null || limit.isEmpty() || limit.equals("all")) {
            utils.maxWarnings = Integer.MAX_VALUE; // no limit is the default
        } else {
            try {
                final int k = Integer.parseInt(limit);
                utils.maxWarnings = k <= 0 ? Integer.MAX_VALUE : k;
            } catch (final NumberFormatException e) {
                // FIXME _ change to an error
                Log.instance(context).getWriter(WriterKind.NOTICE).println(
                        "Expected a number or 'all' as argument for -escMaxWarnings: "
                                + limit);
                utils.maxWarnings = Integer.MAX_VALUE;
            }
        }

        final String v = JmlOption.value(context, JmlOption.SHOW);
        if (v == null) {
            options.put(JmlOption.SHOW.optionName(), "");
        }

        String check = JmlOption.value(context, JmlOption.FEASIBILITY);
        if (check == null || check.isEmpty()
                || check.equals(Strings.feas_default)) {
            options.put(JmlOption.FEASIBILITY.optionName(),
                    check = Strings.feas_defaults);
        }
        if (check.equals(Strings.feas_all)) {
            options.put(JmlOption.FEASIBILITY.optionName(),
                    check = Strings.feas_alls);
        } else if (check.startsWith(Strings.feas_debug)) {
            options.put(JmlOption.FEASIBILITY.optionName(),
                    check = Strings.feas_alls + ",debug");
            if (utils.jmlverbose < Utils.PROGRESS) {
                utils.jmlverbose = Utils.PROGRESS;
            }
        }
        final String badString = Strings.isOK(check);
        if (badString != null) {
            Log.instance(context).getWriter(WriterKind.NOTICE).println(
                    "Unexpected value as argument for -checkFeasibility: "
                            + badString);
        }

        Extensions.register(context);
        JmlSpecs.instance(context).initializeSpecsPath();
        return true;
    }

    /**
     * We override this method in order to process the JML command-line
     * arguments and to do any tool-specific initialization after the
     * command-line arguments are processed.
     */
    // @edu.umd.cs.findbugs.annotations.SuppressWarnings("ST_WRITE_TO_STATIC_FROM_INSTANCE_METHOD")
    @Override
    public Collection<File> processArgs(final String[] oargs,
            final String[] classNames) {
        final Options options = Options.instance(this.context);
        final ListBuffer<File> jmlfiles = new ListBuffer<File>();
        final String[] args = processJmlArgs(oargs, options, jmlfiles);
        if (filenames == null) {
            filenames = new TreeSet<File>(); // needed when
        }
        // called from
        // the API
        final Collection<File> files = super.processArgs(args, classNames);
        if (files != null) {
            files.addAll(jmlfiles);
        }
        // args.addAll(computeDependencyClosure(files));
        if (!setupOptions()) {
            return null;
        }

        final String showOptions = JmlOption.value(context,
                JmlOption.SHOW_OPTIONS);
        if (showOptions != null && !showOptions.equals("none")) { // FIXME -
                                                                  // review and
                                                                  // explain
                                                                  // this
            JmlOption.listOptions(context, showOptions.equals("all"));
        }
        return files;
    }

    /**
     * This registers the JML versions of many of the tools (e.g. scanner,
     * parser, specifications database,...) used by the compiler. They must be
     * registered before the Java versions are invoked, since in most cases
     * singleton values are lazily created. Note also that since tools can only
     * be registered into the context once, circular dependencies can arise from
     * pairs of tools that use each other, if you are not careful.
     *
     * @param context
     *            the compilation context into which to register the tools
     */
    public void register(/* @ non_null @ */ final Context context) {
        this.context = context;// A hack so that context is available in
                               // processArgs()
        if (progressDelegator != null) {
            progressDelegator.setContext(context);
        }
        context.put(IProgressListener.class, progressDelegator);
        context.put(key, this);
        registerTools(context, out, diagListener);
        // Since we can only set a context value once, we create this listener
        // that just delegates to
        // another listener, and then change the delegate when we need to, using
        // setProofResultListener().
        context.put(IAPI.IProofResultListener.class,
                new IAPI.IProofResultListener() {
                    IAPI.IProofResultListener delegate = null;

                    @Override
                    public void reportProofResult(final MethodSymbol sym,
                            final IProverResult res) {
                        if (delegate != null) {
                            delegate.reportProofResult(sym, res);
                        }
                    }

                    @Override
                    public IAPI.IProofResultListener setListener(
                            final IAPI.IProofResultListener listener) {
                        final IAPI.IProofResultListener d = delegate;
                        delegate = listener;
                        return d;
                    }
                });
    }

    public void setProofResultListener(
            final IAPI.IProofResultListener listener) {
        context.get(IAPI.IProofResultListener.class).setListener(listener);
    }

    public static Context.Key<Main> key = new Context.Key<Main>();

    public static Main instance(final Context context) {
        return context.get(key);
    }

    /**
     * Called to register the JML internal tools that replace the tools used in
     * the Java compiler.
     *
     * @param context
     *            the compiler context in which the tools are to be used
     * @param out
     *            the PrintWriter used for error and informational messages
     * @param diagListener
     *            if not null, a listener that will receive reports of warnings
     *            and errors
     */
    public static <S> void registerTools(@NonNull final Context context,
            @NonNull final PrintWriter out,
            @Nullable final DiagnosticListener<S> diagListener) {

        // We register the output writer for the Log first so that it is
        // available if tool registration (or argument processing) needs the
        // Log. However, note that if the Log itself is actually instantiated
        // before
        // Java arguments are read, then it is not set consistently with those
        // options.
        context.put(Log.outKey, out);

        if (diagListener != null) {
            context.put(DiagnosticListener.class, diagListener);
        }

        // These have to be first in case there are error messages during
        // tool registration.
        // registering an additional source of JML-specific error messages
        JavacMessages.instance(context).add(Strings.messagesJML);

        // These register JML versions of the various tools. These essentially
        // register factories: no actual instances are created until
        // instance(context) is called on the particular tool. Creating
        // instances
        // may trigger a cascade of tool instance generation, which can create
        // tools (such as the Log) before the Options are processed and can
        // trigger some circular dependencies in the constructors of the various
        // tools.
        // Any initialization of these tools that needs to be done based on
        // options should be performed in setupOptions() in this class.
        JmlOptions.preRegister(context);
        JmlSpecs.preRegister(context); // registering the specifications
                                       // repository
        JmlFactory.preRegister(context); // registering a Jml-specific factory
                                         // from which to generate JmlParsers
        JmlScanner.JmlFactory.preRegister(context); // registering a
                                                    // Jml-specific factory from
                                                    // which to generate
                                                    // JmlScanners
        JmlTree.Maker.preRegister(context); // registering a JML-aware factory
                                            // for generating JmlTree nodes
        JmlCompiler.preRegister(context);
        JmlEnter.preRegister(context);
        JmlResolve.preRegister(context);
        JmlFlow.preRegister(context);
        JmlMemberEnter.preRegister(context);
        JmlTypes.preRegister(context);
        JmlAttr.preRegister(context); // registering a JML-aware type checker
        JmlCheck.preRegister(context);
        JmlPretty.preRegister(context);
        JmlDeferredAttr.preRegister(context); // registers when created
        // Extensions are registered after options are processed
    }

    /**
     * This is overridden so that serious internal bugs are reported as OpenJML
     * rather than Javac bugs.
     */
    @Override
    protected void bugMessage(final Throwable ex) {
        out.println("Internal JML bug - please report.  Build"
                + JavaCompiler.version());
        ex.printStackTrace(out);
    }

    // EXTERNAL API FOR PROGRAMATIC ACCESS TO JML COMPILER INTERNALS

    public boolean initializingOptions = false;

    /**
     * This method initializes the Options.instance(context) instance of Options
     * class. If the options argument is not null, its content is used to
     * initialize Options.instance(context); if options is null, then
     * Options.instance(context) is initialized by reading the options specified
     * in the environment (System properties + openjml properties files). Then
     * the specified args are processed to make any further adjustments to the
     * options. Any errors are reported through the log mechanism. Any
     * non-options in the args list (e.g. files) are warned about and ignored.
     */
    public void initializeOptions(@Nullable final Options options,
            @NonNull final String... args) {
        initializingOptions = true;
        final Options opts = Options.instance(context);
        setOptions(opts);
        if (options == null) {
            filenames = new TreeSet<File>();
            classnames = new ListBuffer<String>();
            coreDefaultOptions(opts);
            setInitialOptions(opts, args);
            final Properties properties = Utils.findProperties(context);
            setPropertiesFileOptions(opts, properties);
        } else {
            opts.putAll(options);
        }

        if (args != null) {
            try { // Do the following even if there are no args,
                  // because other setup is done as well (e.g.
                  // extensions)
                final Collection<File> files = processArgs(
                        CommandLine.parse(args));
                if (files != null && !files.isEmpty()) {
                    Log.instance(context).warning("jml.ignore.extra.material",
                            files.iterator().next().getName());
                }
            } catch (final java.io.IOException e) {
                Log.instance(context).error("jml.process.args.exception",
                        e.toString());
            }
        }
        initializingOptions = false;
    }

    /**
     * Sets options (first argument) from any relevant properties (second
     * argument)
     */
    protected void setPropertiesFileOptions(final Options opts,
            final Properties properties) {
        for (final Map.Entry<Object, Object> p : properties.entrySet()) {
            final Object o = p.getKey();
            if (!(o instanceof String)) {
                Log.instance(context).warning("jml.ignoring.non.string.key",
                        o.getClass());
                continue;
            }
            final String key = (String) o;
            Object value = p.getValue();
            if (!(value instanceof String)) {
                Log.instance(context).warning("jml.ignoring.non.string.value",
                        o.getClass(), key);
                continue;
            }
            final String v = (String) value;
            if (key.startsWith(Strings.optionPropertyPrefix)) {
                String rest = key
                        .substring(Strings.optionPropertyPrefix.length());
                if (v.equals("true")) {
                    value = "";
                } else if (v.equals("false")) {
                    value = null;
                }
                rest = "-" + rest;
                opts.put(rest, v);
            } else if (key.startsWith("openjml")) {
                opts.put(key, v);
            } else if (key.startsWith("org.openjml")) {
                opts.put(key, v);
            } else {
                opts.put(key, v);
            }
        }
    }

    /**
     * Sets default initial options to the Options instance that is the argument
     * (does not change the compilation context Options directly); edit this
     * method to set any defaults that would not be set by other means.
     */
    protected void coreDefaultOptions(final Options opts) {
        opts.put(JmlOption.LOGIC.optionName(), "ALL");
        opts.put(JmlOption.PURITYCHECK.optionName(), null);
    }

    protected void setInitialOptions(final Options opts, final String... args) {
        for (int i = 0; i < args.length; i++) {
            final String s = args[i];
            if (JmlOption.PROPERTIES_DEFAULT.optionName().equals(s)) {
                if (i + 1 < args.length) {
                    opts.put(JmlOption.PROPERTIES_DEFAULT.optionName(),
                            args[i + 1]);
                } else {
                    Log.instance(context).warning("jml.expected.parameter", s);
                }
            }
        }
    }

    /**
     * Adds additional options to those already present (which may change
     * previous settings).
     */
    public void addOptions(final String... args) {
        processArgs(args);
    }

    /**
     * Adds a custom option (not checked as a legitimate command-line option);
     * may have an argument after a = symbol
     */
    public void addUncheckedOption(final String arg) {
        final int k = arg.indexOf('=');
        if (k == -1) {
            Options.instance(context).put(arg, "");
        } else {
            String value = arg.substring(k + 1);
            if (value.equals("false")) {
                value = null;
            }
            Options.instance(context).put(arg.substring(0, k), value);
        }
    }

    protected Name optionName;

    /**
     * Pushes the current options on the option stack (cf. JmlOption), retaining
     * a copy; then adds to the current options using the Options annotation.
     *
     * @param mods
     */
    public void pushOptions(final JCModifiers mods) {
        if (optionName == null) {
            optionName = Names.instance(context)
                    .fromString("org.jmlspecs.annotation.Options");
        }

        ((JmlOptions) JmlOptions.instance(context)).pushOptions();
        final JCAnnotation addedOptionsAnnotation = Utils.instance(context)
                .findMod(mods, optionName);
        if (addedOptionsAnnotation != null) {
            final List<JCExpression> exprs = addedOptionsAnnotation
                    .getArguments();
            final JCExpression rhs = ((JCAssign) exprs.head).rhs;
            final String[] opts = rhs instanceof JCNewArray
                    ? ((JCNewArray) rhs).elems.stream()
                            .map(JCExpression::toString)
                            .collect(Collectors.toList()).toArray(
                                    new String[((JCNewArray) rhs).elems.size()])
                    : rhs instanceof JCLiteral ? new String[] { rhs.toString() }
                            : null;
            addOptions(opts);
            setupOptions(); // Already run
        }
    }

    // FIXME - the options popped and pushed should not be ones that have
    // modifier/annotation equivalents
    // So no nonnullbydefault/nullablebydefault and code-math and spec-math

    /**
     * Pops a set of options off the options stack, making the popped set the
     * current options.
     */
    public void popOptions() {
        ((JmlOptions) JmlOptions.instance(context)).popOptions();
        setupOptions();
    }

    static protected void fixClasspath(final Context context) {
        final String cp = Options.instance(context).get("-classpath");
        if (cp != null) {
            return;
        }

    }

    /**
     * Appends the internal runtime directory to the -classpath option.
     */
    static protected void appendRuntime(final Context context) {

        String jmlruntimePath = null;

        /** This property is just used in testing. */ // TODO - check this
        final String sy = Options.instance(context)
                .get(Strings.defaultRuntimeClassPath);
        if (sy != null) {
            jmlruntimePath = sy;
        }

        // Look for jmlruntime.jar in the classpath itself

        if (jmlruntimePath == null) {
            final URL url = ClassLoader
                    .getSystemResource(Strings.runtimeJarName);
            if (url != null) {
                jmlruntimePath = url.getFile();
                if (jmlruntimePath.startsWith("file:/")) {
                    jmlruntimePath = jmlruntimePath
                            .substring("file:/".length());
                }
            }
        }

        // Otherwise look for something in the same directory as something on
        // the classpath

        final String classpath = System.getProperty("java.class.path");
        if (jmlruntimePath == null) {
            final String[] ss = classpath.split(java.io.File.pathSeparator);
            for (final String s : ss) {
                if (s.endsWith(".jar")) {
                    try {
                        File f = new File(s).getCanonicalFile().getParentFile();
                        if (f != null) {
                            f = new File(f, Strings.runtimeJarName);
                            if (f.isFile()) {
                                jmlruntimePath = f.getPath();
                                break;
                            }
                        }
                    } catch (final IOException e) {
                        // Just skip
                    }
                } else {
                    final File f = new File(new File(s),
                            Strings.runtimeJarName);
                    if (f.isFile()) {
                        jmlruntimePath = f.getPath();
                        break;
                    }
                }
            }
        }

        // The above all presume some variation on the conventional installation
        // of the command-line tool. In the development environment, those
        // presumptions do not hold. So in that case we use the appropriate
        // bin directories directly. We make sure that we get both of them:
        // the annotations and runtime utilties.
        // This also takes care of the case in which the openjml.jar file is in
        // the class path under a different name.

        if (jmlruntimePath == null) {
            URL url = ClassLoader.getSystemResource(
                    Strings.jmlAnnotationPackage.replace('.', '/'));
            if (url != null) {
                try {
                    String s = url.getPath();
                    if (s.startsWith("file:")) {
                        s = s.substring("file:".length());
                    }
                    int b = (s.length() > 2 && s.charAt(0) == '/'
                            && s.charAt(2) == ':') ? 1 : 0;
                    int k = s.indexOf("!");
                    if (k >= 0) {
                        s = s.substring(b, k);
                    } else {
                        s = s.substring(b);
                        s = new File(s).getParentFile().getParentFile()
                                .getParent();
                    }
                    if (new File(s).exists()) {
                        jmlruntimePath = s;
                    }

                    url = ClassLoader.getSystemResource(
                            Strings.jmlSpecsPackage.replace('.', '/'));
                    if (url != null) {
                        s = url.getPath();
                        if (s.startsWith("file:")) {
                            s = s.substring("file:".length());
                        }
                        b = (s.length() > 2 && s.charAt(0) == '/'
                                && s.charAt(2) == ':') ? 1 : 0;
                        k = s.indexOf("!");
                        if (k >= 0) {
                            s = s.substring(b, k);
                        } else {
                            s = s.substring(b);
                            s = new File(s).getParentFile().getParentFile()
                                    .getParent();
                        }
                        if (new File(s).exists() && !s.equals(jmlruntimePath)) {
                            jmlruntimePath = jmlruntimePath
                                    + java.io.File.pathSeparator + s;
                        }
                    }
                } catch (final Exception e) {
                    // Just skip
                }
            }
        }

        if (jmlruntimePath == null) {
            // This is for the case of running the GUI in the development
            // environment
            String srt = System
                    .getProperty(Strings.eclipseSpecsProjectLocation); // FIXME
                                                                       // _
                                                                       // probably
                                                                       // can
                                                                       // replace
                                                                       // this
                                                                       // with
                                                                       // finding
                                                                       // a
                                                                       // plugin
            srt = srt + "/../OpenJML/OpenJML/bin-runtime";
            final File f = new File(srt);
            if (f.exists() && f.isDirectory()) {
                jmlruntimePath = srt;
            }

        }

        if (jmlruntimePath != null) {
            if (Utils.instance(context).jmlverbose >= Utils.JMLVERBOSE) {
                Log.instance(context).getWriter(WriterKind.NOTICE)
                        .println("Using internal runtime " + jmlruntimePath);
            }
            String cp = Options.instance(context).get("-classpath");
            if (cp == null) {
                cp = System.getProperty("java.class.path");
            }
            cp = cp == null ? jmlruntimePath
                    : (cp + java.io.File.pathSeparator + jmlruntimePath);
            Options.instance(context).put("-classpath", cp);
            if (Utils.instance(context).jmlverbose >= Utils.JMLVERBOSE) {
                Log.instance(context).getWriter(WriterKind.NOTICE)
                        .println("Classpath: "
                                + Options.instance(context).get("-classpath"));
            }
        } else if (!Main.instance(context).initializingOptions) {
            Log.instance(context).warning("jml.no.internal.runtime");
        }
    }

    /** An empty array used simply to avoid repeatedly creating one. */
    private static final @NonNull String[] emptyArgs = new String[] {};

    /** Returns a reference to the API's compilation context. */
    public @Nullable Context context() {
        return context;
    }

    /** An Enum type that gives a choice of various tools to be executed. */
    public static enum Cmd {
        CHECK("check"), ESC("esc"), RAC("rac"), DEP("dep"), JMLDOC(
                "doc"), COMPILE(
                        "compile"), INFER("infer"), JML2RAPID("jml2rapid");

        String name;

        @Override
        public String toString() {
            return name;
        }

        private Cmd(final String name) {
            this.name = name;
        }
    };

}
