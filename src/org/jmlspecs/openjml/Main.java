package org.jmlspecs.openjml;

import java.io.File;
import java.io.PrintWriter;
import java.lang.reflect.Method;
import java.util.ArrayList;

import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlFlow;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Messages;
import com.sun.tools.javac.util.Options;

/**
 * This class is the main entry point for the JML tool. It uses the javac
 * compiler, but overrides some of the functionality here in order to register
 * tools for the compiler to use that are extensions with JML functionality of
 * the usual tools. Also the handling of JML-specific options is initialized
 * here.
 */
public class Main extends com.sun.tools.javac.main.Main {

    /** The compilation unit context most recently registered
     * (this can change if there are multiple contexts; it is really here
     * for convenience for testing. */
    protected Context context;
    
    /** This is a cached copy of the output writer, for use when
     * direct writing is needed (such as printing out help information) before
     * the Log facility is registered.
     */
    //@ non_null
    protected PrintWriter out;
    
    /**
     * Construct a compiler instance.
     */
    @edu.umd.cs.findbugs.annotations.SuppressWarnings("NM_SAME_SIMPLE_NAME_AS_SUPERCLASS")
    public Main() {
        this("jml", new PrintWriter(System.err, true));
    }

    /**
     * Construct a compiler instance.
     */
    public Main(/*@ non_null */String name, /*@ non_null */PrintWriter out) {
        super(name,out);
        this.out = out;
    }

    /** The external entry point - simply calls helper(args) and exits with the
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
    
    /** The option string for requesting help information */
    final public static String helpOption = "-help";
    /** The option string for requesting interactive mode */
    final public static String interactiveOption = "-i";
    
    /** A programmatic interface to the compiler that returns the exit code, but
     * does not itself call System.exit.  [This is called compiler rather than
     * compile as in com.sun.tools.javac.Main because we also have to override
     * com.sun.tools.javac.main.Main.compile ]
     * @param args the command-line arguments
     * @return the exit code
     */ 
    //@ requires args != null && \nonnullelements(args);
    public static int compiler(String[] args) {
        //System.out.println("STARTING");
        int errorcode = 1; //com.sun.tools.javac.main.Main.EXIT_ERROR;
        try {
            if (args == null) {
                Context context = new Context(); // This is a temporary context just for this error message.
                                    // It is not the one used for the options and compilation
                Log log = Log.instance(context);
                Messages.instance(context).add(Utils.messagesJML);
                log.error("jml.main.null.args","org.jmlspecs.openjml.Main.main");
                errorcode = 2; // com.sun.tools.javac.main.Main.EXIT_CMDERR;
            } else {
                // We have to interpret the -useJavaCompiler option before we start
                // the compiler (which does the normal option processing).
                // Since this is rare, we'll require that it be the first
                // option.
                boolean useJavaCompiler = args != null && args.length > 0 &&
                        args[0].equals(JmlOptionName.USEJAVACOMPILER.optionName());
                if (useJavaCompiler) {
                    errorcode = com.sun.tools.javac.Main.compile(args);
                } else if (args.length > 0 && args[0].equals(interactiveOption)) {
                    // interactive mode
                    errorcode = new org.jmlspecs.openjml.Interactive().run(args);
                    if (Utils.jmldebug || errorcode != 0) System.out.println("ENDING with exit code " + errorcode); 
                } else {
                    com.sun.tools.javac.main.Main compiler = new org.jmlspecs.openjml.Main();
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
            Messages.instance(context).add(Utils.messagesJML);
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
            if (Options.instance(context).get(helpOption) != null) {
                exit = super.compile(args,context);
                helpJML();
            } else {
                exit = super.compile(args,context);
            }
        }
//        JmlSpecs specs = JmlSpecs.instance(context); // This is just for debugging
//        specs.printDatabase();
        return exit;
    }
        
    /** This is a utility method to print out all of the help information */
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
    String[] processJmlArgs(/*@ non_null */String [] args,/*@ non_null */ Options options) {
        ArrayList<String> newargs = new ArrayList<String>();
        for (int i = 0; i<args.length; ) {
            String res = "";
            String s = args[i++];
            OptionInterface o = JmlOptionName.find(s);
            if (o == null) {
                int k = s.indexOf('=');
                if (k != -1) {
                    o = JmlOptionName.find(s.substring(0,k));
                    if (s.substring(k+1,s.length()).equals("false")) res = null;
                }
                if (s.equals(helpOption)) options.put(s,"");
            }
            if (o == null) {
                newargs.add(s);
            } else {
                if (!o.hasArg()) options.put(s,res);
                else options.put(s, args[i++]);
            }
        }
        return newargs.toArray(new String[]{});
    }
    
    /* We override this method in order to process the JML command-line 
     * arguments and to do any tool-specific initialization
     * after the command-line arguments are processed.  
     */   // FIXME - we are hacking the availability of 'context' here in a non-thread-safe way
    @edu.umd.cs.findbugs.annotations.SuppressWarnings("ST_WRITE_TO_STATIC_FROM_INSTANCE_METHOD")
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
     * that use each other, if you can not careful.
     * @param context the compilation context into which to register the tools
     */
    public void register(/*@ non_null @*/ Context context) {
        this.context = context;// A hack so that context is available in processArgs()

        // This is done later, but we do it here so that the Log is
        // available if tool registration (or argument processing) needs the
        // Log.  However, note that if the Log is actually instantiated before
        // Java arguments are read, then it is not set consistently with those 
        // options.
        context.put(Log.outKey,out);

        // These have to be first in case there are error messages during 
        // tool registration.
        Messages.instance(context).add(Utils.messagesJML); // registering an additional source of JML-specific error messages

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
}
