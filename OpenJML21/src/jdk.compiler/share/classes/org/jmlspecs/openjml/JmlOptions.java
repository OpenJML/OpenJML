package org.jmlspecs.openjml;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
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
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

import org.jmlspecs.openjml.JmlTree.JmlModifiers;
import org.jmlspecs.openjml.Main.Cmd;
import org.jmlspecs.openjml.Main.PrintProgressReporter;
import org.jmlspecs.openjml.esc.MethodProverSMT;

import com.sun.tools.javac.main.Arguments;
import com.sun.tools.javac.main.JmlCompiler;
import com.sun.tools.javac.main.Option.OptionKind;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCNewArray;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Log.PrefixKind;
import com.sun.tools.javac.util.Log.WriterKind;

/** Handles JML options. Note that all option settings are contained in a simple map of
 * option name (with the initial -) to string value, in the Options superclass.
 */
public class JmlOptions extends Options {
    
    // Warning-keys
    public static final String IMPLICIT_EVERYTHING = "implicit-everything";

    protected Context context;

    /** A stack of sets of options */
    protected Stack<LinkedHashMap<String,String>> stack = new Stack<>();

    /** The set of keys that control the use of optional comments, set in setupOptions() */
    public Set<String> commentKeys = new HashSet<String>();
    
    public Map<String,Boolean> warningKeys = new java.util.HashMap<>();
    {
        warningKeys.put(IMPLICIT_EVERYTHING, true);
    }
    
    public boolean allowed(String key) {
        Boolean b = warningKeys.get(key);
        if (b != null) return b;
        Utils.instance(context).error("jml.internal.not.so.bad","Invalid warning key: " + key);
        return true;
    }

    protected JmlOptions(Context context) {
        super(context);
        this.context = context;
        loadDefaults();
    }

    public static void preRegister(Context context) {
        context.put(Options.optionsKey, new JmlOptions(context));
    }

    public static JmlOptions instance(Context context) {
    	if (!(Options.instance(context) instanceof JmlOptions)) Utils.dumpStack();
        return (JmlOptions)Options.instance(context);
    }
    
    public boolean isSet(JmlOption option) {
    	return (values.get(option.optionName()) != null);
    }

    /** Loads the options map with all defaults for Jml options */
    public void loadDefaults() {
        //System.out.println("SETTING DEFAULTS");
        for (JmlOption opt : JmlOption.map.values()) {
            Object d = opt.defaultValue();
            String s = d == null ? null : d.toString();
            put(opt.optionName(),s);
            opt.check(context,false);
        }
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
     * as JML options and their arguments.
     * @param args the input command-line arguments
     * @param options the Options map in which recognized options are recorded
     * @return all arguments not recognized as JML
     */
    //@ requires \nonnullelements(args);
    //@ ensures \result != null && \nonnullelements(\result);
    String[] processJmlArgs(/*@non_null*/ String [] args, /*@non_null*/ Options options, ListBuffer<File> jmlfiles) {
        java.util.List<String> newargs = new ArrayList<String>();
        java.util.List<String> files = new ArrayList<String>();
        Iterator<String> iter = Arrays.asList(args).iterator();
        while (iter.hasNext()) {
            processJmlArg(iter.next(),iter,options,newargs,files);
        }
        newargs.addAll(files);
        // Separate out .jml files from the list of files, because Java will object to them
        File f;
        iter = newargs.iterator();
        while (iter.hasNext()) {
            String s = iter.next();
            if (s.endsWith(Strings.specsSuffix) && (f=new File(s)).exists()) {
                if (jmlfiles != null) jmlfiles.add(f);
                else Utils.instance(context).warning("jml.message", ".jml files on the command-line are ignored: " + s);
                iter.remove();
            }
        }
        setupOptions(); // check consistency of options so far, even though Java options are not processed yet
        options.put("compilePolicy", "simple");
        JmlCompiler.instance(context).compilePolicy = com.sun.tools.javac.main.JavaCompiler.CompilePolicy.SIMPLE;
        // setupOptions is called to verify consistency after Java options are processed, in JmlArguments.validate
        return newargs.toArray(new String[newargs.size()]);
    }
    
    public void processOption(String key, String value) {
        var o = JmlOption.find(key);
        if (o != null) {
        	values.put(key,  value);
        	o.check(context,  false);
        }
    }
    
    public void addFilesRecursively(String s,  /*@ non_null */ java.util.List<String> files) {
        java.util.List<File> todo = new LinkedList<File>();
        todo.add(new File(s));
        Utils utils = Utils.instance(context);
        while (!todo.isEmpty()) {
            File file = todo.remove(0);
            if (file.isDirectory()) {
                File[] fileArray = file.listFiles();
                // Comparator is intentionally reversed, so we push items on the front of the queue in reverse order
                Arrays.sort(fileArray, new java.util.Comparator<File>(){ public int compare(File f, File ff) { return (f.isFile() && ff.isDirectory()) ? 1 : (ff.isFile() && f.isDirectory()) ? -1 : -f.getPath().compareToIgnoreCase(ff.getPath()); }});
                for (File ff: fileArray) {
                    todo.add(0,ff);
                }
            } else if (file.isFile()) {
                String ss = file.toString();
                if (utils.hasJavaSuffix(ss)) files.add(ss); // The compiler does not handle anything but .java files (any .jml files are loaded implicitly, not explictly)
            } else {
                Utils.instance(context).warning("jml.message", "Ignoring " + file + " (not a file or folder)");
            }
        }
    }

    /** Processes a single JML command-line option and any arguments.
     * Any non-JML argument is added to remainingArgs
     * Any JML but non-Java files are added to files
     *
     * @param args the full array of command-line arguments
     * @param i    the index of the argument to be processed
     * @param options the options object to be adjusted as JML options are found
     * @param remainingArgs any arguments that are not JML options
     * @return the index of the next argument to be processed
     */
    //@ requires iter.hasNext();
    //@ requires \nonnullelements(args);
    //@ requires (* elements of remainingArgs are non-null *);
    //@ requires 0<= i && i< args.length;
    //@ ensures \result > i;
    void processJmlArg(String arg, Iterator<String> iter, /*@non_null*/ Options options, /*@ non_null */ java.util.List<String> remainingArgs, /*@ non_null */ java.util.List<String> files ) {
        if (arg == null) {
            return; // Silently allow a null element in 'args' but remove it
        }
        
        if (arg.isEmpty()) {
            remainingArgs.add(arg);
            return;// Allow empty arguments (Pass them on to Java argument processing)
        }

        String s = arg;
        // If the argument is quoted (with "), remove the quotes
        if (s.length() > 1 && s.charAt(0) == '"' && s.charAt(s.length()-1) == '"') {
            s = s.substring(1,s.length()-1);
        }

        boolean negate = false;
        if (s.startsWith("--no-") || s.startsWith("-no-")) {
            negate = true;
            s = s.replace("-no","");
        }
        
        var o = JmlOption.find(s);
        while (o != null && o.synonym() != null) {
            s = o.synonym();
            if (s.startsWith("-no-") || s.startsWith("--no-")) {
                negate = !negate;
                s = s.replace("-no","");
            }
            o = JmlOption.find(s);
        }
        

        String res = null;
        if (o == null) {
            int k = s.indexOf('=');
            if (k != -1) {
                res = s.substring(k+1,s.length());
                s = s.substring(0,k);
                o = JmlOption.find(s);
                if (!res.isEmpty() && s.equals("--help")) {
                    switch (res) {
                    case "warn":
                        System.out.println("Implemented warning keys: " + warningKeys.keySet());
                        break;
                    default:
                        Utils.instance(context).warning("jml.message", "No detailed help available for '" + res + "'");
                    }
                    return;
                } else if (o == null) {
                    // This is not a JML option. Might be misspelled or it might
                    // be a JDK option with an =, which JDK does not support.
                    // But can't warn about it because in this design we are filtering out
                    // JML options before Java options
                    // Utils.instance(context).warning("jml.message", "Ignoring command-line argument " + arg + " " + s + " " + negate + " which is either misspelled or is a JDK option using = to set an argument (which JDK does not support)");
                    remainingArgs.add(arg);
                    return;
                } else if (res.isEmpty()) {
                    // JML option with a naked = sign
                	// which means to reset the option to its default value
                    Object def = o.defaultValue();
                    res = def == null ? null : def.toString();

                } else  {
                    if (o.hasArg()) {}
                    else if ("false".equals(res)) negate = true;
                    else if ("true".equals(res)) res = "";
                    else {
                        res = "";
                        Utils.instance(context).warning("jml.ignoring.parameter",s);
                    }
                }
            }
        }
        if (o == JmlOption.DIRS || s.equals("-dirs")) { // TODO - do we need the second disjunct
            // Test for this option here before res is set from the iterator
            if (s.startsWith("-d")) { // This is here just to accommodate the old single-hyphen style
                Utils.instance(context).warning("jml.message", "Option " + s + " is deprecated in favor of -" + s);
                s = "-" + s;
            }
            if (negate) {
                Utils.instance(context).warning("jml.message", "-no is not permitted on --dirs (ignored)");
            }
            if (res != null) {
                for (var a: res.split(",")) addFilesRecursively(a, remainingArgs);
            } else {
                // -dirs is different because it reads the next option and does not require an argument
                while (iter.hasNext()) {
                    res = iter.next();
                    if (res.length() > 0 && res.charAt(0) == '-') {
                        // res is the next option
                        processJmlArg(res,iter,options,remainingArgs,remainingArgs);
                        return;
                    }
                    addFilesRecursively(res, files);
                }
            }
            return;
        }

        if (o != null && !negate && o.hasArg() && res == null) {
            if (o instanceof JmlOption && o.enabledDefault != null) {
                res = o.enabledDefault;
            } else if (iter.hasNext()) {
                res = iter.next();
                if (res != null && res.length() > 1 && res.charAt(0) == '"' && s.charAt(res.length()-1) == '"') {
                    res = res.substring(1,res.length()-1);
                }
            } else {
                res = "";
                Utils.instance(context).warning("jml.expected.parameter",s);
                o = null;
                s = null;
            }
        }
        
        if (s == null) {
        } else if (o == null) {
            if (s.equals("-help") || s.equals("-?") || s.equals("--help")) {
                allHelp(true);
                options.put("-?", "");
            } else {
                remainingArgs.add(s);
            }
        } else if (o == JmlOption.DIR || s.equals("-dir")) {
            if (s.startsWith("-d")) { // This is here just to accommodate the old single-hyphen style
                Utils.instance(context).warning("jml.message", "Option " + s + " is deprecated in favor of -" + s);
                s = "-" + s;
            }
            addFilesRecursively(res, remainingArgs);
        } else if (o == JmlOption.PROPERTIES) {
            Properties properties = System.getProperties();
            String file = res;
            if (file != null && !file.isEmpty()) {
                try {
                    Utils.readProps(properties,file);
                } catch (java.io.IOException e) {
                    Utils.instance(context).note(false,"Failed to read property file " + file + " (cwd: " + System.getProperty("user.dir") + ")");
                }
                setPropertiesFileOptions(options, properties);
            }
        } else {
            if (o.defaultValue() instanceof Boolean) {
        		JmlOption.setOption(context, o, !negate);
        	} else {
        		options.put(o.optionName(),res);
        		// Use negate with call of check later on
        	}
            o.check(context, negate);
        }
    }
    
    public void allHelp(boolean details) {
    	if (!details) {
    		Log.instance(context).printRawLines("Usage: openjml <options> <source files>");
    		Log.instance(context).printRawLines("Use option '-?' to list options");
    	} else {
    		Log.instance(context).printLines(WriterKind.STDOUT, PrefixKind.JAVAC, "msg.usage.header", "openjml");
    		Log.instance(context).printRawLines("Java options:");
    		com.sun.tools.javac.main.Option.showHelp(Log.instance(context), OptionKind.STANDARD);
    		helpJML(Main.instance(context).stdOut); // FIXME - send to a log?
    	}
    }


    /** Sets options (first argument) from any relevant properties (second argument) */
    protected void setPropertiesFileOptions(Options opts, Properties properties){
        for (Map.Entry<Object,Object> p : properties.entrySet()) {
            Object o = p.getKey();
            if (!(o instanceof String)) {
                Utils.instance(context).warning("jml.ignoring.non.string.key", o.getClass());
                continue;
            }
            String key = (String)o;
            Object value = p.getValue();
            if (!(value instanceof String)) {
                Utils.instance(context).warning("jml.ignoring.non.string.value", o.getClass(),key);
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
    }

    /** This method is called after options are read, but before compilation actually begins;
     * requires tools to be registered, at least Log and Options
     * here any additional option checking or
     * processing can be performed, particularly checks that depend on multiple options.
     */
    // This should be able to be called without difficulty whenever any option
    // is changed
    public boolean setupOptions() {
        // CAUTION: If tools cache values of options and have their singleton
        // instance created before the options are completely processed, the
        // tool will grab some default version of the option.
        // Crucially, Log does this.

        Options options = Options.instance(context);
        Utils utils = Utils.instance(context);

        options.remove("printArgsToFile");
        
        try {
        	utils.jmlverbose = Integer.parseInt(options.get(JmlOption.VERBOSENESS.optionName()));
        } catch (Exception e) {
        	// continue
        }
        if (options.get("-verbose") != null) {
            // If the Java -verbose option is set, we set -jmlverbose as well
            utils.jmlverbose = Utils.JMLVERBOSE;
        }

        // TODO - needs review
        if (utils.jmlverbose >= Utils.PROGRESS) {
        	try {
        		Main.instance(context).progressDelegator.setDelegate(Main.progressListener != null ? Main.progressListener.get() : new PrintProgressReporter(context,Main.instance(context).stdOut));
        	} catch (Exception e) {
        		e.printStackTrace(System.out);
        		// FIXME - report problem
        		// continue without installing a listener
        	}
        } else {
        	Main.instance(context).progressDelegator.setDelegate(null);
        }


        String keysString = options.get(JmlOption.KEYS.optionName());
        commentKeys = new HashSet<String>();
        if (keysString != null && !keysString.isEmpty()) {
            String[] keys = keysString.split(",");
            for (String k: keys) commentKeys.add(k);
        }

        if (utils.esc) commentKeys.add("ESC");
        if (utils.rac) commentKeys.add("RAC");
        if (JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) commentKeys.add("STRICT");
        commentKeys.add("OPENJML");

        Extensions.register(context);
// FIXME - turn off for now        JmlSpecs.instance(context).initializeSpecsPath();
        return true;
    }



    /** Adds additional options to those already present (which may change
     * previous settings); returns remaining Java args. */
    public String[] addOptions(String... args) {
        args = processJmlArgs(args, Options.instance(context), null);
        setupOptions();
        return args;
    }

    /** Adds a custom option (not checked as a legitimate command-line option);
     * may have an argument after a = symbol */
    public void addUncheckedOption(String arg) {
        int k = arg.indexOf('=');
        if (k == -1) {
            Options.instance(context).put(arg,"");
        } else {
            String value = arg.substring(k+1);
            Options.instance(context).put(arg.substring(0,k),value);
        }
    }

    // FIXME - the options popped and pushed should not be ones that have modifier/annotation equivalents
    // So no nonnullbydefault/nullablebydefault and code-math and spec-math

    /** Pushes the current options on the option stack (cf. JmlOption), retaining a copy;
     * then adds the given modifiers to the current options.
     * @param mods
     */
    public void pushOptions(JCModifiers mods) {
        Name optionName = Names.instance(context).fromString("org.jmlspecs.annotation.Options");

        JmlOptions.instance(context).pushOptions();
        {
        	JCAnnotation addedOptionsAnnotation = Utils.instance(context).findMod(mods, optionName);
        	if (addedOptionsAnnotation != null) {
        		List<JCExpression> exprs = addedOptionsAnnotation.getArguments();
        		JCExpression rhs = ((JCAssign)exprs.head).rhs;
        		String[] opts = rhs instanceof JCNewArray ? ((JCNewArray)rhs).elems.stream().map(e->e.toString()).collect(Collectors.toList()).toArray(new String[((JCNewArray)rhs).elems.size()])
        				: rhs instanceof JCLiteral ? new String[]{ rhs.toString() }
        		: null;
        				addOptions(opts);
        	}
        }
    }

    /** Pushes a copy of the current options on the options stack, so the current state of the options can
     * be reinstated by calling popOptions(); the options currently in effect are unchanged, but can be
     * modified without affecting the pushed copy.
     */
    public void pushOptions() {
        stack.push(values);
        LinkedHashMap<String,String> newvalues = new LinkedHashMap<String,String>();
        newvalues.putAll(values);
        values = newvalues;
    }

    /** Deletes the current copy of the options, replacing it with the set of options popped off the options stack;
     * throws an exception if the options stack is empty (because of more pops than pushes).
     */
    public void popOptions() {
        values = stack.pop();
        setupOptions();
    }

    /** Output all the options -- purely for debugging */
    public void dumpOptions() {
        java.util.List<String> opts = new ArrayList<>();
        for (var s: values.entrySet()) {
            opts.add(s.getKey() + " : " + s.getValue());
        }
        java.util.Collections.sort(opts);
        System.out.println("JML Options:");
        opts.stream().forEach(s -> System.out.println(s));
    }

    /** We replace the Arguments tool in order to validate the JML options
     * when the Java options are validated (during the run-up to compilation
     * in JavaCompiler).
     */
    public static class JmlArguments extends Arguments {
        private Context context;

        public static void register(Context context) {
            context.put(argsKey, new JmlArguments(context));
        }

        public JmlArguments(Context context) {
            super(context);
            this.context = context;
        }

        @Override
        public boolean validate() {
            boolean b = super.validate();
            return JmlOptions.instance(context).setupOptions() && b;
        }
    }
}
