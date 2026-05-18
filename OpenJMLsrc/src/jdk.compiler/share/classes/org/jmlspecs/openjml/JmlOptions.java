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

import javax.tools.JavaFileObject;

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
 * option name (with the initial hyphen(s)) to string value, in the Options superclass.
 * Also note that boolean options are encoded as null for flase, non-null String for true.
 */
public class JmlOptions extends Options {
    
    protected Context context;
    
    public boolean optionsAllSet = false;

    /** A stack of sets of options */
    protected Stack<LinkedHashMap<String,String>> stack = new Stack<>();

    /** The set of keys that control the use of optional comments, set in setupOptions() */
    public Set<String> commentKeys = new HashSet<String>();
    
 
    protected JmlOptions(Context context) {
        super(context);
        this.context = context;
        loadDefaults();
        WarningCategory.instance(context);
    }

    public static void preRegister(Context context) {
        context.put(Options.optionsKey, new JmlOptions(context)); // The put here is unnecessary because 'this' is registered in Options().
    }

    public static JmlOptions instance(Context context) {
        if (Options.instance(context) instanceof JmlOptions jmlopt) return jmlopt;
        // NOCOVERAGE
        // This branch should never execute. If it does, then there is an internal
        // bug in that an Options instance is requested before JmlOptions is a registered tool.
        // DON'T USE Utils.instance(context) -- Stack overflow will result
        System.out.println("Options.instance returns an Options instead of a JmlOptions");
        Utils.dumpStack();
        throw new JmlInternalException();
    }

//    public boolean isSet(JmlOption option) {
//        return (values.get(option.optionName()) != null);
//    }

    /** Loads the options map with all defaults for Jml options */
    public void loadDefaults() {
        //System.out.println("SETTING DEFAULTS");
        for (JmlOption opt : JmlOption.list) {
            Object d = opt.defaultValue();
            String s = d == null ? null : d.toString();
            if (opt.defaultValue() instanceof Boolean b) {
                put(opt.optionName(),b?"true":null); // FIXME - use set, unset
            } else {
                put(opt.optionName(),s);
            }
            if (!opt.obsolete()) opt.check(context,false);
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
        var utils = Utils.instance(context);
        iter = newargs.iterator();
        while (iter.hasNext()) {
            String s = iter.next();
            if (utils.hasSpecSuffix(s)) {
                if (jmlfiles != null) jmlfiles.add(new File(s));
                else utils.warning("jml.message", ".jml files on the command-line are ignored: " + s);
                iter.remove();
            }
        }
        // NOTE: cannot call setupOptions until after Java options are processed - because otherwise Lint is
        // instantiated too early
        return newargs.toArray(new String[newargs.size()]);
    }
    
    public void processOption(String key, String value) {
        var o = JmlOption.find(key);
        if (o != null) {
            values.put(key,  value);
            o.check(context,  false);
        }
    }
    
    public void set(JmlOption opt, boolean value) {
        values.put(opt.optionName(), value?"true":null);
    }
    
    public void put(JmlOption opt, String value) {
        values.put(opt.optionName(), value);
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
        if (s.length() > 1 && s.startsWith("\"") && s.endsWith("\"")) {
            s = s.substring(1,s.length()-1);
        }
        s = s.replace("\r","");
        
        boolean negate = false;
        if (s.startsWith("--no-") || s.startsWith("-no-")) {
            negate = true;
            s = s.replace("-no","");
        }
        
        JmlOption o = JmlOption.find(s);
        while (o != null && o.synonym() != null) {
            s = o.synonym();
            o = JmlOption.find(s);
        }
        

        boolean hasEqual = false;
        String res = null;
        if (o == null) {
            int k = s.indexOf('=');
            if (k != -1) {
                hasEqual = true;
                res = s.substring(k+1,s.length());
                s = s.substring(0,k);
                o = JmlOption.find(s);
                if ("--help".equals(s)) {
                    switch (res) {
                    case "warn":
                        System.out.println(WarningCategory.instance(context).help());
                        break;
                    case "infer":
                        System.out.println(InferCategory.instance(context).help());
                        break;
                    default:
                        Utils.instance(context).warning("jml.message", "No detailed help available for '" + res + "'");
                    }
                    options.put("-?",""); // Allows a clean exit without complaining about missing source files
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
                    if (negate) {
                        Utils.instance(context).warning("jml.message","no- is not permitted with set-to-default (empty string after = character)");
                        negate = false;
                    }
                    if (def instanceof Boolean bdef) negate = !bdef;
                } else  {
                    if (o.hasArg()) { }
                    else if ("false".equals(res)) negate = true;
                    else if ("true".equals(res)) res = "";
                    else {
                        res = "";
                        Utils.instance(context).warning("jml.ignoring.parameter",s);
                    }
                }
            }
        }

        if (o == JmlOption.DIRS) {
            // Test for this option here before res is set from the iterator
            if (s.startsWith("-d")) { // This is here just to accommodate the old single-hyphen style
                Utils.instance(context).warning(WarningCategory.DEPRECATED, "jml.message", "Option " + s + " is deprecated in favor of -" + s);
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
                    if (res.startsWith("-")) {
                        // res is the next option
                        processJmlArg(res,iter,options,remainingArgs,remainingArgs);
                        return;
                    }
                    addFilesRecursively(res, files);
                }
            }
            return;
        }
        

        if (o != null && o.hasArg()) {
            if (negate && !s.equals("--warn") && !s.equals("--infer") && !s.equals("--split")) {
                Utils.instance(context).warning("jml.message","no- is only permitted for boolean options (and --warn)"); // FIXME - add --split to message
                negate = false;
            }
            if (!hasEqual) {
                if (o.enabledDefault != null) {
                    res = o.enabledDefault;
                } else if (iter.hasNext()) {
                    res = iter.next();
                    if (res != null && res.length() > 1 && res.startsWith("\"") && res.endsWith("\"")) {
                        res = res.substring(1,res.length()-1);
                    }
                } else if (!negate) {
                    res = "";
                    Utils.instance(context).warning("jml.expected.parameter",s);
                    o = null;
                    s = null;
                }
            }
        }
        
        if (s == null) {
            // Error reported
        } else if (o == null) {
            if (s.equals("-help") || s.equals("-?") || s.equals("--help")) {
                if (options.get("-?") == null) allHelp(true); // Don't duplicate help output
                options.put("-?", "");
            } else {
                // Not a JML option
                remainingArgs.add(s);
            }
        } else if (o == JmlOption.DIR) {
            // Special case: --dir
            // Note that more than one instance of --dir is permitted
            if (s.startsWith("-d")) { // This is here just to accommodate the old single-hyphen style
                Utils.instance(context).warning(WarningCategory.DEPRECATED, "jml.message", "Option " + s + " is deprecated in favor of -" + s);
                s = "-" + s;
            }
            addFilesRecursively(res, remainingArgs);
        } else if (o == JmlOption.PROPERTIES) {
            // Special case: --properties
            // Note that more than one instance of --properties is permitted
            if (res == null || res.isEmpty()) {
                Utils.instance(context).warning("jml.message", "--properties requires a non-null, non-empty argument");
            } else if (!new File(res).exists() || new File(res).isDirectory()) {
                Utils.instance(context).warning("jml.message", "the argument of --properties must be a file: " + res);
            } else {
                Properties properties = new Properties();
                try {
                    Utils.readProps(properties,res); // Already checked that the file exists
                    setPropertiesFileOptions(options, properties);
                } catch (Exception e) {
                    Utils.instance(context).error("jml.message", "exception on reading properties file: " + res + " " + e);
                }
            }
        } else {
            // Common case: set the value and check it
            if (o.defaultValue() instanceof Boolean) {
                set(o, !negate);
            } else {
                put(o, res);
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
        for (var k : java.util.Collections.list(properties.propertyNames())) {
            String key = (String)k;
            String v = properties.getProperty(key);
            if (key.startsWith(Strings.optionPropertyPrefix)) {
                String rest = key.substring(Strings.optionPropertyPrefix.length());
                boolean negate = false;
                if (rest.startsWith("no-")) {
                    negate = true;
                    rest = rest.substring(3); // 3 == "no-".length()
                }
                rest = "--" + rest;
                JmlOption opt = JmlOption.find(rest);
                if (opt != null) {
                    if (opt.defaultValue() instanceof Boolean) {
                        set(opt, Boolean.parseBoolean(v));
                    } else {
                        opts.put(rest, v);
                    }
                    opt.check(context, negate);
                } else {
                    Log.instance(context).error("jml.message","No such option: " + rest);
                }
            } else {
                // Just save anything that is not encoded as an option, in case it is being used as an extension
                opts.put(key,v);
            }
        }
    }
    
    public static void setPropertiesFromOptionsDefaults(Properties properties) {
        // FIXME: THis only sets JML options
        for (JmlOption opt: JmlOption.map.values()) {
            String key = Strings.optionPropertyPrefix + opt.optionName().substring(1);
            Object defaultValue = opt.defaultValue();
            // Options that are synonyms are not true options (they are translated to their synonym)
            if (opt.synonym() == null) properties.put(key, defaultValue == null ? "" : defaultValue.toString());
        }
    }

    
    public static void setOptionsFromProperties(Properties properties, Context context) {
        // FIXME: This does not set any Java options, just JML ones
        var jmloptions = JmlOptions.instance(context);
        for (var p: properties.entrySet()) {
            String k = p.getKey().toString();
            if (k.startsWith(Strings.optionPropertyPrefix)) {
                String kk = "--" + k.substring(Strings.optionPropertyPrefix.length());
                jmloptions.processOption(kk, p.getValue().toString());
            }
        }
    }
        

    
    // NOTE: OpenJDK encodes boolean options as null for false, non-null for true */
    /** Returns whether a Boolean-valued option is set or not */
    public boolean isSet(JmlOption option) {
        if (!(option.defaultValue() instanceof Boolean)) Utils.instance(context).error("jml.internal", "Calling JmlOption.isSet on a non-boolean option");
        return isSet(option.optionName());
    }
    
    /** Returns a String value; the option must be a String-valued option */
    public String value(JmlOption option) {
        if (option.defaultValue() instanceof Boolean) Utils.instance(context).error("jml.internal", "Calling JmlOption.value on a boolean option");
        return get(option.optionName());
    }
    
    public void resetOption(JmlOption option) {
        boolean b = option.check(context,false);
        if (!b) {
            Utils.instance(context).warning("jml.message", "Erroneous option value when resetting option: " + 
                    option.optionName() + " " + option.value(context));
        }
    }

    /** This method is called after options are read, but before compilation actually begins;
     * requires tools to be registered, at least Log and Options
     * here any additional option checking or
     * processing can be performed, particularly checks that depend on multiple options.
     * 
     * Note that there is an option stack, so the current options can be popped off the stack
     * leaving a previous set of options -- which won't have gone through processJmlArg
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

        // Not supporting this option
        options.remove("printArgsToFile");
        
        utils.init(); // Sets cached fields in Utils

        // In case we have just popped options, reset any option that caches values
        resetOption(JmlOption.KEYS); // Caches in options.commentKeys
        // Set implicit comment keys
        if (utils.esc) commentKeys.add("ESC");
        if (utils.rac) commentKeys.add("RAC");
        if (JmlOption.langJML.equals(JmlOption.LANG.value(context))) commentKeys.add("STRICT");
        commentKeys.add("OPENJML");

        // FIXME - WARN keys not handled correctly I think
        
        Main.instance(context).progressListener.setVerbose(utils.jmlverbose);
        

        // register any user extensions
        Extensions.register(context);
        
        optionsAllSet = true;
        return true;
    }

    /** Adds additional options to those already present (which may change
     * previous settings); returns remaining Java args. */
    public String[] addOptions(String... args) {
        args = processJmlArgs(args, Options.instance(context), null);
        // FIXME - process Java options? 
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
        setupOptions(); // FIXME - should call postOptionProcessing(context)
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

        /** Mock file objects extracted from args during {@link #init} - added
         * back in {@link #getFileObjects} without going through the
         * {@code Files.exists()} check in {@code Option.SOURCEFILE.process}. */
        private final java.util.List<JavaFileObject> pendingMockFiles = new ArrayList<>();

        public static void register(Context context) {
            context.put(argsKey, new JmlArguments(context));
        }

        public JmlArguments(Context context) {
            super(context);
            this.context = context;
        }

        /** Pre-filters any {@code .java} args whose URI is registered in
         * {@code mockFiles.uriMap} so that {@code Option.SOURCEFILE.process}
         * never calls {@code Files.exists()} on them.  The mock objects are
         * stored in {@link #pendingMockFiles} and re-added in
         * {@link #getFileObjects}.
         * <p>
         * URI matching mirrors {@code MockJavaFileObject.makeURI}: for a
         * relative arg like {@code "A.java"} the key is
         * {@code file:///A.java}; for an absolute path the key is the
         * result of {@code Path.toUri().normalize()}. */
        @Override
        public void init(String ownName, Iterable<String> args) {
            pendingMockFiles.clear();
            var main = context.get(Main.key);
            if (main != null && main.mockFiles.hasUriEntries()) {
                java.util.List<String> filteredArgs = new ArrayList<>();
                for (String arg : args) {
                    if (arg.endsWith(".java")) {
                        try {
                            Path p = Paths.get(arg);
                            java.net.URI fileUri = p.isAbsolute()
                                    ? p.toUri().normalize()
                                    : new java.net.URI("file:///" + arg).normalize();
                            JavaFileObject mock = main.mockFiles.getByUri(fileUri);
                            if (mock != null) {
                                pendingMockFiles.add(mock);
                                continue; // skip - bypass Files.exists() check
                            }
                        } catch (Exception ignored) {
                            // not a valid Path or URI; let super handle it
                        }
                    }
                    filteredArgs.add(arg);
                }
                super.init(ownName, filteredArgs);
                if (!pendingMockFiles.isEmpty()) allowEmpty();
            } else {
                super.init(ownName, args);
            }
        }

        /** Adds any mock file objects collected during {@link #init} to the
         * set returned by {@code super.getFileObjects()}. */
        @Override
        public Set<JavaFileObject> getFileObjects() {
            Set<JavaFileObject> result = super.getFileObjects();
            result.addAll(pendingMockFiles);
            return result;
        }

        /** Reports non-empty when pending mock files exist, preventing the
         * early {@code Result.OK} return in javac {@code Main.compile}
         * that would skip compilation when no real files were passed. */
        @Override
        public boolean isEmpty() {
            return pendingMockFiles.isEmpty() && super.isEmpty();
        }

        // FIXME - is this needed? what is its effect on tool component instantiation
        @Override
        public boolean validate() {
            boolean b = super.validate();
            return JmlOptions.instance(context).setupOptions() && b;
        }

        @Override // overridden just to suppress message
        public void printUsage(String ownName) {
            if (JmlOption.VERBOSENESS.getInt(context) != Utils.QUIET || JmlOptions.instance(context).isSet("-verbose")) {
                super.printUsage(ownName);
            }
        }

    }
}
