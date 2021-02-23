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

import org.jmlspecs.openjml.Main.Cmd;
import org.jmlspecs.openjml.Main.PrintProgressReporter;
import org.jmlspecs.openjml.esc.MethodProverSMT;

import com.sun.tools.javac.main.Arguments;
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

/** Handles JML options. Note that all option settings are contained in a simple map of
 * option name (with the initial -) to string value, in the Options superclass.
 */
public class JmlOptions extends Options {

    protected Context context;

    /** A stack of sets of options */
    protected Stack<LinkedHashMap<String,String>> stack = new Stack<>();

    /** The set of keys that control the use of optional comments, set in setupOptions() */
    public Set<String> commentKeys = new HashSet<String>();

    protected JmlOptions(Context context) {
        super(context);
        this.context = context;
        loadDefaults();
    }

    public static void preRegister(Context context) {
        context.put(Options.optionsKey, new JmlOptions(context));
    }

    public static JmlOptions instance(Context context) {
        return (JmlOptions)Options.instance(context);
    }

    /** Loads the options map with all defaults for Jml options */
    public void loadDefaults() {
        //System.out.println("SETTING DEFAULTS");
        for (JmlOption opt : JmlOption.map.values()) {
            Object d = opt.defaultValue();
            String s = d == null ? null : d.toString();
            put(opt.optionName(),s);
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
            processJmlArg(iter,options,newargs,files);
        }
        newargs.addAll(files);
        // Separate out .jml files from the list of files, because Java will object to them
        File f;
        iter = newargs.iterator();
        while (iter.hasNext()) {
            String s = iter.next();
            if (s.endsWith(Strings.specsSuffix) && (f=new File(s)).exists()) {
                if (jmlfiles != null) jmlfiles.add(f);
                iter.remove();
            }
        }
        options.put("compilePolicy", "simple");
        // setupOptions is called to verify consistency after Java options are processed, in JmlArguments.validate
        return newargs.toArray(new String[newargs.size()]);
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
    void processJmlArg(Iterator<String> iter, /*@non_null*/ Options options, /*@ non_null */ java.util.List<String> remainingArgs, /*@ non_null */ java.util.List<String> files ) {
        String arg = iter.next();
        if (arg == null) return; // Allow but remove null arguments
        if (arg.isEmpty()) {
            remainingArgs.add(arg);
            return;
        }

        String s = arg;
        if (s.length() > 1 && s.charAt(0) == '"' && s.charAt(s.length()-1) == '"') {
            s = s.substring(1,s.length()-1);
        }

        boolean negate = false;
        if (s.startsWith("-no-")) {
            negate = true;
            s = s.substring("-no".length());
        }
        var o = JmlOption.find(s);
        while (o != null && o.synonym() != null) {
            s = o.synonym();
            if (s.startsWith("-no-")) {
                negate = !negate;
                s = s.substring("-no".length());
            }
            o = JmlOption.find(s);
        }
        String res = "";
        if (o == null) {
            int k = s.indexOf('=');
            if (k != -1) {
                res = s.substring(k+1,s.length());
                s = s.substring(0,k);
                o = JmlOption.find(s);
                if (o == null) {
                    // This is not a JML option. Might be misspelled or it might
                    // be a JDK option with an =, which JDK does not support.
                    // But can't warn about it because in this design we are filtering out
                    // JML options before Java options
                    // warning(context, "jml.message", "Ignoring command-line argument " + args[i-1] + " which is either misspelled or is a JDK option using = to set an argument (which JDK does not support)");
                    remainingArgs.add(arg);
                    return;
                } else if (res.isEmpty()) {
                    // JML option with a naked = sign
                    Object def = o.defaultValue();
                    res = def == null ? null : def.toString();

                } else {
                    if (o.hasArg()) {}
                    else if ("false".equals(res)) negate = true;
                    else if ("true".equals(res)) res = "";
                    else {
                        res = "";
                        Utils.instance(context).warning("jml.ignoring.parameter",s);
                    }
                }
            }
        } else if (!negate && o.hasArg()) {
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
            }
        }
        if (o == null) {
            if (s.equals("-help")) {
                helpJML(Main.instance(context).stdOut); // FIXME - send to a log?
            } else {
                remainingArgs.add(s);
            }
        } else if (JmlOption.DIR.optionName().equals(s) || JmlOption.DIRS.optionName().equals(s)) {
            java.util.List<File> todo = new LinkedList<File>();
            todo.add(new File(res));
            if (JmlOption.DIRS.optionName().equals(s)) {
                while (iter.hasNext() && (res=iter.next()).length() > 0 && res.charAt(0) != '-') {
                    todo.add(new File(res));
                }
            }
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
                    if (utils.hasJavaSuffix(ss)) files.add(ss); // FIXME - if we allow .jml files on the command line, we have to guard against parsing them twice
                } else {
                    try {
                        String glob = file.toString();
                        final PathMatcher pathMatcher = FileSystems.getDefault().getPathMatcher(
                                "glob:"+glob);

                        String location = ""; // System.getProperty("user.dir");
                        Files.walkFileTree(Paths.get(location), new SimpleFileVisitor<Path>() {

                            @Override
                            public FileVisitResult visitFile(Path path,
                                    BasicFileAttributes attrs) throws IOException {
                                if (pathMatcher.matches(path)) {
                                    todo.add(path.toFile());
                                }
                                return FileVisitResult.CONTINUE;
                            }

                            @Override
                            public FileVisitResult visitFileFailed(Path file, IOException exc)
                                    throws IOException {
                                return FileVisitResult.CONTINUE;
                            }
                        });
                    } catch (Exception e) {
                        utils.warning("jml.message", "Exception while enumerating file " + file.toString() + ": " + e.toString());
                        // continue
                    }
                }
            }
        } else {
            if (negate) {
                if (o.defaultValue() instanceof Boolean) {
                    JmlOption.setOption(context, o, false);
                } else if (o.defaultValue() == null) {
                    options.put(s,null);
                } else {
                    options.put(s,o.defaultValue().toString());
                }
            } else {
                if (o.defaultValue() instanceof Boolean) {
                    JmlOption.setOption(context, o, true);
                } else {
                    options.put(s,res);
                }
            }
        }

        if (o != null && o.equals(JmlOption.PROPERTIES)){
            Properties properties = System.getProperties();
            String file = JmlOption.value(context,JmlOption.PROPERTIES);
            if (file != null && !file.isEmpty()) {
                try {
                    Utils.readProps(properties,file);
                } catch (java.io.IOException e) {
                    Utils.instance(context).note(false,"Failed to read property file " + file);
                }
                setPropertiesFileOptions(options, properties);
            }
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

        String t = options.get(JmlOption.JMLTESTING.optionName());
        Utils.testingMode =  ( t != null && !t.equals("false"));
        String benchmarkDir = options.get(JmlOption.BENCHMARKS.optionName());
        if (benchmarkDir != null) {
            new File(benchmarkDir).mkdir();
        }

        utils.jmlverbose = Utils.NORMAL;

        {
            // Automatically set verboseness to PROGRESS if we are debugging checkFeasibility.
            // So do this determination before we interpret the verboseness option.
            t = options.get(JmlOption.FEASIBILITY.optionName());
            if (t != null) {
                if (t.startsWith("debug") && utils.jmlverbose < Utils.PROGRESS) utils.jmlverbose = Utils.PROGRESS;
                int k = t.indexOf(":");
                if (k > 0) {
                    try {
                        MethodProverSMT.startFeasibilityCheck = Integer.parseInt(t.substring(k+1));
                    } catch (Exception e) {
                        // continue
                    }
                }
            }
        }

        String n = JmlOption.VERBOSENESS.optionName().trim();
        String levelstring = options.get(n);
        if (levelstring != null) {
            levelstring = levelstring.trim();
            if (!levelstring.isEmpty()) try {
                utils.jmlverbose = Integer.parseInt(levelstring);
            } catch (NumberFormatException e) {
                utils.warning("jml.message","The value of the " + n + " option or the " + Strings.optionPropertyPrefix + n.substring(1) + " property should be the string representation of an integer: \"" + levelstring + "\"");
                options.put(n, "1");
            }
        }
        if (options.get("-verbose") != null) {
            // If the Java -verbose option is set, we set -jmlverbose as well
            utils.jmlverbose = Utils.JMLVERBOSE;
        }

        if (utils.jmlverbose >= Utils.PROGRESS) {
            // FIXME - recview all this
            // Why not let the progress listener decide what to print???

            // We check for an existing delegate, because if someone is calling
            // OpenJML programmatically, they may have set one up already.
            // Note, though that this won't undo the setting, if verbosity is
            // turned off.
            //if (!progressDelegator.hasDelegate()) {
                try {
                    Main.instance(context).progressDelegator.setDelegate(Main.progressListener != null ? Main.progressListener.get() : new PrintProgressReporter(context,Main.instance(context).stdOut));
                } catch (Exception e) {
                    // FIXME - report problem
                    // continue without installing a listener
                }
            //}
        } else {
            Main.instance(context).progressDelegator.setDelegate(null);
        }

        boolean b = JmlOption.isOption(context,JmlOption.USEJAVACOMPILER);
        if (b) {
            Utils.instance(context).warning("jml.message","The -java option is ignored unless it is the first command-line argument");
        }

        Cmd cmd = Cmd.CHECK; // default
        String val = options.get(JmlOption.COMMAND.optionName());
        try {
            if (val != null) cmd = Cmd.valueOf(val.toUpperCase());
        } catch (IllegalArgumentException e) {
            Log.instance(context).error("jml.bad.command",val);
            return false;
        }
        utils.cmd = cmd;
        utils.rac = cmd == Cmd.RAC;
        utils.esc = cmd == Cmd.ESC;
        utils.check = cmd == Cmd.CHECK;
        utils.compile = cmd == Cmd.COMPILE;
        utils.infer   = cmd == Cmd.INFER;

        val = options.get(JmlOption.ESC_BV.optionName());
        if (val == null || val.isEmpty()) {
            options.put(JmlOption.ESC_BV.optionName(),(String)JmlOption.ESC_BV.defaultValue());
        } else if("auto".equals(val) || "true".equals(val) || "false".equals(val)) {
        } else {
            utils.warning("jml.message","Command-line argument error: Expected 'auto', 'true' or 'false' for -escBV: " + val);
            options.put(JmlOption.ESC_BV.optionName(),(String)JmlOption.ESC_BV.defaultValue());
        }

        val = options.get(JmlOption.LANG.optionName());
        if (val == null || val.isEmpty()) {
            options.put(JmlOption.LANG.optionName(),(String)JmlOption.LANG.defaultValue());
        } else if(JmlOption.langPlus.equals(val) || JmlOption.langJavelyn.equals(val) || JmlOption.langJML.equals(val)) {
        } else {
            utils.warning("jml.message","Command-line argument error: Expected '" + JmlOption.langPlus + "', '" + JmlOption.langJML + "' or '" + JmlOption.langJavelyn + "' for -lang: " + val);
            options.put(JmlOption.LANG.optionName(),(String)JmlOption.LANG.defaultValue());
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

        // FIXME - can this be set later, so it is not called everytime the options are set/checked
        if (JmlOption.isOption(context,JmlOption.INTERNALRUNTIME)) Main.appendRuntime(context);

        String limit = JmlOption.value(context,JmlOption.ESC_MAX_WARNINGS);
        if (limit == null || limit.isEmpty() || limit.equals("all")) {
            utils.maxWarnings = Integer.MAX_VALUE; // no limit is the default
        } else {
            try {
                int k = Integer.parseInt(limit);
                utils.maxWarnings = k <= 0 ? Integer.MAX_VALUE : k;
            } catch (NumberFormatException e) {
                utils.error("jml.message","Expected a number or 'all' as argument for -escMaxWarnings: " + limit);
                utils.maxWarnings = Integer.MAX_VALUE;
            }
        }

        String v = JmlOption.value(context, JmlOption.SHOW);
        if (v == null) options.put(JmlOption.SHOW.optionName(),"");

        String check = JmlOption.value(context,JmlOption.FEASIBILITY);
        if (check == null || check.isEmpty() || check.equals(Strings.feas_default)) {
            options.put(JmlOption.FEASIBILITY.optionName(),check=Strings.feas_defaults);
        }
        if (check.equals(Strings.feas_all)) {
            options.put(JmlOption.FEASIBILITY.optionName(),check=Strings.feas_alls);
        } else if (check.startsWith(Strings.feas_debug)) {
            options.put(JmlOption.FEASIBILITY.optionName(),check=Strings.feas_alls+",debug");
            if (utils.jmlverbose < Utils.PROGRESS) utils.jmlverbose = Utils.PROGRESS;
        }
        String badString = Strings.isOK(check);
        if (badString != null) {
            utils.error("jml.message","Unexpected value as argument for -checkFeasibility: " + badString);
        }

        Extensions.register(context);
// FIXME - turn off for now        JmlSpecs.instance(context).initializeSpecsPath();
        // dumpOptions();
        return true;
    }



    /** Adds additional options to those already present (which may change
     * previous settings). */
    public void addOptions(String... args) {
        args = processJmlArgs(args, Options.instance(context), null);
        setupOptions();
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
        new RuntimeException().printStackTrace(System.out);
        System.out.println("JML Options:");
        for (var s: values.entrySet()) {
            System.out.println(s.getKey() + " : " + s.getValue());
        }
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
