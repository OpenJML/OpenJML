/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Map;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Log.WriterKind;

/**
 * This is an Enum that contains information about command-line options for JML
 * and related tools. To assist with future extensions, do not use the Enum type
 * directly; rather use the OptionInterface interface.
 * 
 * @author David Cok
 */
// FIXME - investigate integrating this with Option, OptionName; also change to
// something other than an enum since it is not extensible
// FIXME - best practice would use a resources file for all the help
// information; javac loads its resources on demand
public enum JmlOption implements IOption {
    
    // Arguments: option as on CL; true=1 argument, false=0 args; help string
    DIR("-dir",true,null,"Process all files, recursively, within this directory",null),
    DIRS("-dirs",true,null,"Process all files, recursively, within these directories (listed as separate arguments, up to an argument that begins with a - sign)",null),
    ENDOPTIONS("--",false,null,"Terminates option processing - all remaining arguments are files",null),  // FIXME - fix or remove
    KEYS("-keys",true,"","Identifiers for optional JML comments",null),
    COMMAND("-command",true,"check","The command to execute (check,esc,rac,compile)",null),
    CHECK("-check",false,null,"Does a JML syntax check","-command=check"),
    COMPILE("-compile",false,null,"Does a Java-only compile","-command=compile"),
    RAC("-rac",false,null,"Enables generating code instrumented with runtime assertion checks","-command=rac"),
    ESC("-esc",false,null,"Enables static checking","-command=esc"),
    BOOGIE("-boogie",false,false,"Enables static checking with boogie",null),
    USEJAVACOMPILER("-java",false,false,"When on, the tool uses only the underlying javac or javadoc compiler (must be the first option)",null),
    JML("-jml",false,true,"When on, the JML compiler is used and all JML constructs are ignored; use -no-jml to use OpenJML but ignore JML annotations",null),
    STRICT("-strictJML",false,false,"Disables any JML extensions in OpenJML",null),
    EXTENSIONS("-extensions",true,null,"Extension packages and classes (comma-separated qualified names)",null),

    STOPIFERRORS("-stopIfParseErrors",false,false,"When enabled, stops after parsing if any files have parsing errors",null),

    METHOD("-method",true,null,"Comma-separated list of method name patterns on which to run ESC",null),
    EXCLUDE("-exclude",true,null,"Comma-separated list of method name patterns to exclude from ESC",null),
    PROVER("-prover",true,null,"The prover to use to check verification conditions",null),
    PROVEREXEC("-exec",true,null,"The prover executable to use",null),
    LOGIC("-logic",true,"ALL","The SMT logic to use (default ALL)",null),
    
    NONNULLBYDEFAULT("-nonnullByDefault",false,false,"Makes references non_null by default","-nullableByDefault=false"),
    NULLABLEBYDEFAULT("-nullableByDefault",false,false,"Makes references nullable by default",null),
    CODE_MATH("-code-math",true,"safe","Arithmetic mode for Java code",null),
    SPEC_MATH("-spec-math",true,"bigint","Arithmetic mode for specifications",null),
    
    // FIXME - turn default back to true when problems have been worked out
    CHECK_ACCESSIBLE("-checkAccessible",false,false,"When on (the default), JML accessible clauses are checked",null),
    SPECS("-specspath",true,null,"Specifies the directory path to search for specification files",null),
    CHECKSPECSPATH("-checkSpecsPath",false,true,"When on (the default), warnings for non-existent specification path directories are issued",null),
    PURITYCHECK("-purityCheck",false,false,"When on (off by default), warnings for use of impure methods from system libraries are issued",null),
    INTERNALSPECS("-internalSpecs",false,true,"When on (the default), automatically appends the internal specs directory to the specification path",null),
    INTERNALRUNTIME("-internalRuntime",false,true,"When on (the default), automatically appends the internal JML runtime library to the classpath",null),
    TIMEOUT("-timeout",true,null,"Number of seconds to limit any individual proof attempt (default infinite)",null),

    SHOW_NOT_IMPLEMENTED("-showNotImplemented",false,false,"When on (off by default), warnings about unimplemented constructs are issued",null),
    SHOW_NOT_EXECUTABLE("-showNotExecutable",false,false,"When on (off by default), warnings about non-executable constructs are issued",null),

    VERBOSENESS("-verboseness",true,1,"Level of verboseness (0=quiet...4=debug)",null),
    QUIET("-quiet",false,null,"Only output warnings and errors","-verboseness="+Utils.QUIET),
    NORMAL("-normal",false,null,"Limited output","-verboseness="+Utils.NORMAL),
    PROGRESS("-progress",false,null,"Shows progress through compilation phases","-verboseness="+Utils.PROGRESS),
    JMLVERBOSE("-jmlverbose",false,false,"Like -verbose, but only jml information and not as much","-verboseness="+Utils.JMLVERBOSE),
    JMLDEBUG("-jmldebug",false,false,"When on, the program emits lots of output (includes -progress)","-verboseness="+Utils.JMLDEBUG),
    SHOW_OPTIONS("-showOptions",true, "none","When enabled, the values of options and properties are printed, for debugging",null),
    
    JMLTESTING("-jmltesting",false,false,"Only used to generate tracing information during testing",null),
    TRACE("-trace",false,false,"ESC: Enables tracing of counterexamples",null),
    SHOW("-show",true,"","Show intermediate programs",null,false,"all"),
    SPLIT("-split",true,"","Split proof into sections",null),
    ESC_BV("-escBV",true,"auto","ESC: If enabled, use bit-vector arithmetic (auto, true, false)",null),
    ESC_EXIT_INFO("-escExitInfo",false,true,"ESC: Show exit location for postconditions (default true)",null),
    ESC_MAX_WARNINGS("-escMaxWarnings",true,"all","ESC: Maximum number of warnings to find per method",null),
    MAXWARNINGSPATH("-escMaxWarningsPath",false,false,"ESC: If true, find all counterexample paths to each invalid assert",null),
    COUNTEREXAMPLE("-counterexample",false,false,"ESC: Enables output of complete, raw counterexample",null),
    CE("-ce",false,null,"ESC: Enables output of complete, raw counterexample","-counterexample"),
    SUBEXPRESSIONS("-subexpressions",false,false,"ESC: Enables tracing with subexpressions",null),
    FEASIBILITY("-checkFeasibility",true,"all","ESC: Check feasibility of assumptions",null),
    BENCHMARKS("-benchmarks",true,null,"ESC: Collects solver communications",null),
    MINIMIZE_QUANTIFICATIONS("-minQuant",false,true,"Minimizes using quantifications, in favor of inlining",null),
    QUANTS_FOR_TYPES("-typeQuants",true,"auto","Introduces quantified assertions for type variables (true, false, or auto)",null),

    MODEL_FIELD_NO_REP("-modelFieldNoRep",true,"zero","RAC action when a model field has no represents clause (zero,ignore,warn)",null),
//    ROOTS("-roots",false,false,"Enables the Reflective Object-Oriented Testing System---w00t!",null),
    
    RAC_SHOW_SOURCE("-racShowSource",false,true,"RAC: Error messages will include source information",null),
    RAC_CHECK_ASSUMPTIONS("-racCheckAssumptions",false,false,"RAC: Enables runtime checking that assumptions hold",null),
    RAC_JAVA_CHECKS("-racJavaChecks",false,false,"RAC: Enables explicit checking of Java language checks",null),
    RAC_COMPILE_TO_JAVA_ASSERT("-racCompileToJavaAssert",false,false,"RAC: Compiles JML checks as Java asserts",null),
    RAC_PRECONDITION_ENTRY("-racPreconditionEntry",false,false,"RAC: Distinguishes Precondition failures on entry calls",null),
    RAC_MISSING_MODEL_FIELD_REP_SOURCE("-racMissingModelFieldRepSource",true,"zero","RAC: action when a model field has no representation (zero,warn,skip)",null),
    RAC_MISSING_MODEL_FIELD_REP_BINARY("-racMissingModelFieldRepBinary",true,"skip","RAC: action when a model field for a binary class has no representation (zero,warn,skip)",null),

    PROPERTIES("-properties",true,null,"Specifies the path to the properties file",null),
    PROPERTIES_DEFAULT("-properties-default",true,null,"Specifies the path to the default properties file",null),
    
    DEFAULTS("-defaults",true,"","Specifies various default behaviors: constructor:pure|everything",null),
    STATIC_INIT_WARNING("-staticInitWarning",false,true,"Warns about missing static_initializer clauses",null),
    // Experimental
    DETERMINISM("-determinism",false,true,"Experimental: enables better determinism",null),

    OSNAME("-osname",true,null,"Name of OS to use in selecting solver executable",null),

    // Obsolete
    NOCHECKSPECSPATHX("-noCheckSpecsPath",false,false,"When on, no warnings for non-existent specification path directories are issued","-checkSpecsPath=false",true),
    NOPURITYCHECKX("-noPurityCheck",false,false,"When on, no warnings for use of impure methods are issued","-purityCheck=false",true),
    NOINTERNALSPECSX("-noInternalSpecs",false,false,"Disables automatically appending the internal specs directory to the specification path","-internalSpecs=false",true),
    NOINTERNALRUNTIMEX("-noInternalRuntime",false,false,"Disables automatically appending the internal JML runtime library to the classpath","-internalRuntime=false",true),
    NO_RAC_SOURCEX("-noRacSource",false,false,"RAC: Error messages will not include source information","-racShowSource=false",true),
    NO_RAC_CHECK_ASSUMPTIONSX("-noRacCheckAssumptions",false,false,"RAC: Disables checking that assumptions hold","-racCheckAssumptions=false",true),
    NO_RAC_JAVA_CHECKSX("-noRacJavaChecks",false,false,"RAC: Disables explicit checking of Java language checks","-racJavaChecks=false",true),

    ;
    
    /** Holds the name of the option, as it is used in the command-line,
     * including the leading '-' character.
     */
    final private String name;
    
    /** Whether the option takes an argument */
    final private boolean hasArg;
    
    /** The default value of the option */
    final private Object defaultValue;
    
    public String enabledDefault = null;
    
    /** The help string for this option */
    final private String help;
    
    /** The canonical form for the option */
    final private String synonym;
    
    /** If true, the option is obsolete */
    final private boolean obsolete;
    
    /** Private constructor to create Enum instances.
     * @param s The option name, including any leading - character
     * @param defaultValue the default value for the option
     * @param hasArg Whether the option takes a (required) argument
     * @param help The associated help string
     * @param synonym an equivalent command-line argument
     */
    private JmlOption(/*@ non_null */ String s, 
            boolean hasArg, 
            Object defaultValue,
            /*@ non_null */ String help,
            /*@ nullable */ String synonym) {
        this(s,hasArg,defaultValue,help,synonym,false,null);
    }
    
    /** Private constructor to create Enum instances.
     * @param s The option name, including any leading - character
     * @param defaultValue the default value for the option
     * @param hasArg Whether the option takes a (required) argument
     * @param help The associated help string
     * @param synonym an equivalent command-line argument
     * @param obsolete whether the option is obsolete
     */
    private JmlOption(/*@ non_null */ String s, 
            boolean hasArg, 
            Object defaultValue,
            /*@ non_null */ String help,
            /*@ nullable */ String synonym,
            boolean obsolete) {
        this(s,hasArg,defaultValue,help,synonym,obsolete,null);
    }
    
    /** Private constructor to create Enum instances.
     * @param s The option name, including any leading - character
     * @param defaultValue the default value for the option
     * @param hasArg Whether the option takes a (required) argument
     * @param help The associated help string
     * @param synonym an equivalent command-line argument
     * @param obsolete whether the option is obsolete
     */
    private JmlOption(/*@ non_null */ String s, 
            boolean hasArg, 
            Object defaultValue,
            /*@ non_null */ String help,
            /*@ nullable */ String synonym,
            boolean obsolete,
            String enabledDefault) {
        this.name = s;
        this.hasArg = hasArg;
        this.defaultValue = defaultValue;
        this.help = help;
        this.synonym = synonym;
        this.obsolete = obsolete;
        this.enabledDefault = enabledDefault;
    }
    
    /** Enables the given option
     * 
     * @param context the compilation context
     * @param option the option to enable
     */
    public static void putOption(Context context, JmlOption option) {
        putOption(context,option,"");
    }
    
    /** Sets the value of the given option
     * 
     * @param context the compilation context
     * @param option the option to set
     * @param value the value to give the option - boolean options interpret null as false and non-null as true
     */
    public static void putOption(Context context, JmlOption option, String value) {
        Options.instance(context).put(option.name,value);
    }
    
    /** Sets the value of a boolean option, returning the previous value
     * @param context the compilation context
     * @param option the option name
     * @param value the new value of the option
     * @return true if the option was previously enabled, false otherwise
     */
    public static boolean setOption(Context context, IOption option, boolean value) {
    	boolean b = isOption(context,option.optionName());
        Options.instance(context).put(option.optionName(),value?"":null);
        return b;
    }
    
    /** Return whether an option is enabled in the given context
     * @param context the compilation context
     * @param option the option name
     * @return true if the option is enabled, false otherwise
     */
    public static boolean isOption(Context context, JmlOption option) {
        String val = Options.instance(context).get(option.name);
        return interpretBoolean(val);
    }
    
    private static boolean interpretBoolean(String v) {
        return v != null && !"false".equals(v);
    }
    
    /** Return whether an option is enabled in the given context
     * @param context the compilation context
     * @param option the option name by string (including leading -)
     * @return true if the option is enabled, false otherwise
     */
    public static boolean isOption(Context context, String option) {
        String v = value(context,option);
        return interpretBoolean(v);
    }
    
    /** This is used for those options that allow a number of suboptions; it tests whether
     * value is one of the comma-separated suboptions.
     */
    public static boolean includes(Context context, JmlOption option, String value) {
        String v = JmlOption.value(context, option);
        return "all".equals(v) || ( v.equals(value) || v.startsWith(value + ",") || v.endsWith("," + value) || v.contains("," + value +","));
    }
    
    /** Return the value of an option with an argument
     * @param context the compilation unit context
     * @param option the option name
     * @return the value of the argument, or null if not specified
     */
    //@ nullable
    public static String value(Context context, JmlOption option) {
        return value(context,option.optionName());
    }
    
    /** Return the value of an option with an argument
     * @param context the compilation unit context
     * @param option the option name
     * @return the value of the argument, or null if not specified
     */
    //@ nullable
    public static String value(Context context, String option) {
        return Options.instance(context).get(option);
    }
    
    /** The name of the option, including any leading - sign
     * @see org.jmlspecs.openjml.IOption#optionName()
     */
     //@ non_null
    public String optionName() { return name; }

    /** The name of the option, including any leading - sign
     * @see org.jmlspecs.openjml.IOption#optionName()
     */
     //@ non_null
    public String getText() { return name; }
    
    /* Whether the option takes an argument
     * @see org.jmlspecs.openjml.OptionInterface#hasArg()
     */
    public boolean hasArg() { return hasArg; }
    
    /* Whether the option takes an argument
     * @see org.jmlspecs.openjml.OptionInterface#hasArg()
     */
    public Object defaultValue() { return defaultValue; }
    
    /* Whether the option is obsolete */
    public boolean obsolete() { return obsolete; }
    
    /**
     * @return the help string associated with this option
     */
    //@ non_null
    public String help() { 
        if (synonym() == null) {
            return help; 
        } else {
            return help + " [" + synonym() + "]";
        }
    }
    
    /**
     * @return the canonical form for this option
     */
    //@ nullable
    public String synonym() { return synonym; }
    
    /** Finds the option with the given name, returning it if
     * found and returning null if not found.
     * @param s the name of the option to find
     * @return the option found, or null
     */
    //@ ensures \result == null || \result.optionName().equals(s);
    //@ nullable
    static public JmlOption find(/*@ non_null */ String s) {
        return map.get(s);
    }
    
    static private final Map<String,JmlOption> map = new HashMap<String,JmlOption>();
    static {
        // Puts all the options in the map and adds any synonyms
        // synonyms include the all lowercase versions of each name
        for (JmlOption n: JmlOption.values()) {
            map.put(n.name,n);
            map.put(n.name.toLowerCase(),n);
        }
        // Other synonyms
        // FIXME - where did these come from - do we want them?
        map.put("-nonnull",NONNULLBYDEFAULT);
        map.put("-nullable",NULLABLEBYDEFAULT);
    }
    
    /** A help value which is the platform-dependent line termination string */
    //@ non_null
    final static public String eol = System.getProperty("line.separator");
    
    /** Returns the JML command-line argument help information as a String
     * 
     * @return the JML part of the command-line help information
     */
    //@ non_null
    public static String helpInfo() {
        StringBuilder sb = new StringBuilder();
        sb.append("JML options:").append(eol);
        for (IOption j : values()) {
            if (j.obsolete()) continue;
            sb.append("  ").append(j.optionName()).append(" ");
            // The count up to 26 is just to make for nice formatting
            for (int i = j.optionName().length(); i<26; i++) {
                sb.append(" ");
            }
            sb.append(j.help()).append(eol);
        }
        return sb.toString();
        
    }
    
    public static void listOptions(Context context, boolean all) {
        Options options = JmlOptions.instance(context);
        
        PrintWriter noticeWriter = Log.instance(context).getWriter(WriterKind.NOTICE);
        for (String key: new java.util.TreeSet<String>(options.keySet())) {
            if (all || key.startsWith("-") || key.startsWith("openjml") || key.startsWith("org.jmlspecs.openjml")) {
                noticeWriter.println(key + " = " + JmlOption.value(context,key));
            }
        }
    }
    
    /** A helper function to extract values from the 'defaults' option */
    public static /*@ nullable */ String defaultsValue(Context context, String key, String def) {
        String defaultsValue = value(context,JmlOption.DEFAULTS);
        if (defaultsValue == null) return def;
        for (String s: defaultsValue.split(",")) {
            if (s.startsWith(key + ":")) {
                return s.substring(key.length()+1);
            }
        } 
        return def;
    }
}
