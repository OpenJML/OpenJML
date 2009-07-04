package org.jmlspecs.openjml;

import java.util.HashMap;
import java.util.Map;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Options;

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
public enum JmlOptionName implements OptionInterface {

    // Arguments: option as on CL; true=1 argument, false=0 args; help string
    DIR("-dir",true,"Process all files, recursively, within this directory"),
    DIRS("-dirs",true,"Process all files, recursively, within these directories (listed as separate arguments, up to an argument that begins with a - sign)"),
    COMMAND("-command",true,"The command to execute (check,esc,rac,compile)"),
    CHECK("-check",false,"Does a JML syntax check - abbreviation for -command check")
        { public void process(Options options) { options.put(COMMAND.name,"check"); }},
    COMPILE("-compile",false,"Does a Java-only compiler - abbreviation for -command compile")
        { public void process(Options options) { options.put(COMMAND.name,"compile"); }},
    RAC("-rac",false,"Enables generating code instrumented with runtime assertion checks - abbreviation for -command rac")
        { public void process(Options options) { options.put(COMMAND.name,"rac"); }},
    ESC("-esc",false,"Enables static checking - abbreviation for -command esc")
        { public void process(Options options) { options.put(COMMAND.name,"esc"); }},
    USEJAVACOMPILER("-java",false,"When on, the tool uses only the underlying javac or javadoc compiler (must be the first option)"),
    NOJML("-noJML",false,"When on, the JML compiler is used, but all JML constructs are ignored"),
    SPECS("-specspath",true,"Specifies the directory path to search for specification files"),
    NOCHECKSPECSPATH("-noCheckSpecsPath",false,"When on, no warnings for non-existent specification path directories are issued"),
    NOPURITYCHECK("-noPurityCheck",false,"When on, no warnings for use of impure methods are issued"),
    SHOW_NOT_IMPLEMENTED("-showNotImplemented",false,"When on, warnings about unimplemented constructs are issued"),
    STOPIFERRORS("-stopIfParseErrors",true,"When enabled, stops after parsing if any files have parsing errors"),
    NOINTERNALSPECS("-noInternalSpecs",false,"Disables automatically appending the internal specs directory to the specification path"),
    NOINTERNALRUNTIME("-noInternalRuntime",false,"Disables automatically appending the internal JML runtime library to the classpath"),
    NONNULLBYDEFAULT("-nonnullByDefault",false,"Makes references non_null by default")
        { public void process(Options options) { options.put(NULLABLEBYDEFAULT.name,null); }},
    NULLABLEBYDEFAULT("-nullableByDefault",false,"Makes references nullable by default")
        { public void process(Options options) { options.put(NONNULLBYDEFAULT.name,null); }},
    JMLVERBOSE("-jmlverbose",false,"Like -verbose, but only jml information and not as much (included in -verbose)")
        { public void process(Options options) { options.put(PROGRESS.name,""); }},
    PROGRESS("-progress",false,"Shows progress through compilation phases, includes -jmlverbose")
        { public void process(Options options) { options.put(JMLVERBOSE.name,""); }},
    //INTERACTIVE("-i",false,"Must be first, starts interactive mode"),  // FIXME- fix or remove
    TRACE("-trace",false,"ESC: Enables tracing of counterexamples"),
    COUNTEREXAMPLE("-counterexample",false,"ESC: Enables output of complete, raw counterexample"),
    SUBEXPRESSIONS("-subexpressions",false,"ESC: Enables tracing with subexpressions"),
    JMLDEBUG("-jmldebug",false,"When on, the program emits lots of output (includes -progress)"),
    ROOTS("-roots",false,"Enables the Reflective Object-Oriented Testing System---w00t!"),
    ENDOPTIONS("--",false,"Terminates option processing - all remaining arguments are files")
    ;
    public void process(Options options) {}
    

    /** Convenience field for the name of the SPECS option. */
    public final static String specs = SPECS.optionName();
    
    /** Holds the name of the option, as it is used in the command-line,
     * including the leading '-' character.
     */
    final private String name;
    
    /** Whether the option takes an argument */
    final private boolean hasArg;
    
    /** The help string for this option */
    final private String help;
    
    /** Private constructor to create Enum instances.
     * @param s The option name, including any leading - character
     * @param hasArg Whether the option takes a (required) argument
     * @param help The associated help string
     */
    private JmlOptionName(/*@ non_null */ String s, boolean hasArg, /*@ non_null */ String help) {
        this.name = s;
        this.hasArg = hasArg;
        this.help = help;
    }
    
    /** Enables the given option
     * 
     * @param context the compilation context
     * @param option the option to enable
     */
    public static void putOption(Context context, JmlOptionName option) {
        putOption(context,option,"");
    }
    
    /** Sets the value of the given option
     * 
     * @param context the compilation context
     * @param option the option to set
     * @param value the value to give the option
     */
    public static void putOption(Context context, JmlOptionName option, String value) {
        Options.instance(context).put(option.name,value);
    }
    
    /** Return whether an option is enabled in the given context
     * @param context the compilation context
     * @param option the option name
     * @return true if the option is enabled, false otherwise
     */
    public static boolean isOption(Context context, JmlOptionName option) {
        return Options.instance(context).get(option.name) != null;
    }
    
    /** Return whether an option is enabled in the given context
     * @param context the compilation context
     * @param option the option name by string (including leading -)
     * @return true if the option is enabled, false otherwise
     */
    public static boolean isOption(Context context, String option) {
        return Options.instance(context).get(option) != null;
    }
    
    /** Return the value of an option with an argument
     * @param context the compilation unit context
     * @param option the option name
     * @return the value of the argument, or null if not specified
     */
    //@ nullable
    public static String value(Context context, JmlOptionName option) {
        return Options.instance(context).get(option.name);
    }
    
    /** The name of the option, including any leading - sign
     * @see org.jmlspecs.openjml.OptionInterface#optionName()
     */
     //@ non_null
    public String optionName() { return name; }

    /* Whether the option takes an argument
     * @see org.jmlspecs.openjml.OptionInterface#hasArg()
     */
    public boolean hasArg() { return hasArg; }
    
    /**
     * @return the help string associated with this option
     */
    //@ non_null
    public String help() { return help; }
    
    /** Finds the option with the given name, returning it if
     * found and returning null if not found.
     * @param s the name of the option to find
     * @return the option found, or null
     */
    //@ ensures \result == null || \result.optionName().equals(s);
    //@ nullable
    static public JmlOptionName find(/*@ non_null */ String s) {
        return map.get(s);
    }
    
    static Map<String,JmlOptionName> map = new HashMap<String,JmlOptionName>();
    static {
        // Puts all the options in the map and adds any synonyms
        // synonyms include the all lowercase versions of each name
        for (JmlOptionName n:JmlOptionName.values()) {
            map.put(n.name,n);
            map.put(n.name.toLowerCase(),n);
        }
        // Other synonyms
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
        for (OptionInterface j : values()) {
            sb.append("  ").append(j.optionName());
            for (int i = j.optionName().length(); i<27; i++) {
                sb.append(" ");
            }
            sb.append(j.help()).append(eol);
        }
        return sb.toString();
        
    }
}
