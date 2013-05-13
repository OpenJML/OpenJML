/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
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
public enum JmlOption implements IOption {
    
    // Arguments: option as on CL; true=1 argument, false=0 args; help string
    DIR("-dir",true,"Process all files, recursively, within this directory",null),
    DIRS("-dirs",true,"Process all files, recursively, within these directories (listed as separate arguments, up to an argument that begins with a - sign)",null),
    ENDOPTIONS("--",false,"Terminates option processing - all remaining arguments are files",null),  // FIXME - fix or remove
    KEYS("-keys",true,"Identifiers for optional JML comments",null),
    COMMAND("-command",true,"The command to execute (check,esc,rac,compile)",null),
    CHECK("-check",false,"Does a JML syntax check","-command=check"),
    COMPILE("-compile",false,"Does a Java-only compile","-command=compile"),
    RAC("-rac",false,"Enables generating code instrumented with runtime assertion checks","-command=rac"),
    ESC("-esc",false,"Enables static checking","-command=esc"),
    BOOGIE("-boogie",false,"Enables static checking with boogie",null),
    USEJAVACOMPILER("-java",false,"When on, the tool uses only the underlying javac or javadoc compiler (must be the first option)",null),
    NOJML("-noJML",false,"When on, the JML compiler is used, but all JML constructs are ignored",null),
    NEWESC("-newesc",false,"When on, uses the new SMT-based implementation",null),
    CUSTOM("-custom",false,"When on, uses the old custom prover implementation",null),
    STRICT("-strictJML",false,"Disables any JML extensions in OpenJML",null),

    STOPIFERRORS("-stopIfParseErrors",false,"When enabled, stops after parsing if any files have parsing errors",null),

    METHOD("-method",true,"Comma-separated list of method name patterns on which to run ESC",null),
    EXCLUDE("-exclude",true,"Comma-separated list of method name patterns to exclude from ESC",null),
    PROVER("-prover",true,"The prover to use to check verification conditions",null),
    PROVEREXEC("-exec",true,"The prover executable to use",null),

    NONNULLBYDEFAULT("-nonnullByDefault",false,"Makes references non_null by default","-nullableByDefault=false"),
    NULLABLEBYDEFAULT("-nullableByDefault",false,"Makes references nullable by default",null),
    SPECS("-specspath",true,"Specifies the directory path to search for specification files",null),
    NOCHECKSPECSPATH("-noCheckSpecsPath",false,"When on, no warnings for non-existent specification path directories are issued",null),
    NOPURITYCHECK("-noPurityCheck",false,"When on, no warnings for use of impure methods are issued",null),
    NOINTERNALSPECS("-noInternalSpecs",false,"Disables automatically appending the internal specs directory to the specification path",null),
    NOINTERNALRUNTIME("-noInternalRuntime",false,"Disables automatically appending the internal JML runtime library to the classpath",null),

    SHOW_NOT_IMPLEMENTED("-showNotImplemented",false,"When on, warnings about unimplemented constructs are issued",null),
    SHOW_NOT_EXECUTABLE("-showNotExecutable",false,"When on, warnings about non-executable constructs are issued",null),

    VERBOSENESS("-verboseness",true,"Level of verboseness (0=quiet...4=debug)",null),
    QUIET("-quiet",false,"Only output warnings and errors","-verboseness="+Utils.QUIET),
    NORMAL("-normal",false,"Limited output","-verboseness="+Utils.NORMAL),
    PROGRESS("-progress",false,"Shows progress through compilation phases","-verboseness="+Utils.PROGRESS),
    JMLVERBOSE("-jmlverbose",false,"Like -verbose, but only jml information and not as much","-verboseness="+Utils.JMLVERBOSE),
    JMLDEBUG("-jmldebug",false,"When on, the program emits lots of output (includes -progress)","-verboseness="+Utils.JMLDEBUG),

    JMLTESTING("-jmltesting",false,"Only used to generate tracing information during testing",null),
    TRACE("-trace",false,"ESC: Enables tracing of counterexamples",null),
    SHOW("-show",false,"Show intermediate programs",null),
    CE("-ce",false,"ESC: Enables output of complete, raw counterexample","-counterexample"),
    MAXWARNINGS("-escMaxWarnings",true,"ESC: Maximum number of warnings to find per method",null),
    COUNTEREXAMPLE("-counterexample",false,"ESC: Enables output of complete, raw counterexample",null),
    SUBEXPRESSIONS("-subexpressions",false,"ESC: Enables tracing with subexpressions",null),
    FEASIBILITY("-checkFeasibility",true,"ESC: Check feasibility of assumptions",null),
    ROOTS("-roots",false,"Enables the Reflective Object-Oriented Testing System---w00t!",null),
    ASSOCINFO("-crossRefAssociatedInfo",false,">...",null),
    
    SHOW_RAC_SOURCE("-showRacSource",false,"RAC: Error messages will include source information","-noRacSource=false"),
    NO_RAC_SOURCE("-noRacSource",false,"RAC: Error messages will not include source information",null),
    NO_RAC_CHECK_ASSUMPTIONS("-noRacCheckAssumptions",false,"RAC: Disables checking that assumptions hold",null),
    NO_RAC_JAVA_CHECKS("-noRacJavaChecks",false,"RAC: Disables explicit checking of Java language checks",null),
    RAC_COMPILE_TO_JAVA_ASSERT("-racCompileToJavaAssert",false,"RAC: Compiles JML checks as Java asserts",null)
    //INTERACTIVE("-i",false,"Must be first, starts interactive mode"),  // FIXME- fix or remove
    ;
    

    /** Holds the name of the option, as it is used in the command-line,
     * including the leading '-' character.
     */
    final private String name;
    
    /** Whether the option takes an argument */
    final private boolean hasArg;
    
    /** The help string for this option */
    final private String help;
    
    /** The canonical form for the option */
    final private String synonym;
    
    /** Private constructor to create Enum instances.
     * @param s The option name, including any leading - character
     * @param hasArg Whether the option takes a (required) argument
     * @param help The associated help string
     */
    private JmlOption(/*@ non_null */ String s, 
            boolean hasArg, 
            /*@ non_null */ String help,
            /*@ nullable */ String synonym) {
        this.name = s;
        this.hasArg = hasArg;
        this.help = help;
        this.synonym = synonym;
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
     * @param value the value to give the option - boolean options use null for false and non-null for true
     */
    public static void putOption(Context context, JmlOption option, String value) {
        Options.instance(context).put(option.name,value);
    }
    
    /** Return whether an option is enabled in the given context
     * @param context the compilation context
     * @param option the option name
     * @return true if the option is enabled, false otherwise
     */
    public static boolean isOption(Context context, JmlOption option) {
        return Options.instance(context).get(option.name) != null;
    }
    
    /** Return whether an option is enabled in the given context
     * @param context the compilation context
     * @param option the option name by string (including leading -)
     * @return true if the option is enabled, false otherwise
     */
    public static boolean isOption(Context context, String option) {
        return value(context,option) != null;
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

    /* Whether the option takes an argument
     * @see org.jmlspecs.openjml.OptionInterface#hasArg()
     */
    public boolean hasArg() { return hasArg; }
    
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
            sb.append("  ").append(j.optionName()).append(" ");
            // The count up to 26 is just to make for nice formatting
            for (int i = j.optionName().length(); i<26; i++) {
                sb.append(" ");
            }
            sb.append(j.help()).append(eol);
        }
        return sb.toString();
        
    }
}
