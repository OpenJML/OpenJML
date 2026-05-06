/*
 * This file is part of the OpenJML project.
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import static com.sun.tools.javac.main.Option.WERROR;

import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Map;

import org.jmlspecs.openjml.Main.Cmd;
import org.jmlspecs.openjml.esc.MethodProverSMT;

import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;

import com.sun.tools.javac.main.Main.Result;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.JavacMessages;
import com.sun.tools.javac.util.Position;
import org.jmlspecs.openjml.Utils;

/**
 * This is an Enum that contains information about command-line options for JML
 * and related tools. To assist with future extensions, do not use the Enum type
 * directly; rather use the OptionInterface interface.
 *
 * @author David Cok
 */
// FIXME - best practice would use a resources file for all the help
// information; javac loads its resources on demand
public class JmlOption {

    /** Holds a map from standard name (as String) to JmlOption */
    static public final Map<String,JmlOption> map = new HashMap<>();  // Holds a map of name to JmlOption
    /** Holds a list of JmlOption in a predictable order, namely the declaration order */
    // (for both issuing help information and for loading defaults)
    static public final List<JmlOption> list = new ArrayList<>(); 
    
    static public void clWarning(Context context, String message) {
        JavacMessages.instance(context).add(Strings.messagesJML);
        Log.instance(context).warning(Position.NOPOS, JCDiagnostic.Factory.instance(context).warningKey("jml.message",message));
    }
    
    static public void clError(Context context, String message) {
        JavacMessages.instance(context).add(Strings.messagesJML);
        Log.instance(context).error(Position.NOPOS, JCDiagnostic.Factory.instance(context).errorKey("jml.message",message));
    }
    
    public boolean check(Context context, boolean negate) { 
        if (defaultValue() instanceof Boolean) {
            Options options = Options.instance(context);
            String v = options.get(name);
            if ("false".equals(v) || "False".equals(v) || "FALSE".equals(v)) {
                options.put(name,null);
            }
        }
        if (this.obsolete()) {
            clWarning(context, "The option " + this.name + " is obsolete and ignored");
        }
        return true;
    }
    
    // Do Not set cached fields in other classes in the check() methods of JmlOption instances, because that will cause premature 
    // instantiation of tool components (before all the options are processed). Instead, have setupOptions() call some initialization
    // method in those classes that need such initialization.

    // This option is used in Utils.warning, so it must be the first option in the list
    public static final JmlOption VERBOSENESS = new JmlOption("--verboseness",true,"1","Level of verboseness (0=quiet...4=debug)",null) {
        public boolean check(Context context, boolean negate) {
            String n = JmlOption.VERBOSENESS.optionName().trim();
            String levelstring = JmlOptions.instance(context).get(n).trim();
            {
                try {
                    Integer.parseInt(levelstring); // Just to see if it parses OK
                } catch (NumberFormatException e) {
                    // FIXME - avoid insttantiating Utils?
                    clWarning(context, "The value of the " + n + " option or the " + Strings.optionPropertyPrefix + n.substring(2) + " property should be the string representation of an integer: \"" + levelstring + "\"");
                    JmlOptions.instance(context).put(n, "1");
                    return false;
                }
            }
            return true;
        }
        public int getInt(Context context) {
            String n = JmlOption.VERBOSENESS.optionName().trim();
            String value = JmlOptions.instance(context).get(n).trim();
            try { return Integer.parseInt(value); } catch (NumberFormatException e) { return 1; }
        }
    };

    public static final JmlOption DIR = new JmlOption("--dir",true,null,"Process all files, recursively, within this directory",null);
    public static final JmlOption DIRS = new JmlOption("--dirs",true,null,"Process all files, recursively, within these directories (listed as separate arguments, up to an argument that begins with a - sign)",null);
    public static final JmlOption KEYS = new JmlOption("--keys",true,"","Identifiers for optional JML comments",null) {
        public boolean check(Context context, boolean negate) {
            var options = JmlOptions.instance(context);
            String keysString = options.get(JmlOption.KEYS.optionName());
            options.commentKeys = new java.util.HashSet<String>();
            if (keysString != null && !keysString.isEmpty()) {
                String[] keys = keysString.split(",");
                for (String k: keys) options.commentKeys.add(k);
            }
            return true;
        }
    };
    public static final JmlOption COMMAND = new JmlOption("--command",true,"check","The command to execute (parse,check,esc,rac,compile)",null) {
        public boolean check(Context context, boolean negate) {
            Cmd cmd = Cmd.CHECK; // default
            boolean ok = true;
            String val = JmlOptions.instance(context).get(JmlOption.COMMAND.optionName());
            try {
                if (val != null) cmd = Cmd.valueOf(val.toUpperCase());
            } catch (IllegalArgumentException e) {
                Log.instance(context).error("jml.bad.command",val);
                ok = false;
            }
            Utils utils = Utils.instance(context);
            utils.cmd = cmd;
            utils.rac = cmd == Cmd.RAC;
            utils.esc = cmd == Cmd.ESC;
            utils.check = cmd == Cmd.CHECK;
            utils.compile = cmd == Cmd.COMPILE;
            utils.infer   = cmd == Cmd.INFER;
            return ok;
    	}
    };
    public static final JmlOption PARSE = new JmlOption("--parse",false,null,"Only parses input files","--command=parse");
    public static final JmlOption CHECK = new JmlOption("--check",false,null,"Does a JML syntax check","--command=check");
    public static final JmlOption COMPILE = new JmlOption("--compile",false,null,"Does a Java-only compile","--command=compile");
    public static final JmlOption RAC = new JmlOption("--rac",false,null,"Enables generating code instrumented with runtime assertion checks","--command=rac");
    public static final JmlOption ESC = new JmlOption("--esc",false,null,"Enables static checking","--command=esc");
    //    public static final JmlOption BOOGIE = new JmlOption("-boogie",false,false,"Enables static checking with boogie",null);
    public static final JmlOption USEJAVACOMPILER = new JmlOption("-java",false,false,"When on, the tool uses only the underlying javac or javadoc compiler (must be the first option)",null) {
        public boolean check(Context context, boolean negate) {
            boolean b = JmlOption.USEJAVACOMPILER.isSet(context);
            if (b) {
                clWarning(context, "The -java option is ignored unless it is the first command-line argument");
            }
            return true;
        }
    };
    public static final JmlOption JML = new JmlOption("-jml",false,true,"When on, the JML compiler is used and all JML constructs are processed; use -no-jml to use OpenJML but ignore JML annotations",null);

    public static final String langJML = "jml";
    public static final String langOpenJML = "openjml";
    protected static List<String> jmlVariants = Arrays.asList(new String[]{ langJML, langOpenJML });
    public static void addVariant(String s) { jmlVariants.add(s); }
    public static final JmlOption LANG = new JmlOption("--lang",true,langOpenJML,"Set the language variant to use (default 'openjml'): " + Utils.join(" ",jmlVariants),null) {
        public boolean check(Context context, boolean negate) {
            JmlOptions options = JmlOptions.instance(context);
            // The default has been filled in before check is called
            String val = options.get(JmlOption.LANG.optionName());
            if (!jmlVariants.contains(val)) {
                clWarning(context, "Command-line argument error: Expected one of " + jmlVariants + " for --lang: " + val);
                options.put(JmlOption.LANG.optionName(),(String)JmlOption.LANG.defaultValue());
                return false;
            }
            return true;
    	}
    };
    public static final JmlOption EXITVERIFY = new JmlOption("--verify-exit",true,"6","Exit code for verification errors",null) {
        public boolean check(Context context, boolean negate) {
            // FIXME - negate not allowed
            // Check that the value given is a integer
            JmlOptions options = JmlOptions.instance(context);
            // The default has been filled in before check is called
            String val = options.get(JmlOption.EXITVERIFY.optionName());
            try {
                int n = Integer.valueOf(val);
                if (-1 <= n && n <= 6) return true;
                throw new RuntimeException();
            } catch (Exception e) {
                clError(context, "Invalid value for " + JmlOption.EXITVERIFY + ": " + val);
                options.put(JmlOption.EXITVERIFY.optionName(), JmlOption.EXITVERIFY.defaultValue().toString());
                return false;
            }
            
        }
        public int getInt(Context context) {
            JmlOptions options = JmlOptions.instance(context);
            String val = options.get(JmlOption.EXITVERIFY.optionName());
            try {
                int n = Integer.valueOf(val);
                if (-1 <= n && n <= 6) return n;
                throw new RuntimeException();
            } catch (Exception e) {
                clError(context, "Invalid value for " + JmlOption.EXITVERIFY + ": " + val);
                return 6; // the default
            }
       }
    };
    public static final JmlOption EXTENSIONS = new JmlOption("--extensions",true,null,"Extension packages and classes (comma-separated qualified names)",null);

    public static final JmlOption METHOD = new JmlOption("--method",true,null,"Comma-separated list of method name patterns on which to run ESC",null);
    public static final JmlOption EXCLUDE = new JmlOption("--exclude",true,null,"Comma-separated list of method name patterns to exclude from ESC",null);
    public static final JmlOption PROVER = new JmlOption("--prover",true,null,"The prover to use to check verification conditions",null);
    public static final JmlOption PROVEREXEC = new JmlOption("--exec",true,null,"The prover executable to use",null);
    public static final JmlOption LOGIC = new JmlOption("--logic",true,"ALL","The SMT logic to use (default ALL)",null); // obsolete
    public static final JmlOption SMT = new JmlOption("--smt",true,null,"A file to write the smt command file to",null);

    public static final JmlOption NONNULLBYDEFAULT = new JmlOption("--nonnull-by-default",false,false,"Makes references non_null by default","--nullable-by-default=false");
    { map.put("-nonnullByDefault",NONNULLBYDEFAULT); }
    public static final JmlOption NULLABLEBYDEFAULT = new JmlOption("--nullable-by-default",false,false,"Makes references nullable by default",null);
    { map.put("-nullableByDefault",NULLABLEBYDEFAULT); }
    public static final JmlOption CODE_MATH = new JmlOption("--code-math",true,"safe","Arithmetic mode for Java code (java, safe, bigint)",null);
    public static final JmlOption SPEC_MATH = new JmlOption("--spec-math",true,"bigint","Arithmetic mode for specifications (java, safe, bigint)",null);
    public static final JmlOption ARITHMETIC = new JmlOption("--arithmetic-failure",true,"soft","Whether arithmetic warnings are hard, soft (default) or quiet",null) {
          public boolean check(Context context, boolean negate) {
              String n = JmlOption.ARITHMETIC.optionName();
              String mode = JmlOptions.instance(context).get(n);
              if (!(mode.equals("hard") || mode.equals("soft") || mode.equals("quiet"))) {
                  clWarning(context, "The value of the " + n + " option or the " + Strings.optionPropertyPrefix + n.substring(2) 
                  + " property should be one of 'hard', 'soft', or 'quiet': " + mode);
                  JmlOption.ARITHMETIC.put(context, JmlOption.ARITHMETIC.defaultValue().toString());
                  return false;
              }
              return true;
          }
    };
    // FIXME - turn default back to true when problems have been worked out
    public static final JmlOption CHECK_ACCESSIBLE = new JmlOption("--check-accessible",false,true,"When on (the default), JML accessible clauses are checked",null);
    { map.put("-checkAccessible",CHECK_ACCESSIBLE); }
    public static final JmlOption SPECS = new JmlOption("--specs-path",true,null,"Specifies the directory path to search for specification files",null);
    { map.put("-specspath",SPECS); }
    //public static final JmlOption NEWISPURE = new JmlOption("--new-is-pure",false,false,"Allows object allocation in pure expressions",null);
    public static final JmlOption TIMEOUT = new JmlOption("--timeout",true,null,"Number of seconds to limit any individual proof attempt (default infinite)",null);

    public static final JmlOption SHOW_NOT_IMPLEMENTED = new JmlOption("--show-not-implemented",false,false,"When on (off by default), warnings about unimplemented constructs are issued",null);
    { map.put("-showNotImplemented",SHOW_NOT_IMPLEMENTED); }
    public static final JmlOption SHOW_NOT_EXECUTABLE = new JmlOption("--show-not-executable",false,false,"When on (off by default), warnings about non-executable constructs are issued",null);
    { map.put("-showNotExecutable",SHOW_NOT_EXECUTABLE); }

    public static final JmlOption WARN = new JmlOption("--warn",true,"","Comma-separated list of warning keys to enable or disable",null) {
        public boolean check(Context context, boolean negate) {
            JmlOptions options = JmlOptions.instance(context);
            WarningCategory warnings = WarningCategory.instance(context);
            String val = options.get(JmlOption.WARN.optionName());
            // CAUTION: check is called with an empty-string argument as part of initialization, when error messages are not yet read in.
            if (val == null) {
                // In a bug-free program, this branch will never happen
                Log.instance(context).error("jml.internal", "null option value in JmlOption.WARN.check");
            } else {
                if ("list".equals(val)) {
                    System.out.print(warnings.list()); System.out.flush(); // FIXME - use Log.out() or something like that?
                } else if ("reset".equals(val) || val.isEmpty()) {
                    warnings.reset();
                } else if ("all".equals(val)) {
                    warnings.setAll(negate ? WarningCategory.WarnAction.QUIET : WarningCategory.WarnAction.WARN);
                } else if ("none".equals(val)) {
                    warnings.setAll(negate ? WarningCategory.WarnAction.WARN : WarningCategory.WarnAction.QUIET);
                } else {
                    String[] keys = val.split(","); // Discards trailing empty strings (or a single empty string)
                    for (var k: keys) {
                        if (warnings.containsKey(k)) {
                            warnings.put(k, negate ? WarningCategory.WarnAction.QUIET : WarningCategory.WarnAction.WARN );
                        } else {
                            clWarning(context, "In --(no-)warn, '" + k + "' is not a valid warning key; see --help=warn");
                        }
                    }
                }
            }
            return true;
        }
    };
    public static final JmlOption INFER = new JmlOption("--infer",true,"","Comma-separated list of inference keys to enable or disable",null) {
        public boolean check(Context context, boolean negate) {
            JmlOptions options = JmlOptions.instance(context);
            InferCategory infermap = InferCategory.instance(context);
            String val = options.get(JmlOption.INFER.optionName());
            // CAUTION: check is called with an empty-string argument as part of initialization, when error messages are not yet read in.
            if (val == null) {
                // In a bug-free program, this branch will never happen
                Log.instance(context).error("jml.internal", "null option value in JmlOption.INFER.check");
            } else {
                if ("list".equals(val)) {
                    System.out.print(infermap.list()); System.out.flush(); // FIXME - use Log.out() or something like that?
                } else if ("reset".equals(val) || val.isEmpty()) {
                    infermap.reset();
                } else if ("all".equals(val)) {
                    infermap.setAll(negate ? InferCategory.InferAction.NO : InferCategory.InferAction.YES);
                } else if ("none".equals(val)) {
                    infermap.setAll(negate ? InferCategory.InferAction.YES : InferCategory.InferAction.NO);
                } else if ("show".equals(val)) {
                    infermap.showInferred = !negate;
                } else {
                    String[] keys = val.split(","); // Discards trailing empty strings (or a single empty string)
                    for (var k: keys) {
                        if (infermap.inferKeys.containsKey(k)) infermap.inferKeys.put(k, negate ? InferCategory.InferAction.NO : InferCategory.InferAction.YES );
                        else clWarning(context, "In --(no-)infer, '" + k + "' is not a valid infer key; see --help=infer");
                    }
                }
            }
            return true;
        }
    };
    public static final JmlOption QUIET = new JmlOption("--quiet",false,null,"Only output the exit code","--verboseness="+Utils.QUIET);
    public static final JmlOption NORMAL = new JmlOption("--normal",false,null,"Error and warning messages (default)","--verboseness="+Utils.NORMAL);
    public static final JmlOption PROGRESS = new JmlOption("--progress",false,null,"Shows progress through compilation phases","--verboseness="+Utils.PROGRESS);
    public static final JmlOption SHOW_SKIPPED = new JmlOption("--show-skipped",false,true,"Shows methods whose proofs are skipped",null);
    public static final JmlOption SHOW_SUMMARY = new JmlOption("--show-summary",false,true,"Shows summary and time information",null);
    public static final JmlOption JMLVERBOSE = new JmlOption("--jmlverbose",false,false,"Like --verbose, but only jml information and not as much","--verboseness="+Utils.JMLVERBOSE);
    public static final JmlOption JMLDEBUG = new JmlOption("--jmldebug",false,false,"When on, the program emits lots of output (includes --progress)","--verboseness="+Utils.JMLDEBUG);
//    public static final JmlOption SHOW_OPTIONS = new JmlOption("--show-options",false, "none","When enabled, the values of options and properties are printed, for debugging",null);

    // Internal use only
    public static final JmlOption JMLTESTING = new JmlOption("-jmltesting",false,false,"Controls output information during testing",null) {
        public boolean check(Context context, boolean negate) {
            InferCategory.instance(context).showInferred = false;
            return true;
        }
    };
    public static final JmlOption TRACE = new JmlOption("--trace",false,false,"ESC: Enables tracing of counterexamples",null);
    public static final JmlOption SHOW = new JmlOption("--show",true,"","Show intermediate programs",null,"all");   // Has a default
    public static final JmlOption SPLIT = new JmlOption("--split",true,"","Split proof into sections",null) {
        public boolean check(Context context, boolean negate) {
            if (negate) {
                JmlOptions options = JmlOptions.instance(context);
                var nm = JmlOption.SPLIT.optionName();
                options.put(nm, null);
            }
            return true;
        }
    };
    public static final JmlOption ESC_BV = new JmlOption("--esc-bv",true,"auto","ESC: If enabled, use bit-vector arithmetic (auto, true, false)",null) {
        public boolean check(Context context, boolean negate) {
            JmlOptions options = JmlOptions.instance(context);
            var nm = JmlOption.ESC_BV.optionName();
            String val = options.get(nm);
            {
                if("auto".equals(val) || "true".equals(val) || "false".equals(val)) {
                } else {
                    clWarning(context, "Command-line argument error: Expected 'auto', 'true' or 'false' for "+nm+": " + val);
                    options.put(nm,(String)JmlOption.ESC_BV.defaultValue());
                    return false;
                }
            }
            return true;
    	}
    };
    { map.put("-escBV",ESC_BV); }
    public static final JmlOption ESC_TRIGGERS = new JmlOption("--triggers",false,true,"ESC: Enable quantifier triggers in SMT encoding (default true)",null);
    public static final JmlOption ESC_MAX_WARNINGS = new JmlOption("--esc-max-warnings",true,"all","ESC: Maximum number of warnings to find per method",null) {
        public boolean check(Context context, boolean negate) {
            String limit = JmlOption.ESC_MAX_WARNINGS.value(context);
            {
                if (limit.equals("all")) {
                } else {
                    try {
                        Integer.parseInt(limit);
                    } catch (NumberFormatException e) {
                        clError(context, "Expected a number or 'all' as argument for --esc-max-warnings: " + limit);
                        return false;
                    }
                }
            }
            return true;
        }
        public int getInt(Context context) {
            String limit = JmlOption.ESC_MAX_WARNINGS.value(context);
            {
                if (limit.equals("all")) {
                    return Integer.MAX_VALUE; // no limit is the default
                } else {
                    try {
                        int k = Integer.parseInt(limit);
                        return k <= 0 ? Integer.MAX_VALUE : k;
                    } catch (NumberFormatException e) {
                        clError(context, "Expected a number or 'all' as argument for --esc-max-warnings: " + limit);
                        return Integer.MAX_VALUE;
                    }
                }
            }
    	}
    };
    { map.put("-escMaxWarnings",ESC_MAX_WARNINGS); }
    public static final JmlOption ESC_WARNINGS_PATH = new JmlOption("--esc-warnings-path",false,false,"ESC: If true, find all counterexample paths to each invalid assert",null);
    public static final JmlOption COUNTEREXAMPLE = new JmlOption("--counterexample",false,false,"ESC: Enables output of complete, raw counterexample",null);
    { map.put("-ce",COUNTEREXAMPLE); }
    public static final JmlOption SUBEXPRESSIONS = new JmlOption("--subexpressions",false,false,"ESC: Enables tracing with subexpressions",null);
    public static final JmlOption FEASIBILITY = new JmlOption("--check-feasibility",true,"none","ESC: Check feasibility of assumptions",null) {
        public boolean check(Context context, boolean negate) {
            JmlOptions options = JmlOptions.instance(context);
            String check = JmlOption.FEASIBILITY.value(context);
            if (check == null || check.isEmpty()) {
                options.put(JmlOption.FEASIBILITY.optionName(),check=Strings.feas_none);
            } else if (check.equals(Strings.feas_basic)) {
                options.put(JmlOption.FEASIBILITY.optionName(),check=Strings.feas_basics);
            } else if (check.equals(Strings.feas_all)) {
                options.put(JmlOption.FEASIBILITY.optionName(),check=Strings.feas_alls);
            } else if (check.startsWith(Strings.feas_debug)) {
                int k = check.indexOf(":");
                if (k > 0) {
                    try {
                        MethodProverSMT.startFeasibilityCheck = Integer.parseInt(check.substring(k+1));
                    } catch (Exception e) {
                        // continue
                    }
                }
            }
            String badString = Strings.isOKFeasibility(check);
            if (badString != null) {
                clError(context, "Unexpected value as argument for --check-feasibility: " + badString);
                return false;
            }
            return true;
    	}
    };
    { map.put("-checkFeasibility",FEASIBILITY); }
//    public static final JmlOption BENCHMARKS = new JmlOption("--benchmarks",true,null,"ESC: Collects solver communications",null);
    public static final JmlOption QUANTS_FOR_TYPES = new JmlOption("--typeQuants",true,"auto","ESC: Introduces quantified assertions for type variables (true, false, or auto)",null);
    public static final JmlOption SEED = new JmlOption("--solver-seed",true,"0","ESC: Seed to initialize solver's random number generation",null);
//    public static final JmlOption MODEL_FIELD_NO_REP = new JmlOption("-modelFieldNoRep",true,"zero","RAC action when a model field has no represents clause (zero,ignore,warn)",null);

    public static final JmlOption RAC_SHOW_SOURCE = new JmlOption("--rac-show-source",true,"source","RAC: Error messages will include source information (none,line,source)",null) {
        public boolean check(Context context, boolean negate) {
            JmlOptions options = JmlOptions.instance(context);
            String val = options.get(optionName());
            if ("none".equals(val) || "line".equals(val) || "source".equals(val)) {
                // OK
            } else {
                clWarning(context, "Command-line argument error: Expected 'none', 'line' or 'source' for --rac-show-source : " + val);
                options.put(optionName(),(String)defaultValue());
                return false;
            }
            return true;
        }
    };
    public static final JmlOption RAC_CHECK_ASSUMPTIONS = new JmlOption("--rac-check-assumptions",false,true,"RAC: Enables runtime checking that assumptions hold",null);
    public static final JmlOption RAC_JAVA_CHECKS = new JmlOption("--rac-java-checks",false,false,"RAC: Enables explicit checking of Java language checks",null);
    public static final JmlOption RAC_COMPILE_TO_JAVA_ASSERT = new JmlOption("--rac-compile-to-java-assert",false,false,"RAC: Compiles JML checks as Java asserts",null);
    public static final JmlOption RAC_PRECONDITION_ENTRY = new JmlOption("--rac-precondition-entry",false,false,"RAC: Distinguishes Precondition failures on entry calls",null);
    public static final JmlOption RAC_MISSING_MODEL_FIELD_REP = new JmlOption("--rac-missing-model-field-rep",true,"skip","RAC: action when a model field has no representation (zero,zero-quiet,skip,skip-quiet,fail)",null) {
        public final static String[] values = new String[] { "zero", "zero-quiet", "skip", "skip-quiet", "fail" };
        public boolean check(Context context, boolean negate) {
            JmlOptions options = JmlOptions.instance(context);
            String val = options.get(optionName());
            for (var s: values) {
                if (s.equals(val)) return true;
            }
            clError(context, "Command-line argument error: Expected one of " + String.join(" ",values) + " for " + optionName() + " : " + val);
            options.put(optionName(),(String)defaultValue());
            return false;
        }
    };

    public static final JmlOption PROPERTIES = new JmlOption("--properties",true,null,"Specifies the path to the properties file",null);

    public static final JmlOption DEFAULTS = new JmlOption("--defaults",true,"","Specifies various default behaviors: constructor:pure|everything",null);
    public static final JmlOption STATIC_INIT_WARNING = new JmlOption("-staticInitWarning",false,true,"Warns about missing static_initializer clauses",null);
    // Experimental
    public static final JmlOption DETERMINISM = new JmlOption("--determinism",false,true,"Experimental: enables better determinism (default is true)",null);

    public static final JmlOption OSNAME = new JmlOption("--os-name",true,"auto","Name of OS to use in selecting solver executable (default: auto detect; macos, linux, windows)",null);
    public static final JmlOption INLINE_FUNCTION_LITERAL = new JmlOption("--inline-function-literal",false,true,"Whether to inline function literals (default: true)",null);
    public static final JmlOption REQUIRE_WS = new JmlOption("--require-white-space",false,false, "Whether white space is required after the @ in a JML comment (default: false)", null);

    public static final JmlOption ALLOW_PURE_IN_SPECS = new JmlOption("--allow-pure-in-specs",false,false,"When on, allow pure (as well as spec_pure) methods to be used in specifications", null);

    // Obsolete
    public static final JmlOption PURITYCHECK = new JmlOption("--purity-check",false,true,"When on (the default), warnings for use of impure methods from system libraries are issued",null);
    { map.put("-purityCheck",PURITYCHECK); }

//    // Options Related to Specification Inference
//    public static final JmlOption INFER = new JmlOption("-infer",true,"POSTCONDITIONS","Infer missing contracts (postconditions (default), preconditions)","-command=infer");
//    public static final JmlOption INFER_DEBUG = new JmlOption("-infer-debug", false, false, "Enable debugging of contract inference", null);
//    public static final JmlOption INFER_TAG = new JmlOption("-infer-tag", true, true, "If true, inferred specifications are tagged with the key INFERRED", null);
//    public static final JmlOption INFER_PRECONDITIONS = new JmlOption("-infer-preconditions", true, true, "If n    public static final JmlOption pecified, the precondition of methods lacking preconditions will be set to true (otherwise inference is skipped).", null);
//    public static final JmlOption INFER_NO_EXIT = new JmlOption("-noexit",true,false,"Infer contracts (suppress exiting)","-command=infer-no-exit");
//    public static final JmlOption INFER_MINIMIZE_EXPRS = new JmlOption("-infer-minimize-expressions", false, false, "Minimize expressions where possible.", null);
//    public static final JmlOption INFER_DUMP_GRAPHS = new JmlOption("-infer-dump-graphs", false, false, "Dump any specification that would have been inferred to a file for offline analysis", null);
//
//    //
//    // Inference decides to write specs based on the following conditions
//    // 1) If -infer-persist-path is specified, specs are written to that directory (base)
//    // 2) Else, if -specspath is specified, specs are written to that directory (base)
//    // 3) Otherwise, we write the specs to the same directory were the java class source exists
//    //
//    public static final JmlOption INFER_PERSIST = new JmlOption("-infer-persist", true, "jml", "Persist inferred specs. If \"java\" specs are written to the source files. If \"jml\" (default) they are written to seperate .jml files (defaults to location of class source and can be overridden with -infer-persist-path and -specspath)", null);
//    public static final JmlOption INFER_PERSIST_PATH = new JmlOption("-infer-persist-path", true, null, "Specify output directory of specifications (overrides -specspath)", null);
//    public static final JmlOption INFER_MAX_DEPTH = new JmlOption("-infer-max-depth", true, 300, "The largest CFG we will agree to process", null);
//    public static final JmlOption INFER_TIMEOUT = new JmlOption("-infer-timeout", true, 300, "Give up inference after this many seconds. A value of -1 will wait indefinitely", null);
//    public static final JmlOption INFER_DEV_MODE = new JmlOption("-infer-dev-mode", false, false, "Special features for developers.", null);
//
//    //
//    // Options for turning on and off various inference techniques
//    //
//    public static final JmlOption INFER_ANALYSIS_TYPES = new JmlOption("-infer-analysis-types", true, "ALL", "Enables specific analysis types. Takes a comma separated list of analysis types. Support kinds are: REDUNDANT, UNSAT, TAUTOLOGIES, FRAMES, PURITY, and VISIBILITY", null);

//    // Obsolete
//    public static final JmlOption NO_RAC_SOURCEX = new JmlOption("-noRacSource",false,false,"RAC: Error messages will not include source information","--rac-show-source=false",true);
//    public static final JmlOption NO_RAC_CHECK_ASSUMPTIONSX = new JmlOption("-noRacCheckAssumptions",false,false,"RAC: Disables checking that assumptions hold","--rac-check-assumptions=false",true);
//    public static final JmlOption NO_RAC_JAVA_CHECKSX = new JmlOption("-noRacJavaChecks",false,false,"RAC: Disables explicit checking of Java language checks","--rac-java-checks=false",true);
//
//
//    static {
//        // FIXME - where did these come from - do we want them?
//        map.put("-nonnull",NONNULLBYDEFAULT);
//        map.put("-nullable",NULLABLEBYDEFAULT);
//    }

    final static private JmlOption[] hiddenOptions = new JmlOption[] { ALLOW_PURE_IN_SPECS, PURITYCHECK };
    final static private JmlOption[] obsoleteOptions = new JmlOption[] { PURITYCHECK };
    
    /** Holds the name of the option, as it is used in the command-line,
     * including the leading '-' characters.
     */
    final private String name;

    /** Whether the option takes an argument. that is, whether it is boolean */
    final private boolean hasArg;

    /** The default value of the option */
    final private Object defaultValue;

    /** The default to use for String options that would otherwise require an argument */
    public String enabledDefault = null;

    /** The help string for this option */
    final private String help;

    /** The canonical form for the option */
    final private String synonym;

    /** Private constructor to create instances.
     * @param s The option name, including any leading - character
     * @param defaultValue the default value for the option
     * @param hasArg Whether the option takes a (required) argument
     * @param help The associated help string
     * @param synonym an equivalent command-line argument
     */
    public JmlOption(/*@ non_null */ String s,
            boolean hasArg,
            Object defaultValue,
            /*@ non_null */ String help,
            /*@ nullable */ String synonym) {
        this(s,hasArg,defaultValue,help,synonym,null);
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
            /*@ nullable */ Object defaultValue,
            /*@ non_null */ String help,
            /*@ nullable */ String synonym,
            /*@ nullable */ String enabledDefault) {
        this.name = s;
        this.hasArg = hasArg;
        this.defaultValue = defaultValue;
        this.help = help;
        this.synonym = synonym;
        this.enabledDefault = enabledDefault;
        map.put(s, this);
        list.add(this);
    }

    /** Sets the value of the given option
     *
     * @param context the compilation context
     * @param option the option to set
     * @param value the value to give the option - boolean options
     *   interpret null or 'false' as false and non-null as true
     */
    public void put(Context context, String value) {
        Options.instance(context).put(this.name,value);
    }

    /** Sets the value of a boolean option, returning the previous value
     * @param context the compilation context
     * @param option the option name
     * @param value the new value of the option
     * @return true if the option was previously enabled, false otherwise
     */
    public boolean set(Context context, boolean value) {
        boolean b = this.isSet(context);
        Options.instance(context).put(this.optionName(),value?"true":null);
        return b;
    }

//    /** Return whether a boolean option is enabled in the given context
//     * @param context the compilation context
//     * @param option the option name
//     * @return true if the option is enabled, false otherwise
//     */
//    public static boolean isOption(Context context, JmlOption option) {
//        String val = Options.instance(context).get(option.name);
//        return interpretBoolean(val);
//    }

    // CAUTION: Should maintain that this is equivalent to the behavior in Option
    private static boolean interpretBoolean(String v) {
        return v != null;
    }

//    // FIXME - is this needed?
//    /** Return whether a boolean option is enabled in the given context
//     * @param context the compilation context
//     * @param option the option name by string (including leading -)
//     * @return true if the option is enabled, false otherwise
//     */
//    public static boolean isOption(Context context, String option) {
//        String v = value(context,option);
//        return interpretBoolean(v);
//    }

   
    /** This is used for those options that allow a number of suboptions; it tests whether
     * any one of the values is one of the comma-separated suboptions.
     */
    public boolean includes(Context context, String ... values) {
        String[] strings = this.value(context).split(",");
        for (var v: values) {
            for (var vv: strings) {
                if (v.equals(vv)) return true;
            }
        }
        return false;
    }
    
    /** Valid only for boolean options -- returns true or false per the option's value */
    public boolean isSet(Context context) {
        return Options.instance(context).isSet(this.optionName());
    }

    /** Valid only for boolean options -- returns true or false per the option's value */
    public boolean isUnset(Context context) {
        return Options.instance(context).isUnset(this.optionName());
    }

//    /** Return the value of an option with an argument
//     * @param context the compilation unit context
//     * @param option the option name
//     * @return the value of the argument, or its default
//     */
//    //@ nullable
//    public static String value(Context context, JmlOption option) {
//        return value(context,option.optionName());
//    }

//    /** Return the value of an option with an argument
//     * @param context the compilation unit context
//     * @param option the option name
//     * @return the value of the argument, or its default
//     */
//    //@ nullable
//    public static String value(Context context, String option) {
//        return Options.instance(context).get(option);
//    }
    
    /** Return the value of the option in the given context */
    public String value(Context context) {
        return Options.instance(context).get(this.optionName());
    }
    
    /** For options that implement this method, returns an int value appropriate to the option */
    public int getInt(Context context) { return -100; } // -100 is a value that flags it is widely wrong -- any JmlOption using this call should override it

    /** The name of the option, including any leading - sign
     */
     //@ non_null
    public String optionName() { return name; }

    /* Whether the option takes an argument
     * @see org.jmlspecs.openjml.OptionInterface#hasArg()
     */
    public boolean hasArg() { return hasArg; }

    /* The default value of the option
     * @see org.jmlspecs.openjml.OptionInterface#hasArg()
     */
    public Object defaultValue() { return defaultValue; }

    /* Whether the option is obsolete */
    public boolean obsolete() { return Arrays.asList(obsoleteOptions).contains(this); }

    /* Whether the option is hidden */
    public boolean hidden() { return Arrays.asList(hiddenOptions).contains(this); }

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
     * found and returning null if not found. Replaces inputs that have just one leading hyphen with two hyphens if necessary.
     * @param s the name of the option to find
     * @return the option found, or null
     */
    //@ ensures \result == null || \result.optionName().equals(s);
    //@ nullable
    static public JmlOption find(/*@ non_null */ String s) {
        var o = map.get(s);
        if (o == null) {
            if (s.length() >= 2 && s.charAt(1) != '-') o = map.get("-"+s);
        }
        return o;
    }

    /** Returns the JML command-line argument help information as a String
     *
     * @return the JML part of the command-line help information
     */
    //@ non_null
    public static String helpInfo() {
        StringBuilder sb = new StringBuilder();
        sb.append("JML options:").append(Strings.eol);
        for (var j : list) {
            if (j.hidden()) continue;
            sb.append("  ").append(j.optionName()).append(" ");
            // The count up to 26 is just to make for nice formatting
            for (int i = j.optionName().length(); i<26; i++) {
                sb.append(" ");
            }
            sb.append(j.help()).append(Strings.eol);
        }
        return sb.toString();
    }

    // FIXME - is this really needed?
    /** A helper function to extract values from the 'defaults' option */
    public static /*@ nullable */ String defaultsValue(Context context, String key, String def) {
        String defaultsValue = JmlOption.DEFAULTS.value(context);
        if (defaultsValue == null) return def;
        for (String s: defaultsValue.split(",")) {
            if (s.startsWith(key + ":")) {
                return s.substring(key.length()+1);
            }
        }
        return def;
    }

    /** Name of option, with any initial hyphens */
    public String toString() {
        return name;
    }
}
