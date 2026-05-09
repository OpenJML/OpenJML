/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import static com.sun.tools.javac.code.Flags.STATIC;
import static com.sun.tools.javac.code.Flags.UNATTRIBUTED;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;
import java.util.stream.Stream;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.IJmlClauseKind.ModifierKind;
import org.jmlspecs.openjml.IJmlClauseKind.TypeAnnotationKind;
import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;
import org.jmlspecs.openjml.JmlTree.IInJML;
import org.jmlspecs.openjml.JmlTree.JmlAnnotation;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlModifiers;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.Main.Cmd;
import org.jmlspecs.openjml.ext.JmlPrimitiveTypes;
import org.jmlspecs.openjml.ext.Modifiers;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.file.PathFileObject.CannotCreateUriError;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.JmlToken;
import com.sun.tools.javac.parser.JmlTokenizer;
import com.sun.tools.javac.tree.EndPosTable;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.BasicDiagnosticFormatter.BasicConfiguration.SourcePosition;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.DiagnosticSource;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.JavacMessages;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Position;
import com.sun.tools.javac.util.PropagatedException;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticFlag;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.JCDiagnostic.SimpleDiagnosticPosition;
import com.sun.tools.javac.util.JCDiagnostic.Warning;

/** This class holds a number of utility methods.  They could often be
 * static, but we make this a registerable tool, so that it can be 
 * overridden by some enterprising future person.
 */
public class Utils {
    
    // Static debugging flags -- do not use in any environment that multi-threads openjml

    /** cf isJML() */
    static private boolean isjml = System.getenv("NOJML")==null;

    /** true if openjml is set to process JML (rather than only java).
     * Recall that the openjdk/openjml has a bootstrap compilation cycle.
     * 'isjml' must be false for the bootstrap compilation and then 'true' to actually run openjml
     * See the use in the Makefile.
     * 
     * Utils.isJML() is also used to guard output statements in OpenJML that should not be output when in
     * usual Java-only mode.
     * 
     * Note that isjml is a static field -- it cannot be changed in a multi-threaded environment.
     * It is meant to be always true during regular OpenJML execution.
     */
    static public boolean isJML() {
        return isjml;
    }
    
    static public void setNoJML(boolean noJML) {
        isjml = !noJML;
    }

    // The order of the next several stastements is important-- OJ has to be read first. 
    // And these are not thread-safe -- they are meant solely for controlling debugging information.
    static private String debugstring = System.getenv("OJ");
    static private String[] debugkeys = debugstring == null ? null : debugstring.split(",");

    /** These fields. and similar ones in other files, are used to guard debugging statements that
     * are selectively enabled by setting the OJ environment variable.
     */
    static public boolean debugOptions = Utils.debug("options");
    static public boolean debugInst = Utils.debug("register") && isJML();
    
    static public final JavaFileObject NULL_SOURCE = null;
    
    /** True if OJ is set to anything at all, including an empty string */
    public static boolean debug() {
        return debugstring != null;
    }
    
    /** True iff OJ contains the given string */
    public static boolean debug(String key) {
        if (debugkeys == null) return false;
        // Note: streams cannot be reused
        var b = Arrays.stream(debugkeys).anyMatch(s->s.equals(key));
        // System.out.println("DEBUG " + key + " " + b);
        return b;
    }
    
    public static String debugValue(String key, String def) {
        if (debugkeys == null) return def;
        // Note: streams cannot be reused
        var opt = Arrays.stream(debugkeys).filter(s->s.startsWith(key)).findFirst();
        return opt.isEmpty() ? def : opt.get().substring(key.length());
    }
    
    ///////////////////////////////////////////////////////////////////////////////////////

    /** The context applicable for this instance of the Utils class. */
    public Context context;
    
    /** The Log object - do not use this directly - use log() instead */
    private Log log;
    
    /** The error and warning log. It is crucial that the log be obtained
     * lazily, and not before options are read; otherwise the Log object
     * is not properly initialized from the Java options. */
    public final Log log() {
        if (log == null) log = Log.instance(context);
        return log;
    }

    private JmlTypes jmltypes; // Do not use this value directly -- use jmltypes() instead
    
    /** The Types object */
    public JmlTypes jmltypes() {
        if (jmltypes == null) jmltypes = JmlTypes.instance(context);
        return jmltypes;
    }

    /** This field is used to restrict output during testing so as to 
     * make test results more deterministic (or to match old test results).
     * It is set when processing options. It is static and so is not thread-safe.
     */
    public boolean testingMode;
    
    /** The key to use to retrieve the instance of this class from the Context object. */
    //@ non_null
    public static final Context.Key<Utils> utilsKey =
            new Context.Key<Utils>();

    /** A method that returns the unique instance of this class for the given Context
     * 
     * @param context the Context whose JmlSpecs instance is wanted
     * @return the singleton instance (per Context) of this class
     */
    //@ non_null
    public static Utils instance(Context context) {
        Utils instance = context.get(utilsKey);
        if (instance == null) {
            instance = new Utils(context);  // registers itself
        }
        return instance;
    }

    /** Creates an instance in association with the given Context; 
     * @param context The compilation context
     */
    protected Utils(Context context) {
        if (Utils.debugInst) System.out.println("UTILS");
        this.context = context;
        context.put(utilsKey, this);
        init();
    }
    /** Initializes option-dependent fields */
    public void init() {
        Cmd cmd = Cmd.CHECK; // default
        boolean ok = true;
        String val = JmlOptions.instance(context).get(JmlOption.COMMAND.optionName());
        try {
            if (val != null) cmd = Cmd.valueOf(val.toUpperCase());
        } catch (IllegalArgumentException e) {
            Log.instance(context).error("jml.bad.command",val);
            ok = false;
        }
        this.cmd = cmd;
        this.rac = cmd == Cmd.RAC;
        this.esc = cmd == Cmd.ESC;
        this.check = cmd == Cmd.CHECK;
        this.compile = cmd == Cmd.COMPILE;
        this.infer   = cmd == Cmd.INFER;

        jmlverbose = JmlOption.VERBOSENESS.getInt(context);
        if (Options.instance(context).isSet("-verbose")) jmlverbose = Utils.JMLVERBOSE;

        String check = JmlOption.FEASIBILITY.value(context);
        if (check != null && check.startsWith(Strings.feas_debug)) {
            if (jmlverbose < Utils.PROGRESS) jmlverbose = Utils.PROGRESS;
        }

        testingMode = JmlOption.JMLTESTING.isSet(context);
    }

    /** Global utility value that enables printing of debugging or trace information. */
    public int jmlverbose = NORMAL; 
    static public final int QUIET = 0;
    static public final int NORMAL = 1;
    static public final int PROGRESS = 2;
    static public final int JMLVERBOSE = 3;
    static public final int JMLDEBUG = 4;

    public Main.Cmd cmd = null;
    
    // FIXME _ change to be setup by init()
    /** Do ESC - set by Main.setupOptions */
    public boolean esc = false;

    /** Do RAC - set by Main.setupOptions */
    public boolean rac = false;

    /** Do JML check only - set by Main.setupOptions */
    public boolean check = false;

    /** Do Java compilation - set by Main.setupOptions */
    public boolean compile = false;

    /** Do Contract Inference **/
    public boolean infer = false;
    
    /** Do Jmldoc  */
    public boolean doc = false;
    
    // These are now overloaded -- FIXME - need a better solution

    /** A bit that indicates that a declaration was declared within a JML annotation (so that it should not be visible to Java) */
    final public static long JMLBIT = 1L << 16; // Any bit that does not conflict with bits in com.sun.tools.javac.code.Flags.

    /** A bit that indicates that a declaration was declared somewhere within a JML annotation, but not nested within a class or method body that is also in the JML annotation */
    final public static long JMLBITTOP = 1L << 23; // Any bit that does not conflict with bits in com.sun.tools.javac.code.Flags.

    /** A bit that indicates that JML instrumentation has been added .... FIXME */
    final public static long JMLINSTRUMENTED = 1L << 19; // Any bit that does not conflict with bits in com.sun.tools.javac.code.Flags.

    /** A bit that indicates that a variable is local to an expression */
    final public static long JMLEXPRLOCAL = 1L << 21; // Any bit that does not conflict with bits in com.sun.tools.javac.code.Flags.

    // FIXME - describe  - used to be the DEFAULT flag
    final public static long JMLADDED = 1L << 32;
    
    // FIXME - needed? - var symbols only?
    final public static long JMLINSTANCE = 1L << 36;

    /** Tests whether the JML flag is set in the given modifiers object
     * @param mods the instance of JCModifiers to test
     * @return true if JML is set
     */
    public static boolean isJML(/*@ nullable */ JCModifiers mods) {
        return mods != null && (mods.flags & JMLBIT) != 0;
    }
    
    /** Tests whether the JML flag is set in the given bit-vector
     * @param flags the bit-array to test
     * @return true if JML is set
     */
    public static boolean isJML(long flags) {  // FIXME - make static and some other of these methods
        return (flags & JMLBIT) != 0;
    }

    public boolean isJMLTop(/*@ nullable */ JCModifiers mods) {
        return mods != null && (mods.flags & JMLBITTOP) != 0;
    }
    
    /** Sets the JML flag in the given modifiers.
     * 
     * @param mods The modifiers in which to set the JML flag
     */
    public static void setJML(/*@ non_null */ JCModifiers mods) {
        mods.flags |= JMLBIT;
    }

    /** Sets the JMLBIT flag in the flags bit-vector */
    public static long setJML(long flags) {
        return flags | JMLBIT;
    }

    /** Unsets the JML flag in the given modifiers.
     * 
     * @param mods The modifiers in which to set the JML flag
     */
    public static void unsetJML(/*@ non_null */ JCModifiers mods) {
        mods.flags &= ~JMLBIT;
    }

    public boolean isJMLTop(long flags) {
        return (flags & JMLBITTOP) != 0;
    }

    public void setJMLTop(/*@ non_null */ JCModifiers mods) {
        mods.flags |= JMLBITTOP;
    }

    /** Tests whether the given tree was directly parsed as part of JML annotation;
     * nested declarations that are not themselves directly in a JML comment will return false, 
     * even if they are nested in a class that itself is directly in a JML comment.
     */
    public boolean isJML(JCTree t) {
        return (t instanceof IInJML) && ((IInJML)t).isJML();
    }


    // FIXME - document
    public boolean isInstrumented(long flags) {
        return (flags & JMLINSTRUMENTED) != 0;
    }

    // FIXME - document
    public void setInstrumented(/*@ non_null */JCModifiers mods) {
        mods.flags |= JMLINSTRUMENTED;
    }

    /** Returns true if the flags indicate this is a generated default constructorn */
    public static boolean isGeneratedConstructor(MethodSymbol methodSym) {
        return (methodSym.flags() & Flags.GENERATEDCONSTR) != 0;
    }

    /** Returns true if the file is a specification (.jml) file */
    public boolean isSpecFile(JavaFileObject file) {
        // A .jml file is Kind.OTHER, but might (eventually?) be Kind.JML
        return file.getKind() != JavaFileObject.Kind.SOURCE;
    }

    /** Creates an annotation symbol from the fully qualified name for the
     * annotation; generally the result is cached.
     * @param fullyQualifiedName the fully qualified name
     * @return the annotation symbol
     */
    public ClassSymbol createClassSymbol(String fullyQualifiedName) {
        return ClassReader.instance(context).
                enterClass(Names.instance(context).fromString(fullyQualifiedName));
    }

    public ClassSymbol createClassSymbol(Symbol.ModuleSymbol msym, String fullyQualifiedName) {
        var cr = ClassReader.instance(context);
        var saved = cr.currentModule;
        cr.currentModule = msym;
        var csym = cr.enterClass(Names.instance(context).fromString(fullyQualifiedName));
        cr.currentModule = saved;
        return csym;
    }

    // FIXME - should perhaps not be in this class
    /** Returns true if the given symbol has a helper annotation
     * 
     * @param symbol the symbol to check
     * @return true if there is a helper annotation
     */
    public void setHelper(/*@non_null*/ MethodSymbol symbol) {
        var mods = JmlSpecs.instance(context).getLoadedSpecs(symbol).mods;
        JmlToken tok = new JmlToken( Modifiers.HELPER, Position.NOPOS, Position.NOPOS);
        ((JmlModifiers)mods).jmlmods.add(tok);
    }
    
    public boolean isHelper(/*@non_null*/ MethodSymbol symbol) {
        return hasModifier(JmlSpecs.instance(context).getLoadedSpecs(symbol).mods, Modifiers.HELPER);
    }
    
    public boolean isModel(/*@non_null*/ ClassSymbol symbol) {
        return hasModifier(JmlSpecs.instance(context).getLoadedSpecs(symbol).modifiers, Modifiers.MODEL);
    }
    
    public boolean isModel(/*@non_null*/ MethodSymbol symbol) {
        return hasModifier(JmlSpecs.instance(context).getLoadedSpecs(symbol).mods, Modifiers.MODEL);
    }

    public boolean isModel(/*@non_null*/ VarSymbol symbol) {
        var fs = JmlSpecs.instance(context).getLoadedSpecs(symbol);
        return fs != null && hasModifier(fs.mods, Modifiers.MODEL);
    }

    public boolean isGhost(/*@non_null*/ VarSymbol symbol) {
        var fs = JmlSpecs.instance(context).getLoadedSpecs(symbol);
        return fs != null && hasModifier(fs.mods, Modifiers.GHOST);
    }
    
    public boolean isGhostOrModel(/*@non_null*/ VarSymbol symbol) {
        var fs = JmlSpecs.instance(context).getLoadedSpecs(symbol);
        return fs != null && hasModifier(fs.mods, Modifiers.GHOST, Modifiers.MODEL);
    }

    public boolean isModel(/*@non_null*/ Symbol symbol) {
        if (symbol instanceof ClassSymbol) return isModel((ClassSymbol)symbol);
        if (symbol instanceof MethodSymbol) return isModel((MethodSymbol)symbol);
        if (symbol instanceof VarSymbol) return isModel((VarSymbol)symbol);
        return false;// This should really be an error FIXME
    }

    /** Determines which OS we are in and returns an identifying string */
    public static String identifyOS(Context context) {
        String sp = context == null ? null : JmlOption.OSNAME.value(context);
        if (sp == null || sp.isEmpty() || "auto".equals(sp)) sp = System.getProperty("os.name");
        if (sp.contains("mac") || sp.contains("Mac")) return "macos";
        if (sp.contains("lin") || sp.contains("Lin")) {
            if ("aarch64".equals(System.getProperty("os.arch"))) return "linux-arm64";
            return "linux";
        }
        if (sp.contains("win") || sp.contains("Win")) return "windows";
        return sp;
    }
    
    /** Returns true if the given symbol is marked static or is a member of a JML interface
     * that is not marked as 'instance'
     */
    public boolean isJMLStatic(Symbol sym) {
        // non-static Simple identifier is OK
        // If the owner of the field is an interface, it
        // is by default static. However, it might be a
        // JML field marked as instance.
        if (sym.owner == null) {
            if ((sym.flags() & STATIC) == 0) return false;
        } else {
            if (!sym.isStatic()) return false;
            if ((sym.flags() & STATIC) == 0 || (sym.flags_field & Utils.JMLINSTANCE) != 0) return false;
        }
        if (isJML(sym.flags())) {
            Symbol csym = sym.owner;
            if (csym != null && (csym.flags() & Flags.INTERFACE) != 0) {
                // TODO - should cleanup this reference to JmlAttr from Utils
                if (Utils.instance(context).hasModifier(sym,Modifiers.INSTANCE)) return false;
            } 
        } else if (Utils.instance(context).hasModifier(sym,Modifiers.INSTANCE)) return false;
        return true;
    }

    public boolean isJMLStatic(JCModifiers mods, ClassSymbol csym) {
        // non-static Simple identifier is OK
        // If the owner of the field is an interface, it
        // is by default static. However, it might be a
        // JML field marked as instance.
        if ((csym.flags() & Flags.INTERFACE) != 0) {
            // TODO - should cleanup this reference to JmlAttr from Utils
            if (hasModifier(mods,Modifiers.INSTANCE)) return false;
            if ((mods.flags & STATIC) == 0 || (mods.flags & Utils.JMLINSTANCE) != 0) return false;
        } 
        return ((mods.flags & Flags.STATIC) != 0);
    }

    // FIXME - document
    public Object envString(/*@ non_null */Env<AttrContext> env) {
        return (env.tree instanceof JCCompilationUnit ? 
                ((JCCompilationUnit)env.tree).sourcefile : 
                    env.tree instanceof JCClassDecl ? 
                            ((JCClassDecl)env.tree).sym.flatName() : 
                                env.tree.getClass());
    }

    // FIXME - move these
    
    /** Returns true if no standard modifiers or annotations have been set
     * @param mods the modifiers structure to check
     * @return true if any standard flags or annotations are set
     */  // FIXME - should this check for just JML annotations?
    public boolean hasNone(/*@ nullable */JCModifiers mods) {
        return mods == null || ((mods.flags&Flags.StandardFlags) == 0 && (mods.annotations == null || mods.annotations.isEmpty()));
    }

    /** Returns true if any of the specified Java modifiers is set
     * @param mods the modifiers structure to check
     * @return true if any of the given flags are set
     */
    public boolean hasAny(/*@ nullable */JCModifiers mods, long flags) {
        return mods != null && ((mods.flags&flags) != 0);
    }

    /** Returns non-zero if any Java modifiers other than those specified are set
     * @param mods the modifiers structure to check
     * @return bit-vector of the offending flags
     */
    public long hasOnly(/*@ nullable */JCModifiers mods, long flags) {
        if (mods == null) return 0;
        return mods.flags & ~flags & Flags.StandardFlags;
    }

    /** Finds whether a specified annotation is present in the given modifiers,
     * returning it if it is; this method requires that the annotations have
     * already been attributed.
     * @param mods the modifiers to search
     * @param m the Name (fully qualified) of the annotation type to find
     * @return the annotation AST if present, null if not
     */
    //@ nullable
    public JmlTree.JmlAnnotation findMod(/*@ nullable */ JCModifiers mods, /*@ non_null */Name m) {
        if (mods == null) return null;
        return findMod(mods.annotations, m);
    }
    //@ nullable
    public JmlTree.JmlAnnotation findMod(List<JCAnnotation> anns, /*@ non_null */Name m) {
        for (JCTree.JCAnnotation a: anns) {
            Type t = a.annotationType.type;
            if (t != null) {
                // FIXME - can this be done by comparing symbols rather than strings
                if (((Symbol.ClassSymbol)t.tsym).fullname.equals(m)) return (JmlTree.JmlAnnotation)a; 
            } else {
                // FIXME this is not going to work for unattributed and not-fully qualified annotations
                String s = a.annotationType.toString();
                if (m.toString().equals(s)) return (JmlTree.JmlAnnotation)a;
                if (m.toString().equals(Strings.jmlAnnotationPackage + "."+s)) return (JmlTree.JmlAnnotation)a; // FIXME - fix attribution of annotations in MemberEnter
            }
        }
        return null;
    }

    public JmlTree.JmlAnnotation findMod(/*@ nullable */ JCModifiers mods, /*@ non_null */IJmlClauseKind.ModifierKind ... tarr) {
        if (mods == null) return null;
        for (var ta: tarr) {
            for (JCTree.JCAnnotation a: mods.annotations) {
                var ja = (JmlTree.JmlAnnotation)a;
                if (ja.kind == ta) return ja;
            }
        }
        return null;
    }
    
    public boolean hasModifier(/*@ non_null */ Symbol sym, /*@ non_null */IJmlClauseKind.ModifierKind ... tarr) {
        JmlModifiers mods = null;
        if (sym instanceof Symbol.MethodSymbol m) {
            var sp = JmlSpecs.instance(context).get(m);
            //if (sp == null) System.out.println("NULL SPECS FOR " + sym);
            if (sp != null) mods = (JmlModifiers)sp.mods;
        }
        else if (sym instanceof Symbol.ClassSymbol c) {
            var sp = JmlSpecs.instance(context).get(c);
            //if (sp == null) System.out.println("NULL SPECS FOR " + sym);
            if (sp != null) mods = sp.modifiers;
        }
        else if (sym instanceof Symbol.VarSymbol c) {
            var sp = JmlSpecs.instance(context).get(c);
            //if (sp == null) System.out.println("NULL SPECS FOR " + sym);
            if (sp != null) mods = sp.mods;
        } else {
            // This can be a package symbol, or the owner of 'Array'
            // In any case there is no modifier
            return false;
        }
        // else error -- FIXME
        if (mods != null) {
            for (var ta: tarr) {
                for (var t: mods.jmlmods) {
                    if (t.jmlclausekind == ta) return true;
                }
            }
        }
        return false;
    }
    
    /** Has one of the listed modifiers */
    public boolean hasModifier(/*@ nullable */ JCModifiers mods, /*@ non_null */IJmlClauseKind.ModifierKind ... tarr) {
        if (mods instanceof JmlModifiers jmods) {
            for (var ta: tarr) {
                for (var t: jmods.jmlmods) {
                    if (t.jmlclausekind == ta) return true;
                }
            }
        }
        return false;
    }
    
    /** Return one of the listed modifiers or null */
    public JmlToken findModifier(/*@ nullable */ JCModifiers mods, /*@ non_null */IJmlClauseKind.ModifierKind ... tarr) {
        if (mods instanceof JmlModifiers jmods) {
            for (var ta: tarr) {
                for (var t: jmods.jmlmods) {
                    if (t.jmlclausekind == ta) return t;
                }
            }
        }
        return null;
    }
    
    public boolean hasJavaAnnotation(Symbol sym, JmlAnnotation annotation) {
        return sym.getAnnotationMirrors().stream().anyMatch( a-> annotation.type == a.type);
    }

    public boolean hasMod(JCModifiers mods, ModifierKind... ata) {
        if (mods != null) for (var ta: ata) {
            if (mods instanceof JmlModifiers) {
                JmlModifiers jmods = (JmlModifiers)mods;
                if (jmods.jmlmods != null) for (var t: jmods.jmlmods) {
                    if (t.jmlclausekind == ta) return true;
                }
            }
            var a = findMod(mods, ta); // Finds annotation
            if (a != null) return true;
        }
        return false;
    }

    public boolean hasModOrAnn(JmlModifiers jmods, ModifierKind... ata) {
        if (jmods != null) for (var ta: ata) {
            if (jmods.jmlmods != null) for (var t: jmods.jmlmods) {
                if (t.jmlclausekind == ta) return true;
            }
            var a = findMod(jmods, ta); // Finds annotation
            if (a != null) return true;
        }
        return false;
    }

    public int locNonNullAnnotation(JCTree.JCVariableDecl vd) {
        int p = locMod(vd.mods, Modifiers.NON_NULL);
        if (p != Position.NOPOS) return p;
        var a = findMod(vd.mods, Modifiers.NON_NULL);
        if (a != null) return a.pos;
        var t = vd.vartype;
        while (true) {
            if (t instanceof JCTree.JCAnnotatedType at) {
                var n = findMod(at.annotations, Names.instance(context).fromString("org.jmlspecs.annotation.NonNull"));
                if (n != null) return n.pos;
                return Position.NOPOS;
            } else if (t instanceof JCTree.JCArrayTypeTree arr) {
                t = arr.elemtype;
                continue;
            } else {
                return Position.NOPOS;
            }
        }
    }

    // FIXME - would prefer to issue a DiagnosticPosition
    public int locMod(JCModifiers mods, ModifierKind... ata) {
        for (var ta: ata) {
            if (mods instanceof JmlModifiers) {
                for (var t: ((JmlModifiers)mods).jmlmods) if (t.jmlclausekind == ta) {
                    return t.pos;
                }
            }
            var a = findMod(mods, ta);
            if (a != null) return a.pos;
        }
        return com.sun.tools.javac.util.Position.NOPOS;
    }

    /** Finds whether a specified annotation is present in the given modifiers,
     * returning it if it is; this method requires that the annotations have
     * already been attributed.
     * @param mods the modifiers to search
     * @param asym the symbol of the annotation type to find
     * @return the annotation AST if present, null if not
     */
    public JmlTree.JmlAnnotation findMod(/*@ nullable */ JCModifiers mods, /*@ non_null */Symbol asym) {
        if (mods == null) return null;
        for (JCTree.JCAnnotation a: mods.annotations) {
            Type t = a.annotationType.type;
            if (t != null) {
                if (t.tsym.equals(asym)) return (JmlTree.JmlAnnotation)a; 
            } else {
                // FIXME this is not going to work for unattributed and not-fully qualified annotations, and at best is a real hack
                String s = a.annotationType.toString();
                if (asym.flatName().toString().endsWith(s)) return (JmlTree.JmlAnnotation)a;
            }
        }
        return null;
    }
    
    /** Finds a field of a class with a given name.
     */
    public Symbol findFieldMember(TypeSymbol sym, String name) {
        Name n = Names.instance(context).fromString(name);
        for (Symbol s: sym.getEnclosedElements()) {
            if (s instanceof VarSymbol && s.name.equals(n)) return s;
        }
        return null;
    }

    public Symbol findStaticMember(TypeSymbol sym, String name) {
        Name n = Names.instance(context).fromString(name);
        for (Symbol s: sym.getEnclosedElements()) {
            if (s.isStatic() && s.name.equals(n)) return s;
        }
        return null;
    }

    public Symbol findStaticMethod(TypeSymbol sym, String name, Type ...argtypes) {
        Name n = Names.instance(context).fromString(name);
        x: for (Symbol s: sym.getEnclosedElements()) {
            if (s.isStatic() && s instanceof MethodSymbol && s.name.equals(n)) {
                MethodSymbol ms = (MethodSymbol)s;
                if (argtypes.length != ms.params.length()) continue;
                for (int i=0; i< argtypes.length; i++) {
                    if (!jmltypes.isSameType(argtypes[i], ms.params.get(i).type)) continue x;
                }
                return s;
            }
        }
        return null;
    }

    /** Returns true if the given String ends with a valid JML specification suffix, including the
     * period; there are no further checks that the argument is a sensible filename.
     * @param filename the String to check
     * @return true if the input ends in a valid JML suffix
     */
    public boolean hasSpecSuffix(String filename) {
        return filename.endsWith(Strings.specsSuffix);
    }

    /** Returns true if the given String ends with a valid Java suffix, including the
     * period; there are no further checks that the argument is a sensible filename.
     * @param filename the String to check
     * @return true if the input ends in a valid Java suffix
     */
    public boolean hasJavaSuffix(String filename) {
        return (filename.endsWith(Strings.javaSuffix));
    }
    
    @SafeVarargs
    public static <T> T[] concat(T[] array1, T[] ... arrays) {
        int n = array1.length;
        for (var a: arrays) n += a.length;
        T[] res = java.util.Arrays.copyOf(array1, n);
        int k = array1.length;
        for (var a: arrays) { System.arraycopy(a, 0, res, k, a.length); k += a.length; }
        return res;
    }

    public static <T> T[] concat2(T[] array1, T[] array2) {
        T[] res = java.util.Arrays.copyOf(array1, array1.length + array2.length);
        System.arraycopy(array2, 0, res, array1.length, array2.length);
        return res;
    }

    /** A little class to encapsulate elapsed wall-clock time */
    public static class Timer {
        /** Time the object was constructed or reset */
        protected long startTime;

        /** Constructs a new object, marking the time */
        public Timer() {
            reset();
        }

        /** Resets the timestamp */
        public void reset() {
            startTime = System.currentTimeMillis();
        }

        /** Returns the wall-clock time elapsed since object construction or the
         * most recent call to reset
         * 
         * @return elapsed time in milliseconds
         */
        public long elapsed() {
            return System.currentTimeMillis() - startTime;
        }
    }

    // FIXME - this is in the wrong class
    /** This method is never actually executed.  It is here to provide a
     * convenient signature for a method used by ESC - that maps each class
     * to a distinct integer - not necessarily its hashCode (which are not
     * necessarily unique).
     * @param c
     * @return a distinct integer for the given class
     */
    public int distinct(Class<?> c) {
        return c.hashCode();
    }

    // FIXME - document
    public void notImplemented(DiagnosticPosition pos, String feature) {
        // FIXME - control with an option
        if (rac) warning(pos,"jml.not.implemented.rac",feature);
        else if (esc) warning(pos,"jml.not.implemented.esc",feature);
    }
    
    /** Finds OpenJML properties files in pre-defined places, reading their
     * contents into the Properties object that is returned.
     */
    public static Properties findProperties(Context context) {
        boolean verbose = debugOptions;

        if (context == null) context = new Context();
        PrintWriter noticeWriter = Log.instance(context).getWriter(WriterKind.NOTICE);
        Properties properties = new Properties();
        
        // Initialize with builtin defaults
        //setPropertiesFromOptionsDefaults(properties);
        
        // Override with any system properties
        properties.putAll(System.getProperties());
        
        // Load properties files found in these locations:
        // These are read in inverse order of priority, so that later reads
        // overwrite the earlier ones.
        
        // In installation directory
        {
            String s = Main.install + "/" + Strings.propertiesFileName;
            try {
                boolean found = readProps(properties,s);
                if (verbose) {
                    if (found) noticeWriter.println("Properties read from installation directory: " + s);
                    else noticeWriter.println("No properties found in installation directory: " + s);
                }
            } catch (Exception e) {
                noticeWriter.println("Failed to read property file " + s + " " + e);
            }
        }
        
        
//        // On the system classpath
//        {
//            URL url2 = ClassLoader.getSystemResource(Strings.propertiesFileName);
//            if (url2 != null) {
//                String s = url2.getFile();
//                try {
//                    boolean found = readProps(properties,s);
//                    if (verbose) {
//                        if (found) noticeWriter.println("Properties read from system classpath: " + s);
//                        else noticeWriter.println("No properties found on system classpath: " + s);
//                    }
//                } catch (java.io.IOException e) {
//                    noticeWriter.println("Failed to read property file " + s); // FIXME - review
//                }
//            }
//        }

        // In the user's home directory
        // Note that this implementation does not read through symbolic links
        {
            String s = System.getProperty("user.home") + "/" + Strings.propertiesFileName;
            try {
                boolean found = readProps(properties,s);
                if (verbose) {
                    if (found) noticeWriter.println("Properties read from user's home directory: " + s);
                    else noticeWriter.println("No properties found in user's home directory: " + s);
                }
            } catch (Exception e) {
                noticeWriter.println("Failed to read property file " + s + " " + e);
            }
        }

        // In the working directory
        {
            String s = System.getProperty("user.dir") + "/" + Strings.propertiesFileName;
            try {
                boolean found = readProps(properties,s);
                if (verbose) {
                    if (found) noticeWriter.println("Properties read from working directory: " + s);
                    else noticeWriter.println("No properties found in working directory: " + s);
                }
            } catch (Exception e) {
                noticeWriter.println("Failed to read property file " + s + " " + e);
            }
        }

        // Set from environment variables
        // This works for options whose names do not contain underscores or periods
        // System property names typically have periods, so env.vars. cannot fill in for actual properties
        {
            String prefix = "OPENJML_";
            for (var p : System.getenv().entrySet()) {
                if (p.getKey().startsWith(prefix)) {
                    String kk = Strings.optionPropertyPrefix + p.getKey().substring(prefix.length());
                    kk = kk.replace('_','-');
                    properties.put(kk, p.getValue());
                }
            }
        }
        
        if (verbose) {
            // Print out the properties
            for (String key: new String[]{"user.home","user.dir"}) {
                noticeWriter.println("Environment:    " + key + " = " + System.getProperty(key));
            }
            for (java.util.Map.Entry<Object,Object> entry: properties.entrySet()) {
                noticeWriter.println("Local property: " + entry.getKey() + " = " + entry.getValue());
            }
        }
        return properties;
    }

    /** Reads properties from the given file into the given Properties object, 
     * adding to or overriding any properties already present.
     * @param properties the object to add properties to
     * @param filename the file to read properties from
     * @return true if the file was found and read successfully
     */
    public static boolean readProps(Properties properties, String filename) throws java.lang.Exception {
        // Note: Java, or at least this code, does not read through Cygwin symbolic links
        Path filepath = Paths.get(filename);
        if (filepath.toFile().exists()) {
            try (InputStream stream = Files.newInputStream(filepath)) {
                properties.load(stream);
                return true;
            } 
        } else {
            return false;
        }
    }
    
    // FIXME: Move these to JmlTypes?
    
    public boolean isJavaOrJmlPrimitiveType(TypeSymbol ct) {
        return isJavaOrJmlPrimitiveType(ct.type);
    }

    public boolean isJavaOrJmlPrimitiveType(Type ct) {
        return ct.isPrimitive() || jmltypes().isJmlType(ct);
    }

    public boolean isJavaOrJmlPrimitiveOrVoidType(Type ct) {
        return ct.isPrimitiveOrVoid() || jmltypes().isJmlType(ct);
    }

    /** A special method to check the type of arguments; isSameType might fail because of different wildcard type arguments of Class<>. */
    public boolean isClassType(Type ct) {
        return ct.tsym == Symtab.instance(context).classType.tsym;
    }
    
    public Type headType(Type t) {
        while (t instanceof Type.ArrayType at) { t = at.getComponentType(); }
        return t;
    }

    // Includes self
    public java.util.List<ClassSymbol> parents(TypeSymbol ct, boolean includeEnclosingClasses) {
        return parents(ct, includeEnclosingClasses, true);
    }
    public java.util.List<ClassSymbol> parents(TypeSymbol ct, boolean includeEnclosingClasses, boolean includeSelf) {
        ArrayList<ClassSymbol> interfaces = new ArrayList<ClassSymbol>(20);
        if (objectSym == null) objectSym = (Symbol.ClassSymbol)Symtab.instance(context).objectType.tsym;
        if (ct == objectSym && !includeSelf) return interfaces;
        if (isJavaOrJmlPrimitiveType(ct.type)) {
            if (includeSelf) interfaces.add((ClassSymbol)ct);
            return interfaces;
        }

        if (ct instanceof Symbol.TypeVariableSymbol) {
            ct = ct.type.getUpperBound().tsym;
            // FIXME - what if bound is also a type variable?
        }
        if (!(ct instanceof ClassSymbol)) return interfaces;
        ClassSymbol c = (ClassSymbol)ct; // FIXME - what if we want the parents of a type variable?
        List<ClassSymbol> classes = new LinkedList<ClassSymbol>();
        Set<ClassSymbol> interfaceSet = new HashSet<ClassSymbol>();
        ClassSymbol cc = c;
        List<ClassSymbol> todo = new LinkedList<ClassSymbol>();
        todo.add(c);
        while (!todo.isEmpty()) {
            cc = todo.remove(0);
            if (cc == null) continue;
            if (classes.contains(cc)) {
                classes.remove(cc);
                classes.add(0,cc);
                continue;
            }
            if (includeEnclosingClasses) {
                Symbol sym =  cc.getEnclosingElement();
                while (sym instanceof MethodSymbol) sym = sym.owner;
                if (sym instanceof ClassSymbol) todo.add((ClassSymbol)sym); // FIXME - can this be an interface?
            }
            var sc = cc.getSuperclass().tsym;
            if (sc != null) todo.add((ClassSymbol)sc);
            classes.add(0,cc);
        }
        for (ClassSymbol ccc: classes) {
            List<Type> ifs = ccc.getInterfaces();
            for (Type ifc : ifs) {
                ClassSymbol sym = (ClassSymbol)ifc.tsym;
                if (interfaceSet.add(sym)) interfaces.add(sym);
            }
        }
        if (!includeSelf) classes.remove(classes.size()-1);
        // FIXME - the interfaces are not in a good order
        int i = 0;
        while (i < interfaces.size()) {
            ClassSymbol ccc = interfaces.get(i++);
            List<Type> ifs = ccc.getInterfaces();
            for (Type ifc : ifs) {
                ClassSymbol sym = (ClassSymbol)ifc.tsym;
                if (interfaceSet.add(sym)) interfaces.add(sym);
                // FIXME - what about the owners of interfaces
            }
        }
        classes.remove(objectSym);
        interfaces.addAll(classes);
        interfaces.add(0,objectSym);
        return interfaces;
    }
    
    public com.sun.tools.javac.util.List<VarSymbol> collectFields(ClassSymbol baseType, java.util.function.Predicate<VarSymbol> a) {
        com.sun.tools.javac.util.ListBuffer<VarSymbol> list = new com.sun.tools.javac.util.ListBuffer<VarSymbol>();
        for (var cc : parents(baseType, false)) {
            for (var sym : cc.getEnclosedElements()) {
                //System.out.println("COLLECT " + sym + " " + sym.getClass() + " " + (sym instanceof VarSymbol vs && a.test(vs)));
                if (sym instanceof VarSymbol vs && a.test(vs)) list.add(vs);
            }
        }
        return list.toList();
    }



    private ClassSymbol objectSym = null;

    // Returns all methods that are overridden by the argument, including self // FI(XME - review for order
    public java.util.List<MethodSymbol> parents(MethodSymbol m, boolean includeSelf) {
        List<MethodSymbol> methods = new LinkedList<MethodSymbol>();
        if (isJMLStatic(m)) {
            if (includeSelf) methods.add(m); 
        } else if (m.isConstructor() ) {
            if (includeSelf) methods.add(m);
        } else {
            // FIXME - the 'true' here should be false -- it seems that model interface enclosed within 
            // and extending java interfaces do not show those interfaces in getInterfaces()
            var classes = parents((ClassSymbol)m.owner, false);
            //if (m.toString().contains("sequential")) System.out.println("CLASSES " + m.owner + " " + m + " " + m.isDefault() + " " + Arrays.toString(classes.toArray()));
            for (ClassSymbol c: classes) {
                for (Symbol mem: c.members().getSymbols(
                        mem->(mem instanceof MethodSymbol && (includeSelf || m.owner != mem.owner) &&
                                mem.name == m.name))) {
                    boolean ok = m.overrides(mem, (TypeSymbol)m.owner, Types.instance(context), true, false);
                    //if (m.toString().contains("sequential")) System.out.println("  CHECKING " + m.owner + "#" + m + " " + mem.owner + "#" + mem + " " + ((MethodSymbol)mem).isDefault() + " " + ok);
                    if (ok) methods.add((MethodSymbol)mem);
                }
            }
        }
        //if (m.toString().contains("sequential")) { System.out.println("  RESULT " + m + " : " + join(",",methods,mm->mm.owner.toString())); Utils.dumpStack(); }
        return methods;
    }

    public static <T> String join(CharSequence delim, java.util.Collection<T> list) { return Utils.join(delim, list.stream(), x->String.valueOf(x)); }
    public static <T,U> String join(CharSequence delim, java.util.Collection<T> list, java.util.function.Function<T,U> f) { return Utils.join(delim, list.stream(), f); }
    public static <T,U> String join(CharSequence delim, java.util.stream.Stream<T> list) { return Utils.join(delim, list, x->x); }
    public static <T,U> String join(CharSequence delim, java.util.stream.Stream<T> list, java.util.function.Function<T,U> f) { return String.join(delim, list.map(mm->String.valueOf(f.apply(mm))).collect(java.util.stream.Collectors.toList())); }
    public static <T> String join(CharSequence delim, T[] list) { return Utils.join(delim, Stream.of(list), x->x); }

    /** Creates the location prefix including the colon without any message;
     * 'pos' is the position in the file given by log().currentSource(). */
    public String locationString(int pos) {
        return locationString(pos, null);
    }

    /** Creates the location prefix including the colon without any message;
     * 'pos' is the position in the file given by source or if source is null, by log.currentSource(). */
    public String locationString(int pos, /*@ nullable */ JavaFileObject source) {
        return locationString(new SimpleDiagnosticPosition(pos), source);
    }

    /** Creates the location prefix including the ending colon without any message;
     * 'pos' is the position in the file given by source or if source is null, by log.currentSourceFile(). */
    public String locationString(DiagnosticPosition pos, /*@ nullable */ JavaFileObject source) {
        // TODO - there must be a better way to format this string
        DiagnosticSource ds = source == null ? log().currentSource() : new DiagnosticSource(source, log);
        JCDiagnostic diag = JCDiagnostic.Factory.instance(context).note(ds, pos, "empty", "");
        String msg = diag.toString().replace("Note: ", "");
        int k = msg.indexOf(':');
        k = msg.indexOf(':',k+1);
        msg = msg.substring(0,k+1);
        return msg;
    }
    
    public boolean isTypeChecked(ClassSymbol sym) {
        ClassSymbol c = sym;
        if (c == null) return false;
        return ((c.flags_field & UNATTRIBUTED) == 0);
    }

    public Symbol topLevelEnclosingType(Symbol item) {
        // Enclosing elements can be either methods or classes/interfaces
        // The top level type will be enclosed by a package
        Symbol sym = item;
        do {
            item = sym;
            sym = item.getEnclosingElement();
        } while (!(sym instanceof Symbol.PackageSymbol));
        return item;
    }
    
    /** Java visibility, ignoring the access of the containing class */
    public boolean locallyVisible(Symbol base, Symbol parent, long flags) {
        if (base == parent) return true; // Everything is visible in its own class
        Symbol topbase = topLevelEnclosingType(base);
        Symbol parentbase = topLevelEnclosingType(parent);
        if (topbase == parentbase) return true; // Everything is visible if they share a top-level class
        if ((flags & Flags.PUBLIC) != 0) return true; // public things are always visible
        if (parent.isInterface()) return true; // everything in an interface is public and hence visible
        if ((flags & Flags.PRIVATE) != 0) return false; // Private things are never visible outside their own top-level class
        if (base.packge().equals(parent.packge())) return true; // Protected and default things are visible if in the same package
        if ((flags & Flags.PROTECTED) == 0) return false; // Otherwise default things are not visible
        // Just left with protected things, so is base a subclass of parent
        while (base instanceof Symbol.TypeVariableSymbol) base = ((Symbol.TypeVariableSymbol)base).type.getUpperBound().tsym;
        return base.isSubClass(parent, Types.instance(context)); // Protected things are visible in subclasses
    }

    /** JML visibility, ignoring the access of the containing class */
    public boolean locallyJMLVisible(Symbol base, Symbol parent, long flags) {
        if (locallyVisible(base,parent,flags)) return true;
        if (hasSpecPublic(parent)) return true;
        return false;
        // FIXME - needs to check spec protected; needs to check actual symbol
    }


    /** Returns true if a declaration with the given flags is visible in the
     * 'base' class when declared in the 'parent' class. This is standard
     * Java visibility.
     */
    public boolean visible(Symbol base, Symbol parent, long flags) {
        Symbol gp = parent;
        while (gp instanceof ClassSymbol) {
            if (!locallyVisible(base,gp,gp.flags())) return false;
            gp = gp.getEnclosingElement();
        }
        return locallyVisible(base, parent, flags);
    }
    
    /** Returns true if a declaration with the given flags is visible in the
     * 'base' class when declared in the 'parent' class. This is JML visibility.
     */
    public boolean jmlvisible(Symbol base, Symbol parent, long flags) {
        Symbol gp = parent;
        while (gp instanceof ClassSymbol) {
            if (!locallyJMLVisible(base,gp,gp.flags())) return false;
            do { gp = gp.getEnclosingElement(); }
            while (gp instanceof MethodSymbol);
        }
        return locallyJMLVisible(base, parent, flags);
    }

    public boolean hasSpecPublic(Symbol s) {
        if (s instanceof ClassSymbol) {
            var tspecs = JmlSpecs.instance(context).getLoadedSpecs((ClassSymbol)s);
            return hasMod(tspecs.modifiers, Modifiers.SPEC_PUBLIC);
        }
        if (s instanceof VarSymbol) {
            var tspecs = JmlSpecs.instance(context).getLoadedSpecs((VarSymbol)s);
            return tspecs != null && hasMod(tspecs.mods, Modifiers.SPEC_PUBLIC);  // FIXME - why does this need the !=null guard
        }
        if (s instanceof MethodSymbol) {
            var tspecs = JmlSpecs.instance(context).getLoadedSpecs((MethodSymbol)s);
            return hasMod(tspecs.mods, Modifiers.SPEC_PUBLIC);
        }
        return s != null && s.attribute(JmlAttr.instance(context).modToAnnotationSymbol.get(Modifiers.SPEC_PUBLIC)) != null;
    }

    public boolean hasSpecProtected(Symbol s) {
        if (s instanceof ClassSymbol) {
            var tspecs = JmlSpecs.instance(context).getLoadedSpecs((ClassSymbol)s);
            return hasMod(tspecs.modifiers, Modifiers.SPEC_PROTECTED);
        }
        if (s instanceof VarSymbol) {
            var tspecs = JmlSpecs.instance(context).getLoadedSpecs((VarSymbol)s);
            return hasMod(tspecs.mods, Modifiers.SPEC_PROTECTED);
        }
        if (s instanceof MethodSymbol) {
            var tspecs = JmlSpecs.instance(context).getLoadedSpecs((MethodSymbol)s);
            return hasMod(tspecs.mods, Modifiers.SPEC_PROTECTED);
        }
        return s != null && s.attribute(JmlAttr.instance(context).modToAnnotationSymbol.get(Modifiers.SPEC_PROTECTED)) != null;
    }

    /** Returns true if a declaration in the 'parent' class with the given flags 
     * is jml-visible in a method in the
     * 'base' class and the method has the given 'methodFlags'. 
     * This check takes into account spec-public and spec-protected declarations
     * and also JML-specific visibility rules. The first argument can be null
     * if checking the visibility, say of a clause.
     */
    public boolean jmlvisible(/*@ nullable */ Symbol s, Symbol base, Symbol parent, long flags, long methodFlags) {
        // Make sure enclosing classes are visible
        if (jmlvisible(base,parent,flags)) return true;
        Symbol p = parent.getEnclosingElement();
        while (p instanceof MethodSymbol) p = p.getEnclosingElement();
        
        // Recheck this FIXME
        if (!(p instanceof Symbol.PackageSymbol)) {
            if (!jmlvisible(null,base,p,parent.flags(),methodFlags)) return false;
        }
        
        // In JML the clause must be at least as visible to clients as the method
        flags &= Flags.AccessFlags;
        methodFlags &= Flags.AccessFlags;
        
        // If target is public, then it is jml-visible, since everyone can see it
        if (flags == Flags.PUBLIC) return true;
        if (flags == 0 && parent.isInterface()) return true;
        if (hasSpecPublic(s)) return true;

        // Otherwise a public method sees nothing
        if (methodFlags == Flags.PUBLIC) return false;
        
        // If the method itself is private, then anyone who can see the method
        // can also see the target
        if (methodFlags == Flags.PRIVATE) return true;
        
        // By now the method is either protected or package
        // The target is either protected or package or private
        // FIXME - comment more
        if (flags == Flags.PRIVATE && !hasSpecProtected(s)) return false;
        
        if (flags == 0) return methodFlags == 0;
        // By now flags must be PROTECTED
        // and methodFlags is PROTECTED or package
        
        // Must be in the same package
        return (base.owner == parent.owner);
        // The rule is that the clause has to be visible wherever the method is visible
        // If a protected method can see a protected clause by Java rules, then either
        // the clause is in the same package OR in the same or a super class.
        // But if both the clause and method are to be visible to a client, then 
        // the clause has to be in the same package AND in the same or a super class
    }

    // Lists all fields of 'owner' that are visible from 'base' in an environment with baseVisibility, according to JML visibility rules
    public List<Symbol.VarSymbol> listJmlVisibleFields(TypeSymbol owner, TypeSymbol base, long baseVisibility, boolean forStatic, boolean includeDataGroups) {
        List<Symbol.VarSymbol> list = new LinkedList<Symbol.VarSymbol>();
        for (TypeSymbol csym: parents(owner, true)) {
            for (Symbol s: csym.members().getSymbols()) {
                if (s.kind != Kinds.Kind.VAR) continue;
                if (isJMLStatic(s) != forStatic) continue;
                if ((s.flags() & Flags.FINAL) != 0) continue;
                if (!includeDataGroups && JmlTypes.instance(context).isOnlyDatagroup(s.type)) continue;
                //System.out.println("LVF " + owner + " " + base + " " + csym + " " + s);
                if (!jmlvisible(s,base,csym,s.flags()&Flags.AccessFlags,baseVisibility)) continue; // FIXME - jml access flags? on base and on target?
                list.add((Symbol.VarSymbol)s);
            }
        }
        return list;
    }

    public List<Symbol.VarSymbol> listAllFields(TypeSymbol base, boolean forStatic) {
        List<Symbol.VarSymbol> list = new LinkedList<Symbol.VarSymbol>();
        for (TypeSymbol csym: parents(base, true)) {
            // FIX - I think we need to expand recursively
            for (Symbol s: csym.members().getSymbols()) {
                if (s.kind != Kinds.Kind.VAR) continue;
                if (!isJMLStatic(s) && forStatic) continue;
                list.add((Symbol.VarSymbol)s);
            }
        }
        return list;
    }

    /** Returns the owning class declaration of a method declaration */
    public JmlClassDecl getOwner(JmlMethodDecl methodDecl) {
        return (JmlClassDecl)JmlEnter.instance(context).getEnv((ClassSymbol)methodDecl.sym.owner).tree;
    }
        
    /** Returns a method signature with a fully-qualified method name */
    public String qualifiedMethodSig(MethodSymbol sym) {
        return classQualifiedName(sym.owner) + "." + sym;
    }

    /** Returns a method signature with a fully-qualified method name, but org.jmlspecs.annotation and java.lang and org.jmlspecs.lang removed */
    public String abbrev(String s) {
        s = s.replace("@org.jmlspecs.annotation.","@").replace("org.jmlspecs.annotation.","");
        var r = s.replaceAll("java.lang." ,"").replaceAll("org.jmlspecs.lang." ,"");
        return r;
    }

    /** Returns a method signature with a fully-qualified method name, but org.jmlspecs.annotation and java.lang and org.jmlspecs.lang removed */
    public String abbrevMethodSig(MethodSymbol sym) {
        var sig = classQualifiedName(sym.owner) + "." + sym;
        sig = sig.replace("@org.jmlspecs.annotation.","@").replace("org.jmlspecs.annotation.","");
        var r = sig.replaceAll("java.lang." ,"").replaceAll("org.jmlspecs.lang." ,"");
        return r;
    }
    
    public static String uniqueSymbolName(Symbol sym) {
        if (sym instanceof MethodSymbol ms) {
            return uniqueSymbolName(ms.owner) + "." + ms.toString();
        }
        if (sym instanceof ClassSymbol cs) {
            String owner = uniqueSymbolName(cs.owner);
            String cstr = cs.toString();
            int k = cstr.lastIndexOf('$');
            if (k == -1) cstr = cs.name.toString();
            else cstr = cstr.substring(k, cstr.length()-1);
            if (owner.isEmpty()) return cstr;
            else return owner + "." + cstr;
        }
        if (sym instanceof Symbol.PackageSymbol ps) {
            if (ps.isUnnamed()) return "";
            else return ps.toString();
        }
        // For VarSymbol and other owner types (e.g. anonymous class created in a
        // field initializer has a VarSymbol as its immediate owner): walk up to the
        // enclosing class or method so the FQN includes the correct class prefix.
        if (sym != null && sym.owner != null && sym.owner != sym) {
            return uniqueSymbolName(sym.owner);
        }
        return "";
    }

    /** Returns a fully-qualified name for a symbol, without the signature */ // FIXME - may include <init>
    public String qualifiedName(Symbol sym) {
        return classQualifiedName(sym.owner) + "." + sym.name.toString();
    }

    // FIXME - probably replace all calls to the above with the one below (and change its name) - but needs to be tested.
    
    /** Returns a fully-qualified name for a symbol, without the signature */ // FIXME - may include <init>
    public String qualifiedNameNoInit(Symbol sym) {
        return classQualifiedName(sym.owner) + "." + sym.name.toString().replace("<init>", sym.owner.getSimpleName().toString());
    }

    /** Returns a fully-qualified name for a class symbol, with adjustments for anonymous types */
    public String classQualifiedName(Symbol sym) {
        String s = sym.getQualifiedName().toString();
        if (s.isEmpty()) {
            s = sym.flatName().toString().replace('$','.');
        }
        return s;
    }

    /** Returns an unqualified name, but with the class name instead of init */
    public String methodName(MethodSymbol sym) {
        String s = sym.toString();
        int k = s.indexOf("(");
        s = k >= 0 ? s.substring(0,k) : s;
        if (s.isEmpty()) {
            // Anonymous constructor
            s = sym.owner.toString();
            if (s.startsWith("$anonymous$")) {
                s = s.substring("$anonymous$".length());
            }
        }
        return s;
    }

    /** Removes an element from a ListBuffer, if there is one, and return the new list */
    public static <T> ListBuffer<T> remove(ListBuffer<T> list, T element) {
        // Remove the duplicate if it is in newdefs
        ListBuffer<T> n = new ListBuffer<>();
        for (T ttt: list) {
            if (ttt != element) n.add(ttt);
        }
        return n;
    }
    
    /** Removes an element from a ListBuffer, if there is one, and return the new list */
    public static <T> ListBuffer<T> remove(ListBuffer<T> list, ListBuffer<T> elements) {
        // Remove the duplicate if it is in newdefs
        ListBuffer<T> n = new ListBuffer<>();
        x: for (T ttt: list) {
            for (T rem: elements) {
                if (ttt == rem) continue x;
            }
            n.add(ttt);
        }
        return n;
    }
    
    /** Removes an element from a List, if there is one, and return the new list */
    public static <T> com.sun.tools.javac.util.List<T> remove(com.sun.tools.javac.util.List<T> list, T element) {
        // Remove the duplicate if it is in newdefs
        ListBuffer<T> n = new ListBuffer<>();
        for (T ttt: list) {
            if (ttt != element) n.add(ttt);
        }
        return n.toList();
    }
    
    // FIXME - replace calls of this by the versions in treeutils -- but not sure what version that is?
    public/* @ nullable */JmlAnnotation modToAnnotationAST(ModifierKind jt,
            int position, int endpos) {

        JmlTree.Maker F = JmlTree.Maker.instance(context);
        JCExpression p = nametree(position, endpos, jt.fullAnnotation, null);
        JmlAnnotation ann;
        if (jt instanceof TypeAnnotationKind) {
            ann = F.at(position).TypeAnnotation(p,
                    com.sun.tools.javac.util.List.<JCExpression> nil());
        } else {
            ann = F.at(position).Annotation(p,
                    com.sun.tools.javac.util.List.<JCExpression> nil());
        }
        ann.sourcefile = log().currentSourceFile();
        ann.kind = jt;
        ann.annotationType.type = ann.type = jt.annotationType(context);
        // FIXME - attribute field is not set
        return ann;
    }
    
    /** Returns an AST corresponding to the qualified name of the annotation class
     *  given as fqName
     */
    public JCExpression nametree(int position, int endpos, String fqName, JmlParser parser) {
        String[] nms = fqName.split("\\.");
        JmlTree.Maker F = JmlTree.Maker.instance(context);
        Names names = Names.instance(context);
        JCExpression tree = F.at(position).Ident(nms[0]);
        if (parser != null) parser.storeEnd(tree,endpos);
        for (int i = 1; i<nms.length; i++) {
            tree = F.at(position).Select(tree, names.fromString(nms[i]));
            if (parser != null) parser.storeEnd(tree,endpos);
        }
        return tree;
    }
    
    public void removeAnnotation(JCModifiers mods, ModifierKind mk) {
        ListBuffer<JCAnnotation> newlist = new ListBuffer<>();
        mods.annotations.forEach((JCAnnotation a)->{ if (a instanceof JmlTree.JmlAnnotation && ((JmlTree.JmlAnnotation)a).kind != mk) newlist.add(a); } );
        mods.annotations = newlist.toList();
        ListBuffer<JmlToken> newtokens = new ListBuffer<>();
        ((JmlModifiers)mods).jmlmods.forEach((JmlToken t)->{ if (t.jmlclausekind != mk) newtokens.add(t); });
        ((JmlModifiers)mods).jmlmods  = newtokens.toList();
    }

    /** Instances of this class are used to abort operations that are not
     * implemented.
     * @author David R. Cok
     */
    public static class JmlNotImplementedException extends RuntimeException {
        private static final long serialVersionUID = 1L;
        @SuppressWarnings("serial")
        public DiagnosticPosition pos;
        public JmlNotImplementedException(DiagnosticPosition pos, String location) {
            super(location);
            this.pos = pos;
        }
        
        public static class Quantifier extends JmlNotImplementedException {
            private static final long serialVersionUID = 1L;
            public Quantifier(DiagnosticPosition pos, String location) {
                super(pos,location);
            }
        }
    }

    public static String nameTP(JmlClassDecl cd) {
        String s = cd.name.toString();
        if (cd.typarams == null || cd.typarams.length() == 0) return s;
        return s + "<" + join(",",cd.typarams,p->p.name) +">";
    }

    /** This is a predicate that can be used in a debugging condition */
    public static boolean print(String s) {
        if (s != null) System.out.println(s);
        return true;
    }
    
    /** This is solely used to easily insert conditional breakpoints for debugging. */
    public static void stop() {
        return;
    }
    
    /** Returns true if the JDK -deprecation option is set */
    public boolean isDeprecationSet() {
        return Options.instance(context).isSet("-Xlint:deprecation");
    }
    
    public static boolean isStatic(long flags) {
        return (flags & Flags.STATIC) != 0;
    }
    
    public static boolean isFinal(long flags) {
        return (flags & Flags.FINAL) != 0;
    }
    
    public static class DoubleMap<T1,T2,TR> {
        Map<T1, Map<T2,TR>> map = new HashMap<T1, Map<T2,TR>>();
        
        public TR get(T1 t1, T2 t2) {
            Map<T2,TR> m = map.get(t1);
            if (m == null) return null;
            return m.get(t2);
        }
        
        public void put(T1 t1, T2 t2, TR tr) {
            Map<T2,TR> m = map.get(t1);
            if (m == null) {
                m = new HashMap<T2,TR>();
                map.put(t1, m);
            }
            m.put(t2, tr);
        }
        
        public void clear() {
            map.clear();
        }
    }
    
    @SuppressWarnings("unchecked")
    public static <T> java.util.Collection<T> asSet(T ... args) {
        return java.util.Arrays.asList(args);
    }
    
    /** Reports progress to the registered IProgressListener; also checks if
     * the progress listener has received a user-cancellation, in which case
     * this method throws an exception to terminate processing
     * @param ticks amount of work to report
     * @param level level of the message (lower levels are more likely to be printed)
     * @param message the progress message
     */
    public void progress(int ticks, int level, String message) {
        org.openjml.IAPI.IProgressListener pr = org.jmlspecs.openjml.Main.instance(context).progressListener;
        boolean cancelled = pr.report(level,message);
        if (pr != null && ticks != 0) pr.worked(ticks);
        if (cancelled) {
            throw new PropagatedException(new Main.JmlCanceledException("ESC operation cancelled"));
        }
    }
    
    /**
     * Checks to see if two JavaFileObjects point to the same location.
     * In some cases, it's a bad idea to use JavaFileObject.equals, because copying a JavaFileObject can change the path name, even if they point to the same canonical path.
     * This function exists for where JavaFileObject.equals may fail.
     */
    public static boolean ifFilepathsEqual(JavaFileObject jfo1, JavaFileObject jfo2) {
        try {
            File file1 = new File(jfo1.getName());
            File file2 = new File(jfo2.getName());
            return file1.getCanonicalPath().equals(file2.getCanonicalPath());
        } catch (IOException e) {}
        return jfo1.equals(jfo2);
    }

    /** Issue a verification failure message, via the Log */
    public void verify(JavaFileObject source, int pos, String key, Object ... args) {
        Log log = log();
        JavaFileObject prev = null;
        if (source != null) prev = log.useSource(source);
        try {
            verify(pos, key, args);
        } finally {
            if (prev != null) log.useSource(prev);
        }
    }
    
    /** Issue a log warning message */
    public void warning(JavaFileObject source, int pos, String key, Object ... args) {
        Log log = log();
        JavaFileObject prev = null;
        if (source != null) prev = log.useSource(source);
        try {
            warning(pos, key, args);
        } finally {
            if (prev != null) log.useSource(prev);
        }
    }
    
    /** Issue a log warning message */
    public void warning(JavaFileObject source, DiagnosticPosition pos, String key, Object ... args) {
        Log log = log();
        JavaFileObject prev = null;
        if (source != null) prev = log.useSource(source);
        try {
            warning(pos, key, args);
        } finally {
            if (prev != null) log.useSource(prev);
        }
    }
    
    public void warningAndAssociatedDeclaration(JavaFileObject source, DiagnosticPosition pos, JavaFileObject assoc, DiagnosticPosition assocpos, String key, Object ... args) {
        Log log = log();
        JavaFileObject prev = log.useSource(source);
        try {
            warning(pos, key, args);
        } finally {
            log.useSource(prev);
        }
        prev = log.useSource(assoc);
        try {
            warning(assocpos, "jml.associated.decl.cf", locationString(pos, source));
        } finally {
            log.useSource(prev);
        }
    }
    
    public void warningAndAssociatedDeclaration(JavaFileObject source, int pos, JavaFileObject assoc, int assocpos, String key, Object ... args) {
        Log log = log();
        JavaFileObject prev = log.useSource(source);
        try {
            warning(pos, key, args);
        } finally {
            log.useSource(prev);
        }
        prev = log.useSource(assoc);
        try {
            warning(assocpos, "jml.associated.decl.cf", locationString(pos, source));
        } finally {
            log.useSource(prev);
        }
    }
    
    public void error(JavaFileObject source, int pos, String key, Object ... args) {
        Log log = log();
        JavaFileObject prev = null;
        if (source != null) prev = log.useSource(source);
        try {
            log.error(pos, key, args);
        } finally {
            if (prev != null) log.useSource(prev);
        }
    }
    
    public void error(JavaFileObject source, DiagnosticPosition pos, String key, Object ... args) {
        Log log = log();
        JavaFileObject prev = null;
        if (source != null) prev = log.useSource(source);
        try {
            error(pos, key, args);
        } finally {
            if (prev != null) log.useSource(prev);
        }
    }
    
    public void errorAndAssociatedDeclaration(JavaFileObject source, int pos, JavaFileObject assoc, int assocpos, String key, Object ... args) {
        Log log = log();
        JavaFileObject prev = log.useSource(source);
        try {
            error(pos, key, args);
        } finally {
            log.useSource(prev);
        }
        prev = log.useSource(assoc);
        try {
            error(assocpos, "jml.associated.decl.cf", locationString(pos, source));
        } finally {
            log.useSource(prev);
        }
    }
    
    public void errorAndAssociatedDeclaration(JavaFileObject source, DiagnosticPosition pos, JavaFileObject assoc, DiagnosticPosition assocpos, String key, Object ... args) {
        Log log = log();
        JavaFileObject prev = log.useSource(source);
        try {
            error(pos, key, args);
        } finally {
            log.useSource(prev);
        }
        prev = log.useSource(assoc);
        try {
            error(assocpos, "jml.associated.decl.cf", locationString(pos, source));
        } finally {
            log.useSource(prev);
        }
    }
    
    /** Return null if the method is to be checked, a reason string if it is to be skipped.
     */
    public String filter(JCMethodDecl methodDecl) {
        String fullyQualifiedName = this.qualifiedName(methodDecl.sym);
        String simpleName = methodDecl.name.toString();
        if (methodDecl.sym.isConstructor()) {
            String constructorName = methodDecl.sym.owner.name.toString();
            fullyQualifiedName = fullyQualifiedName.replace("<init>", constructorName);
            simpleName = simpleName.replace("<init>", constructorName);
        }
        String fullyQualifiedSig = uniqueSymbolName(methodDecl.sym);

        String excludes = JmlOption.EXCLUDE.value(context);
        if (excludes != null && !excludes.isEmpty()) {
            String[] splits = excludes.contains("(") || excludes.contains(";") ? excludes.split(";") : excludes.split(",");
            for (String exclude: splits) { //$NON-NLS-1$
                if (exclude.equals("<init>") && methodDecl.sym.isConstructor()) {
                    return ("Skipping " + fullyQualifiedName + " because it matches the exclusion " + exclude); //$NON-NLS-1$ //$NON-NLS-2$
                }
                if (fullyQualifiedName.equals(exclude) ||
                        fullyQualifiedSig.equals(exclude) ||
                        simpleName.equals(exclude)) {
                    return ("Skipping " + fullyQualifiedName + " because it matches the exclusion " + exclude); //$NON-NLS-1$ //$NON-NLS-2$
                }
                try {
                    if (Pattern.matches(exclude,fullyQualifiedName)) {
                        return ("Skipping " + fullyQualifiedName + " because it matches the exclusion pattern " + exclude); //$NON-NLS-1$ //$NON-NLS-2$
                    }
                } catch(PatternSyntaxException e) {
                    // The methodToDo can be a regular string and does not
                    // need to be legal Pattern expression
                    // skip
                }
            }
        }

        String methodsToDo = JmlOption.METHOD.value(context);
        if (methodsToDo != null && !methodsToDo.isEmpty()) {
            match: {
                if (fullyQualifiedSig.equals(methodsToDo)) break match; // A hack to allow at least one signature-containing item in the methods list
                String[] splits = methodsToDo.contains("(") || methodsToDo.contains(";") ? methodsToDo.split(";") : methodsToDo.split(",");
                for (String methodToDo: splits) { //$NON-NLS-1$ 
                    methodToDo = methodToDo.trim();
                    if (methodToDo.isEmpty()) continue;
                    // Match if methodToDo
                    //    is the full FQN
                    //    is just the name of the method
                    //    contains a "." character before a "(" and is the same as the FQ signature
                    //    does not contain a "." character before a "(" and is the tail of the FQ signature
                    if (fullyQualifiedName.equals(methodToDo) ||
                            methodToDo.equals(simpleName) ||
                            ( methodToDo.contains(".") && methodToDo.contains("(") && methodToDo.indexOf(".") > methodToDo.indexOf("(") ? fullyQualifiedSig.equals(methodToDo) : fullyQualifiedSig.endsWith(methodToDo))) {
                        break match;
                    }
                    try {
                        // Also check whether methodToDo, interpreted as a regular expression
                        // matches either the signature or the name
                        if (Pattern.matches(methodToDo,fullyQualifiedSig)) break match;
                        if (Pattern.matches(methodToDo,fullyQualifiedName)) break match;
                    } catch(PatternSyntaxException e) {
                        // The methodToDo can be a regular string and does not
                        // need to be legal Pattern expression
                        // skip
                        int x = 0;
                    }
                }
                return ("Skipping " + fullyQualifiedName + " because it does not match " + methodsToDo);  //$NON-NLS-1$//$NON-NLS-2$
            }
        }
        
        return null;
    }
    
    // The following are wrappers for calls to log, to output errors, warnings and notes through a 
    // common mechanism. The wrappers are handy because Log itself does not expose all the 
    // needed combinations of arguments. Note that you can use 
    // - null for an absent DiagnosticFlag
    // - DiagnosticSource.NO_SOURCE for an absent DiagnosticSource, but the default DIagnosticSource is the current log.currentSource()
    // - Position.NOPOS for an absent int position
    // - null for an absent DiagnosticPosition position
    
    // Used in reporting parser syntax errors
    public JCDiagnostic.Error errorKey(String key, Object ... args) {
        return JCDiagnostic.Factory.instance(context).errorKey(key, args);
    }

//    public JCDiagnostic.Warning warningKey(String key, Object ... args) {
//        return JCDiagnostic.Factory.instance(context).warningKey(key, args);
//    }
//
//    public JCDiagnostic.Note noteKey(String key, Object ... args) {
//        return JCDiagnostic.Factory.instance(context).noteKey(key, args);
//    }
    
    public JCDiagnostic errorDiag(DiagnosticSource sp, DiagnosticPosition pos, String key, Object ...args) {
        return JCDiagnostic.Factory.instance(context).create(JCDiagnostic.DiagnosticType.ERROR, sp, pos, key, args);
    }
//    
//    public JCDiagnostic warningDiag(DiagnosticSource sp, DiagnosticPosition pos, String key, Object ...args) {
//        // FIXME - needs a spot for a WarningCategory
//        return JCDiagnostic.Factory.instance(context).create(JCDiagnostic.DiagnosticType.WARNING, sp, pos, key, args);
//    }
//    
//    public JCDiagnostic noteDiag(DiagnosticSource sp, DiagnosticPosition pos, String key, Object ...args) {
//        return JCDiagnostic.Factory.instance(context).create(JCDiagnostic.DiagnosticType.NOTE, sp, pos, key, args);
//    }
    
    public void error(String key, Object ... args) {
        log().error(JCDiagnostic.Factory.instance(context).errorKey(key, args));
    }

    public void error(int pos, String key, Object ... args) {
        log().error(pos, JCDiagnostic.Factory.instance(context).errorKey(key, args));
    }

    public void error(int begin, int end, String key, Object... args) {
        this.error(
                new DiagnosticPositionSE(begin, end), // end is exclusive (one past last char)
                key, args);// TODO - not unicode friendly
    }

    public void error(int begin, int preferred, int end, String key, Object... args) {
        this.error(
                new DiagnosticPositionSE(begin, preferred, end), // end is exclusive (one past last char)
                key, args);// TODO - not unicode friendly
    }
    
    public void error(DiagnosticPosition pos, String key, Object ... args) {
        log().error(null, pos, JCDiagnostic.Factory.instance(context).errorKey(key, args));
    }

    public void error(DiagnosticFlag flag, DiagnosticPosition pos, String key, Object ... args) {
        log().error(flag, pos, JCDiagnostic.Factory.instance(context).errorKey(key, args));
    }

    public void error(DiagnosticFlag flag, int pos, String key, Object ... args) {
        log().error(flag, pos, JCDiagnostic.Factory.instance(context).errorKey(key, args));
    }

    public void warning(String key, Object ... args) {
        warning(WarningCategory.NULL, (JavaFileObject)null, null, key, args);
    }

    public void warning(int pos, String key, Object ... args) {
        warning(WarningCategory.NULL, (JavaFileObject)null, new DiagnosticPositionSE(pos,pos), key, args);
    }

    public void warning(int pos, int endPos, String key, Object ... args) {
        warning(WarningCategory.NULL, (JavaFileObject)null, new DiagnosticPositionSE(pos, endPos), key, args);
    }

    public void warning(DiagnosticPosition pos, String key, Object ... args) {
        warning(WarningCategory.NULL, (JavaFileObject)null, pos, key, args);
    }

    /** Warning messages with no source location */
    public void warning(WarningCategory.Key category, String key, Object ... args) {
        warning(category, (JavaFileObject)null, null, key, args);
    }
    
    public void warning(WarningCategory.Key category, JavaFileObject source, int pos, JavaFileObject asource, int apos, String key, String... args) {
        warning(category, source, new DiagnosticPositionSE(pos, pos), asource, new DiagnosticPositionSE(apos, apos), args[0]); // FIXME
    }


    public void warning(WarningCategory.Key category, JavaFileObject source, DiagnosticPosition pos, JavaFileObject asource, DiagnosticPosition apos, String message) {
        var wt = WarningCategory.instance(context).action(category);
        if (wt == WarningCategory.WarnAction.QUIET) return;
        Log log = log();
        switch (wt) {
        case WARN: {
            JavaFileObject prev = log.useSource(source);
            try {
                log.warning(pos, JCDiagnostic.Factory.instance(context).warningKey("jml.message", "[" + category + "] " + message));
            } finally {
                log.useSource(prev);
            }
            prev = log.useSource(asource);
            try {
                log.warning(apos, JCDiagnostic.Factory.instance(context).warningKey("jml.associated.decl.cf", locationString(pos, source)));
            } finally {
                log.useSource(prev);
            }
            break;
        }
        case ERROR: {
            JavaFileObject prev = log.useSource(source);
            try {
                log.error(pos, JCDiagnostic.Factory.instance(context).errorKey("jml.message", "[" + category + "] " + message));
            } finally {
                log.useSource(prev);
            }
            prev = log.useSource(asource);
            try {
                log.error(apos, JCDiagnostic.Factory.instance(context).errorKey("jml.associated.decl.cf", locationString(pos, source)));
            } finally {
                log.useSource(prev);
            }
            break;
        }
        }
    }

    public void warning(WarningCategory.Key category, JavaFileObject source, int begin, int end, String key, Object ... args) {
        this.warning(category, source,
                new DiagnosticPositionSE(begin, end), // end is exclusive (one past last char)
                key, args);
    }
    
    public void warning(WarningCategory.Key category, JavaFileObject source, DiagnosticPosition pos, String key, Object ... args) {
        // All this mucking about with the diagnostic message is to insert the category string into the message
        // without having to alter every message key and warning call throughout openjml
        var wt = WarningCategory.instance(context).action(category);
        if (wt == WarningCategory.WarnAction.QUIET) return;
        var dg = com.sun.tools.javac.util.JCDiagnostic.Factory.instance(context).warning(null, null, null, key, args);
        var message = dg.toString().substring("warning: ".length());
        if (category != null) message = "[" + category + "] " +  message;
        JavaFileObject prev = null;
        if (source != null) prev = log.useSource(source);
        try {
            switch (wt) {
            case WARN:
                log().warning(null, pos, JCDiagnostic.Factory.instance(context).warningKey("jml.raw", message));
                break;
            case ERROR:
                log().error(null, pos, JCDiagnostic.Factory.instance(context).errorKey("jml.raw", message));
                break;
            }
        } finally {
            if (prev != null) log.useSource(prev);
        }
    }
    
    public void warning(WarningCategory.Key category, JavaFileObject source, int pos, String key, Object ... args) {
        this.warning(category, source,
                new DiagnosticPositionSE(pos, pos), // FIXME or is end pos+1?
                key, args);
    }
        
    public int verifyWarnings = 0;

    com.sun.tools.javac.util.BasicDiagnosticFormatter verifyDiagnosticFormatter = null;
    public void verify(DiagnosticPosition pos, String key, Object ... args) {
        // useVerify is the normal behavior
        // turn it off to have the legacy test behavior where a verify warning was a regular warning
        // FIXME: Keep the no verify alternative until the tests are all fixed
        boolean useVerify = !"-1".equals(JmlOption.EXITVERIFY.value(context));
        if (jmlverbose > QUIET) {
            if (useVerify) {
                var df = log().getDiagnosticFormatter();
                if (verifyDiagnosticFormatter == null) {
                    verifyDiagnosticFormatter = new com.sun.tools.javac.util.BasicDiagnosticFormatter(Options.instance(context),JavacMessages.instance(context)) {
                        public String formatKind(JCDiagnostic d, Locale l) {
                            return "verify: ";
                        }
                    };
                }
                // FIXME - need some explanation -- there seems to be two formatters, one in Log and one in JCDiagnostic.Factory -- which one matters when?
                log().setDiagnosticFormatter(verifyDiagnosticFormatter);
                var df2 = JCDiagnostic.Factory.instance(context).setFormatter(verifyDiagnosticFormatter);
                log().mandatoryWarning(pos, JCDiagnostic.Factory.instance(context).warningKey(key, args));
                log().setDiagnosticFormatter(df);
                JCDiagnostic.Factory.instance(context).setFormatter(df2);
            } else {
                log().mandatoryWarning(pos, JCDiagnostic.Factory.instance(context).warningKey(key, args));
            }
        }
        if (useVerify) {
            verifyWarnings++;
            log().nwarnings--;
        }
    }
    
    public void verify(int pos, String key, Object ... args) {
        verify(pos==Position.NOPOS?null:new SimpleDiagnosticPosition(pos), key, args);
    }

    public void verify(String key, Object ... args) {
        verify((DiagnosticPosition)null, key, args);
    }

    public void note(boolean verboseOnly, String msg) {
        if (!verboseOnly || Utils.instance(context).jmlverbose >= Utils.JMLVERBOSE) {
            log().getWriter(WriterKind.NOTICE).println(msg);
        }
    }

    public void note(String msg) {
        note(null, "jml.message", msg);
    }

    public void note(DiagnosticPosition pos, String key, Object ... args) {
        log().note(pos, JCDiagnostic.Factory.instance(context).noteKey(key, args));
    }

    public void note(int pos, String key, Object... args) {
        log.note(pos==Position.NOPOS?null:new SimpleDiagnosticPosition(pos), new JCDiagnostic.Note("compiler", key, args));
    }

    public void note(JavaFileObject source, DiagnosticPosition pos, String key, Object ... args) {
        JavaFileObject prev = source == null ? null : log().useSource(source);
        try {
            note(pos, key, args);
        } finally {
            if (prev != null) log().useSource(prev);
        }
    }
    
    public void noPrefix(String msg) {
        log().getWriter(WriterKind.STDOUT).println(msg);
    }

    /** A derived class of DiagnosticPosition that allows for straightforward setting of the
     * various positions associated with an error message.
     */
    // FIXME - comment on relationship to unicode characters
    static public class DiagnosticPositionSE implements DiagnosticPosition {
        protected int begin;
        protected int preferred;
        protected int end; // Exclusive end: one character BEYOND the last character of the range
        
        public DiagnosticPositionSE(int begin, int end) {
            this.begin = begin;
            this.preferred = begin;
            this.end = end;
        }
        
        public DiagnosticPositionSE(int begin, int preferred, int end) {
            this.begin = begin;
            this.preferred = preferred;
            this.end = end;
        }
        
        @Override
        public JCTree getTree() {
            return null;
        }

        @Override
        public int getStartPosition() {
            return begin;
        }

        @Override
        public int getPreferredPosition() {
            return preferred;
        }

        @Override
        public int getEndPosition(EndPosTable endPosTable) {
            return end;// FIXME
        }
        
    }
    
    public void unexpectedException(Throwable e, String msg) {
        error("jml.internal","Unexpected exception: " + msg + " " + e);
        e.printStackTrace(System.out);
    }

    /** This method checks that a condition that is expected to always be tree is actually true.
     * That is, if the condition is false, some internal bug has occurred.
     * This method is used in place of ojassert if the bug is something that can be worked around.
     *      * If the condition is false, an error message is emitted.
     * Returns the value of the argument.
     */
    public boolean ojcheck(boolean condition, String message) {
        if (!condition) {
            // In a bug-free program, this branch will never happen
            Log.instance(context).error("jml.internal", message != null ? message : "internal bug caught by ojcheck");
        }
        return condition;
    }
    
    /** This method checks that a condition that is expected to always be tree is actually true.
     * That is, if the condition is false, some internal bug has occurred.
     * This method is used (instead of ojcheck) if there is no reasonable recovery.
     * If the condition is false, an error message is emitted and a JmlInternalException exception is thrown.
     */
    public void ojassert(boolean condition, String message) {
        if (!condition) {
            // In a bug-free program, this branch will never happen
            Log.instance(context).error("jml.internal", message != null ? message : "internal bug caught by ojassert");
            throw new JmlInternalException(message);
        }
    }
    
    static boolean verbose = System.getenv("VERBOSE") != null;
    public boolean verbose() {
        return jmlverbose >= Utils.JMLVERBOSE || verbose;
    }

    /** True if verbosity is at least PROGRESS */
    public boolean progress() {
        return jmlverbose >= Utils.PROGRESS;
    }

    public static void dumpStack() {
        new RuntimeException().printStackTrace(System.out); // Thread.dumpStack() goes to Stderr
    }
    
    public static void dumpStack(String message) {
        System.out.println("DUMP " + message);
        dumpStack();
    }

    public static void conditionalPrintStack(String heading, Throwable e) {
        if (System.getenv("STACK") != null) {
            System.out.println(heading);
            e.printStackTrace(System.out);
        }
    }

//    // FIXME - move this
//    /** This just tests whether the type is explicitly a datagroup */
//    public boolean isOnlyDatagroup(Type type) {
//        return type == JmlPrimitiveTypes.datagroupTypeKind.getType(context);
//    }
}
