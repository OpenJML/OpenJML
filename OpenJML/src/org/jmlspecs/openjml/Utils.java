/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;
import org.jmlspecs.openjml.JmlTree.IInJML;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.PropagatedException;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.JCDiagnostic.SimpleDiagnosticPosition;

/** This class holds a number of utility methods.  They could often be
 * static, but we make this a registerable tool, so that it can be 
 * overridden by some enterprising future person.
 */
public class Utils {
    
    /** This field is used to restrict output during testing so as to 
     * make test results more deterministic (or to match old test results).
     */
    static public boolean testingMode = false;
    
    ///////////////////////////////////////////////////////////////////////////////////////

    /** The context applicable for this instance of the Utils class. */
    protected Context context;
    
    /** The Log object - do not use this directly - use log() instead */
    private Log log;

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
        this.context = context;
        context.put(utilsKey, this);
    }

    /** The error and warning log. It is crucial that the log be obtained
     * lazily, and not before options are read; otherwise the Log object
     * is not properly intialized from the Java options. */
    public final Log log() {
        if (log == null) log = Log.instance(context);
        return log;
    }

    /** Global utility value that enables printing of debugging or trace information. */
    public int jmlverbose = 0; 
    static public final int QUIET = 0;
    static public final int NORMAL = 1;
    static public final int PROGRESS = 2;
    static public final int JMLVERBOSE = 3;
    static public final int JMLDEBUG = 4;

    /** Do ESC - set by Main.setupOptions */
    public boolean esc = false;

    /** Do RAC - set by Main.setupOptions */
    public boolean rac = false;

    /** Do JML check only - set by Main.setupOptions */
    public boolean check = false;

    /** Do Java compilation - set by Main.setupOptions */
    public boolean compile = false;

    /** Do Jmldoc  */
    public boolean doc = false;
    
    /** Max number of ESC warnings per method (set from an option) */
    public int maxWarnings = 1;

    /** The set of keys that control the use of optional comments, set from options */
    public Set<String> commentKeys = new HashSet<String>();

    /** A bit that indicates that a declaration was declared within a JML annotation (so that it should not be visible to Java) */
    final public static long JMLBIT = 1L << 50; // Any bit that does not conflict with bits in com.sun.tools.javac.code.Flags.

    /** A bit that indicates that a declaration was declared somewhere within a JML annotation, but not nested within a class or method body that is also in the JML annotation */
    final public static long JMLBITTOP = 1L << 53; // Any bit that does not conflict with bits in com.sun.tools.javac.code.Flags.

    /** A bit that indicates that JML instrumentation has been added .... FIXME */
    final public static long JMLINSTRUMENTED = 1L << 51; // Any bit that does not conflict with bits in com.sun.tools.javac.code.Flags.

    /** A bit that indicates that a variable is local to an expression */
    final public static long JMLEXPRLOCAL = 1L << 52; // Any bit that does not conflict with bits in com.sun.tools.javac.code.Flags.


    /** Tests whether the JML flag is set in the given modifiers object
     * @param mods the instance of JCModifiers to test
     * @return true if JML is set
     */
    public boolean isJML(/*@ nullable */ JCModifiers mods) {
        return mods != null && (mods.flags & JMLBIT) != 0;
    }
    
    public boolean isJMLTop(/*@ nullable */ JCModifiers mods) {
        return mods != null && (mods.flags & JMLBITTOP) != 0;
    }
    
    /** Tests whether the given tree was directly parsed as part of JML annotation;
     * nested declarations that are not themselves directly in a JML comment will return false, 
     * even if they are nested in a class that itself is directly in a JML comment.
     */
    public boolean isJML(JCTree t) {
        return (t instanceof IInJML) && ((IInJML)t).isJML();
    }

//    public boolean isJMLTop(JCTree t) {
//        return (t instanceof IInJML) && ((IInJML)t).isJMLTop();
//    }

    /** Tests whether the JML flag is set in the given bit-vector
     * @param flags the bit-array to test
     * @return true if JML is set
     */
    public boolean isJML(long flags) {
        return (flags & JMLBIT) != 0;
    }

    public boolean isJMLTop(long flags) {
        return (flags & JMLBITTOP) != 0;
    }

    /** Sets the JML flag in the given modifiers.
     * 
     * @param mods The modifiers in which to set the JML flag
     */
    public void setJML(/*@ non_null */ JCModifiers mods) {
        mods.flags |= JMLBIT;
    }

    public void setJMLTop(/*@ non_null */ JCModifiers mods) {
        mods.flags |= JMLBITTOP;
    }

    /** Unsets the JML flag in the given modifiers.
     * 
     * @param mods The modifiers in which to set the JML flag
     */
    public void unsetJML(/*@ non_null */ JCModifiers mods) {
        mods.flags &= ~JMLBIT;
    }

    // FIXME - document
    public boolean isInstrumented(long flags) {
        return (flags & JMLINSTRUMENTED) != 0;
    }

    // FIXME - document
    public void setInstrumented(/*@ non_null */JCModifiers mods) {
        mods.flags |= JMLINSTRUMENTED;
    }

    // IS this flag used for anything?  FIXME
    /** Returns true if the modifiers is marked as local to a JML expression */
    public boolean isExprLocal(/*@ non_null */ JCModifiers mods) {
        return (mods.flags & JMLEXPRLOCAL) != 0;
    }

    /** Returns true if the modifiers is marked as local to a JML expression */
    public boolean isExprLocal(long flags) {
        return (flags & JMLEXPRLOCAL) != 0;
    }

    /** Sets the modifiers as local to a JML expression */
    public void setExprLocal(/*@ non_null */ JCModifiers mods) {
        mods.flags |= JMLEXPRLOCAL;
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

    /** A cache for the symbol */
    private ClassSymbol helperAnnotationSymbol = null;

    /** Returns true if the given symbol has a helper annotation
     * 
     * @param symbol the symbol to check
     * @return true if there is a helper annotation
     */
    public boolean isHelper(@NonNull Symbol symbol) {
        if (helperAnnotationSymbol == null) {
            helperAnnotationSymbol = createClassSymbol(Strings.helperAnnotation);
        }
        return symbol.attribute(helperAnnotationSymbol)!=null;
    }

    /** Returns true if the given symbol is marked static or is a member of a JML interface
     * that is not marked as 'instance'
     */
    public boolean isJMLStatic(Symbol sym) {
        // non-static Simple identifier is OK
        // If the owner of the field is an interface, it
        // is by default static. However, it might be a
        // JML field marked as instance.
        if (!sym.isStatic()) return false;
        if (isJML(sym.flags())) {
            Symbol csym = sym.owner;
            if ((csym.flags() & Flags.INTERFACE) != 0) {
                // TODO - should cleanup this reference to JmlAttr from Utils
                if (JmlAttr.instance(context).hasAnnotation(sym,JmlTokenKind.INSTANCE)) return false;
            } 
        }
        return true;
    }

    public boolean isJMLStatic(JCModifiers mods, ClassSymbol csym) {
        // non-static Simple identifier is OK
        // If the owner of the field is an interface, it
        // is by default static. However, it might be a
        // JML field marked as instance.
        if ((csym.flags() & Flags.INTERFACE) != 0) {
            // TODO - should cleanup this reference to JmlAttr from Utils
            if (JmlAttr.instance(context).findMod(mods,JmlTokenKind.INSTANCE) != null) return false;
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
        for (JCTree.JCAnnotation a: mods.annotations) {
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

    public JmlTree.JmlAnnotation findMod(/*@ nullable */ JCModifiers mods, /*@ non_null */JmlTokenKind ta) {
        if (mods == null) return null;
        return findMod(mods,JmlAttr.instance(context).tokenToAnnotationSymbol.get(ta));
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
    
//    public boolean hasAnnotation(Symbol sym, JmlTokenKind token) {
//        for (com.sun.tools.javac.code.Attribute.Compound c: sym.getDeclarationAttributes()) {
//            String s = c.toString();
//            String ss = token.annotationType.toString();
//            if (s.equals(ss)) return true;
//        }
//        return false;
//    }
    
    /** Finds a member of a class with a given name; note that this works for methods only
     * if the method is uniquely named.
     */
    public Symbol findMember(TypeSymbol sym, String name) {
        Name n = Names.instance(context).fromString(name);
        for (Symbol s: sym.getEnclosedElements()) {
            if (s.name.equals(n)) return s;
        }
        return null;
    }

    /** Returns true if the given String ends with a valid JML suffix, including the
     * period; there are no further checks that the argument is a sensible filename.
     * @param filename the String to check
     * @return true if the input ends in a valid JML suffix
     */
    public boolean hasValidSuffix(String filename) {
        for (String s : Strings.suffixes) {
            if (filename.endsWith(s)) return true;
        }
        return false;
    }

    public boolean hasJavaSuffix(String filename) {
        return (filename.endsWith(".java"));
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
        if (rac) log().warning(pos,"jml.not.implemented.rac",feature);
        else if (esc) log().warning(pos,"jml.not.implemented.esc",feature);
    }
    
    /** Finds OpenJML properties files in pre-defined places, reading their
     * contents and loading them into the System property set.
     */
    public static Properties findProperties(Context context) {

        //      boolean verbose = Utils.instance(context).jmldebug ||
        //          JmlOption.isOption(context,JmlOption.JMLVERBOSE) ||
        //          Options.instance(context).get("-verbose") != null;

        boolean verbose = context != null && Utils.instance(context).jmlverbose >= Utils.JMLVERBOSE;
        Properties properties = System.getProperties();
        PrintWriter noticeWriter = Log.instance(context).getWriter(WriterKind.NOTICE);
        // Load properties files found in these locations:
        // These are read in inverse order of priority, so that later reads
        // overwrite the earlier ones.
        
        // On the system classpath
        {
            URL url2 = ClassLoader.getSystemResource(Strings.propertiesFileName);
            if (url2 != null) {
                String s = url2.getFile();
                try {
                    boolean found = readProps(properties,s);
                    if (verbose) {
                        if (found) noticeWriter.println("Properties read from system classpath: " + s);
                        else noticeWriter.println("No properties found on system classpath: " + s);
                    }
                } catch (java.io.IOException e) {
                    noticeWriter.println("Failed to read property file " + s); // FIXME - review
                }
            }
        }

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
            } catch (java.io.IOException e) {
                noticeWriter.println("Failed to read property file " + s); // FIXME - review
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
            } catch (java.io.IOException e) {
                noticeWriter.println("Failed to read property file " + s); // FIXME - review
            }
        }

        // FIXME - add on the application classpath


        // check if -properties or -properties-default option is set.
        {
            String properties_file = JmlOption.value(context,JmlOption.PROPERTIES_DEFAULT);            
           
            if (properties_file != null) {
                try {
                    boolean found = readProps(properties,properties_file);
                    if (verbose) {
                        if (found) noticeWriter.println("Properties read from file: " + properties_file);
                        else noticeWriter.println("No properties file option found: " + properties_file);
                    }
                } catch (java.io.IOException e) {
                    noticeWriter.println("Failed to read property file " + properties_file); // FIXME - review
                }
            } else {
                if (verbose) noticeWriter.println("No properties file option is set");
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

    /** Reads properties from the given file into the given Properties object.
     * @param properties the object to add properties to
     * @param filename the file to read properties from
     * @return true if the file was found and read successfully
     */
    public static boolean readProps(Properties properties, String filename) throws java.io.IOException {
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

    // Includes self
    public java.util.List<ClassSymbol> parents(TypeSymbol ct, boolean includeEnclosingClasses) {
        ArrayList<ClassSymbol> interfaces = new ArrayList<ClassSymbol>(20);
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
            if (cc.owner instanceof ClassSymbol) todo.add((ClassSymbol)cc.owner); // FIXME - can this be an interface?
            todo.add((ClassSymbol)cc.getSuperclass().tsym);
            classes.add(0,cc);
        }
        for (ClassSymbol ccc: classes) {
            List<Type> ifs = ccc.getInterfaces();
            for (Type ifc : ifs) {
                ClassSymbol sym = (ClassSymbol)ifc.tsym;
                if (interfaceSet.add(sym)) interfaces.add(sym);
            }
        }
        // FIXME - the interfaces are not in a good order
        int i = 0;
        while (i < interfaces.size()) {
            ClassSymbol ccc = interfaces.get(i++);
            List<Type> ifs = ccc.getInterfaces();
            for (Type ifc : ifs) {
                ClassSymbol sym = (ClassSymbol)ifc.tsym;
                if (interfaceSet.add(sym)) interfaces.add(sym);
            }
        }
        interfaces.addAll(classes);
        return interfaces;
    }

    // Includes self // FIXME - review for order
    public java.util.List<MethodSymbol> parents(MethodSymbol m) {
        List<MethodSymbol> methods = new LinkedList<MethodSymbol>();
        for (ClassSymbol c: parents((ClassSymbol)m.owner, false)) {
            for (Symbol mem: c.getEnclosedElements()) {
                if (mem instanceof MethodSymbol &&
                        mem.name.equals(m.name) &&
                        (mem ==m || m.overrides(mem, c, Types.instance(context), true))) {
                    methods.add((MethodSymbol)mem);
                }
            }
        }
        return methods;
    }
    
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
    
    /** Creates the location prefix including the colon without any message;
     * 'pos' is the position in the file given by source or if source is null, by log.currentSource(). */
    public String locationString(DiagnosticPosition pos, /*@ nullable */ JavaFileObject source) {
        // USE JCDiagnostic.NO_SOURCE ? FIXME
        JavaFileObject prev = null;
        if (source != null) prev = log().useSource(source);
        try {
            JCDiagnostic diag = JCDiagnostic.Factory.instance(context).note(log().currentSource(), pos, "empty", "");
            String msg = diag.noSource().replace("Note: ", "");
            return msg;
        } finally {
            if (source != null) log().useSource(prev);
        }
    }
    
    Symbol codeBigintMath = null;
    Symbol codeSafeMath = null;
    Symbol codeJavaMath = null;
    Symbol specBigintMath = null;
    Symbol specJavaMath = null;
    Symbol specSafeMath = null;
    
    private void initModeSymbols() {
        if (codeBigintMath != null) return;
        specSafeMath = ClassReader.instance(context).enterClass(Names.instance(context).fromString(Strings.jmlAnnotationPackage + ".SpecSafeMath"));
        specJavaMath = ClassReader.instance(context).enterClass(Names.instance(context).fromString(Strings.jmlAnnotationPackage + ".SpecJavaMath"));
        specBigintMath = ClassReader.instance(context).enterClass(Names.instance(context).fromString(Strings.jmlAnnotationPackage + ".SpecBigintMath"));
        codeSafeMath = ClassReader.instance(context).enterClass(Names.instance(context).fromString(Strings.jmlAnnotationPackage + ".CodeSafeMath"));
        codeJavaMath = ClassReader.instance(context).enterClass(Names.instance(context).fromString(Strings.jmlAnnotationPackage + ".CodeJavaMath"));
        codeBigintMath = ClassReader.instance(context).enterClass(Names.instance(context).fromString(Strings.jmlAnnotationPackage + ".CodeBigintMath"));
    }
    
    public boolean isTypeChecked(ClassSymbol sym) {
        ClassSymbol c = sym;
        if (c == null) return false;
        return ((c.flags_field & UNATTRIBUTED) == 0);
    }
    
    public IArithmeticMode defaultArithmeticMode(Symbol sym, boolean jml) {
        initModeSymbols();
        if (!jml) {
            if (sym.attribute(codeBigintMath) != null) return org.jmlspecs.openjml.ext.Arithmetic.Math.instance(context);
            if (sym.attribute(codeSafeMath) != null) return org.jmlspecs.openjml.ext.Arithmetic.Safe.instance(context);
            if (sym.attribute(codeJavaMath) != null) return org.jmlspecs.openjml.ext.Arithmetic.Java.instance(context);
            sym = sym.owner;
            if (!(sym instanceof Symbol.PackageSymbol)) return defaultArithmeticMode(sym,jml);
            return org.jmlspecs.openjml.ext.Arithmetic.Safe.instance(context);
        } else {
            if (sym.attribute(specBigintMath) != null) return org.jmlspecs.openjml.ext.Arithmetic.Math.instance(context);
            if (sym.attribute(specSafeMath) != null) return org.jmlspecs.openjml.ext.Arithmetic.Safe.instance(context);
            if (sym.attribute(specJavaMath) != null) return org.jmlspecs.openjml.ext.Arithmetic.Java.instance(context);
            sym = sym.owner;
            if (!(sym instanceof Symbol.PackageSymbol)) return defaultArithmeticMode(sym,jml);
            return org.jmlspecs.openjml.ext.Arithmetic.Math.instance(context);
        }
    }



    /** Returns true if a declaration with the given flags is visible in the
     * 'base' class when declared in the 'parent' class. This is standard
     * Java visibility.
     */
    public boolean visible(Symbol base, Symbol parent, long flags) {
        if (base == parent) return true; // Everything is visible in its own class
        if (base.isEnclosedBy((ClassSymbol)parent)) return true; // Everything is visible to inner classes
        if ((flags & Flags.PUBLIC) != 0) return true; // public things are always visible
        if ((flags & Flags.PRIVATE) != 0) return false; // Private things are never visible outside their own class
        if (base.packge().equals(parent.packge())) return true; // Protected and default things are visible if in the same package
        return (flags & Flags.PROTECTED) != 0 && base.isSubClass(parent, Types.instance(context)); // Protected things are visible in subclasses
    }

    /** Returns true if a declaration in the 'parent' class with the given flags 
     * is jml-visible in a method in the
     * 'base' class and the method has the given 'methodFlags'. 
     * This check takes into account spec-public and spec-protected declarations
     * and also JML-specific visibility rules. The first argument can be null
     * if checking the visibility, say of a clause.
     */
    public boolean jmlvisible(/*@ nullable */ Symbol s, Symbol base, Symbol parent, long flags, long methodFlags) {
        if (!visible(base,parent,flags)) return false;  // FIXME - this looks backwards - if it is Java-visible, then it ought to be JML visible???
        
        // In JML the clause must be at least as visible to clients as the method
        flags &= Flags.AccessFlags;
        methodFlags &= Flags.AccessFlags;
        
        //boolean isPublic = null != JmlSpecs.instance(context).fieldSpecHasAnnotation((Symbol.VarSymbol)s,JmlTokenKind.SPEC_PUBLIC);
        
        // If target is public, then it is jml-visible, since everyone can see it
        if (flags == Flags.PUBLIC) return true;
        if (s != null && s.attribute(JmlAttr.instance(context).tokenToAnnotationSymbol.get(JmlTokenKind.SPEC_PUBLIC)) != null) return true;

        // Otherwise a public method sees nothing
        if (methodFlags == Flags.PUBLIC) return false;
        
        // If the method itself is private, then anyone who can see the method
        // can also see the target
        if (methodFlags == Flags.PRIVATE) return true;
        
        // By now the method is either protected or package
        // The target is either protected or package or private
        // FIXME - comment more
        if (flags == Flags.PRIVATE && s != null && 
                s.attribute(JmlAttr.instance(context).tokenToAnnotationSymbol.get(JmlTokenKind.SPEC_PROTECTED)) == null
                ) return false;
        
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
    
    public List<Symbol.VarSymbol> listJmlVisibleFields(TypeSymbol base, long baseVisibility, boolean forStatic) {
        List<Symbol.VarSymbol> list = new LinkedList<Symbol.VarSymbol>();
        for (TypeSymbol csym: parents(base, true)) {
            for (Symbol s: csym.members().getElements()) {
                if (s.kind != Kinds.VAR) continue;
                if (isJMLStatic(s) != forStatic) continue;
                if (!jmlvisible(s,base,csym,s.flags()&Flags.AccessFlags,baseVisibility)) continue; // FIXME - jml access flags? on base and on target?
                list.add((Symbol.VarSymbol)s);
            }
        }
        return list;
    }

    public List<Symbol.VarSymbol> listAllFields(TypeSymbol base, boolean forStatic) {
        List<Symbol.VarSymbol> list = new LinkedList<Symbol.VarSymbol>();
        for (TypeSymbol csym: parents(base, true)) {
            for (Symbol s: csym.members().getElements()) {
                if (s.kind != Kinds.VAR) continue;
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

    /** Returns a fully-qualified name for a method symbol, without the signature */ // FIXME - may include <init>
    public String qualifiedName(Symbol sym) {
        return classQualifiedName(sym.owner) + "." + sym.name;
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
    
    public/* @ nullable */JCAnnotation tokenToAnnotationAST(JmlTokenKind jt,
            int position, int endpos) {
        Class<?> c = jt.annotationType;
        if (c == null) return null;
        JmlTree.Maker F = JmlTree.Maker.instance(context);
        Names names = Names.instance(context);
        JCExpression t = nametree(position, "org.jmlspecs.annotation");
        t = (F.at(position).Select(t, names.fromString(c.getSimpleName())));
        JCAnnotation ann = (F.at(position).Annotation(t,
                com.sun.tools.javac.util.List.<JCExpression> nil()));
        ((JmlTree.JmlAnnotation)ann).sourcefile = log().currentSourceFile();
        return ann;
    }
    
    public JCExpression nametree(int position, String s) {
        String[] nms = s.split("\\.");
        JmlTree.Maker F = JmlTree.Maker.instance(context);
        Names names = Names.instance(context);
        JCExpression tree = F.at(position).Ident(nms[0]);
        for (int i = 1; i<nms.length; i++) {
            tree = F.at(position).Select(tree, names.fromString(nms[i]));
        }
        return tree;
    }



    /** Instances of this class are used to abort operations that are not
     * implemented.
     * @author David R. Cok
     */
    public static class JmlNotImplementedException extends RuntimeException {
        private static final long serialVersionUID = 1L;
        public DiagnosticPosition pos;
        public JmlNotImplementedException(DiagnosticPosition pos, String location) {
            super(location);
            this.pos = pos;
        }
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
    
    /** Reports progress to the registered IProgressListener; also checks if
     * the progress listener has received a user-cancellation, in which case
     * this method throws an exception to terminate processing
     * @param ticks amount of work to report
     * @param level level of the message (lower levels are more likely to be printed)
     * @param message the progress message
     */
    public void progress(int ticks, int level, String message) {
        org.jmlspecs.openjml.Main.IProgressListener pr = context.get(org.jmlspecs.openjml.Main.IProgressListener.class);
        boolean cancelled = pr == null ? false : pr.report(ticks,level,message);
        if (cancelled) {
            throw new PropagatedException(new Main.JmlCanceledException("ESC operation cancelled"));
        }
    }
    
    /**
     * Checks to see if two JavaFileObjects point to the same location.
     * In some cases, it's a bad idea to use JavaFileObject.equals, because copying a JavaFileObject can change the path name, even if they point to the same canonical path.
     * This function exists for where JavaFileObject.equals may fail.
     */
    public static boolean ifSourcesEqual(JavaFileObject jfo1, JavaFileObject jfo2) {
        try {
            File file1 = new File(jfo1.getName());
            File file2 = new File(jfo2.getName());
            return file1.getCanonicalPath().equals(file2.getCanonicalPath());
        } catch (IOException e) {}
        return jfo1.equals(jfo2);
    }

    public void warning(JavaFileObject source, int pos, String key, Object ... args) {
        Log log = log();
        JavaFileObject prev = log.useSource(source);
        try {
            log.warning(pos, key, args);
        } finally {
            log.useSource(prev);
        }
    }
    
    public void error(JavaFileObject source, int pos, String key, Object ... args) {
        Log log = log();
        JavaFileObject prev = log.useSource(source);
        try {
            log.error(pos, key, args);
        } finally {
            log.useSource(prev);
        }
    }
    
    public void error(JavaFileObject source, DiagnosticPosition pos, String key, Object ... args) {
        Log log = log();
        JavaFileObject prev = log.useSource(source);
        try {
            log.error(pos, key, args);
        } finally {
            log.useSource(prev);
        }
    }
    
    public void errorAndAssociatedDeclaration(JavaFileObject source, int pos, JavaFileObject assoc, int assocpos, String key, Object ... args) {
        Log log = log();
        JavaFileObject prev = log.useSource(source);
        try {
            log.error(pos, key, args);
        } finally {
            log.useSource(prev);
        }
        prev = log.useSource(assoc);
        try {
            log.error(assocpos, "jml.associated.decl.cf", locationString(pos, source));
        } finally {
            log.useSource(prev);
        }
    }
    
    public void errorAndAssociatedDeclaration(JavaFileObject source, DiagnosticPosition pos, JavaFileObject assoc, DiagnosticPosition assocpos, String key, Object ... args) {
        Log log = log();
        JavaFileObject prev = log.useSource(source);
        try {
            log.error(pos, key, args);
        } finally {
            log.useSource(prev);
        }
        prev = log.useSource(assoc);
        try {
            log.error(assocpos, "jml.associated.decl.cf", locationString(pos, source));
        } finally {
            log.useSource(prev);
        }
    }

}
