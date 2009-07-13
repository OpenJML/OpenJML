package org.jmlspecs.openjml;

import java.util.Set;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

/** This class holds a number of utility methods.  They could often be
 * static, but we make this a registerable tool, so that it can be 
 * overridden by some enterprising future person.
 */
public class Utils {
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
        context.put(utilsKey, this);
    }
    /** Global utility value that enables printing of debugging information. */
    public boolean jmldebug = false;

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
    
    /** The set of keys that control the use of optional comments */
    public Set<Name> commentKeys;
    
    /** A bit that indicates that a declaration was declared within a JML annotation */
    final public static long JMLBIT = 1L << 50; // Any bit that does not conflict with bits in com.sun.tools.javac.code.Flags.

    /** A bit that indicates that JML instrumentation has been added .... FIXME */
    final public static long JMLINSTRUMENTED = 1L << 51; // Any bit that does not conflict with bits in com.sun.tools.javac.code.Flags.


    /** Tests whether the JML flag is set in the given modifiers object
     * @param mods the instance of JCModifiers to test
     * @return true if JML is set
     */
    public boolean isJML(/*@ nullable */ JCModifiers mods) {
        return mods != null && (mods.flags & JMLBIT) != 0;
    }
    
    /** Tests whether the JML flag is set in the given bit-vector
     * @param flags the bit-array to test
     * @return true if JML is set
     */
    public boolean isJML(long flags) {
        return (flags & JMLBIT) != 0;
    }
    
    /** Sets the JML flag in the given modifiers.
     * 
     * @param mods The modifiers in which to set the JML flag
     */
    public void setJML(/*@ non_null */ JCModifiers mods) {
        mods.flags |= JMLBIT;
    }
    
    /** Unsets the JML flag in the given modifiers.
     * 
     * @param mods The modifiers in which to set the JML flag
     */
     public void unsetJML(/*@ non_null */ JCModifiers mods) {
         mods.flags &= ~JMLBIT;
     }
    
    // FIXME - document
    public Object envString(/*@ non_null */Env<AttrContext> env) {
        return (env.tree instanceof JCCompilationUnit ? 
                ((JCCompilationUnit)env.tree).sourcefile : 
               env.tree instanceof JCClassDecl ? 
                       ((JCClassDecl)env.tree).name : 
                           env.tree.getClass());
    }

    // FIXME - document
    public boolean isInstrumented(long flags) {
        return (flags & JMLINSTRUMENTED) != 0;
    }

    // FIXME - document
    public void setInstrumented(/*@ non_null */JCModifiers mods) {
        mods.flags |= JMLINSTRUMENTED;
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
    public JCTree.JCAnnotation findMod(/*@ nullable */ JCModifiers mods, /*@ non_null */Name m) {
        if (mods == null) return null;
        for (JCTree.JCAnnotation a: mods.annotations) {
            Type t = a.annotationType.type;
            if (t != null) {
                // FIXME - can this be done by comparing symbols rather than strings
                if (((Symbol.ClassSymbol)t.tsym).fullname.equals(m)) return a; 
            } else {
                // FIXME this is not going to work for unattributed and not-fully qualified annotations
                String s = a.annotationType.toString();
                if (m.toString().equals(s)) return a;
                if (m.toString().equals("org.jmlspecs.annotations."+s)) return a; // FIXME - fix attribution of annotations in MemberEnter
            }
        }
        return null;
    }
    
    public JCTree.JCAnnotation findMod(/*@ nullable */ JCModifiers mods, /*@ non_null */Symbol asym) {
        if (mods == null) return null;
        for (JCTree.JCAnnotation a: mods.annotations) {
            Type t = a.annotationType.type;
            if (t != null) {
                if (t.tsym.equals(asym)) return a; 
            } else {
                // FIXME this is not going to work for unattributed and not-fully qualified annotations
                String s = a.annotationType.toString();
                if (asym.flatName().toString().equals(s)) return a;
            }
        }
        return null;
    }
    
    public boolean hasValidSuffix(String filename) {
        for (String s : suffixes) {
            if (filename.endsWith(s)) return true;
        }
        return false;
    }
    
    
    // The following are stored here globally (e.g., for all compilation
	// contexts). I expect they will always be constant, but one could, for
	// example, reset them by a command-line option. No guarantees on the
	// behavior of the tool if these are changed during processing.  They are
    // final for now - which could be changed if necessary.

    /** A string giving the name of the package that JML annotations are in.
     */
    /*@ non_null*/
    public static final String jmlAnnotationPackage = "org.jmlspecs.annotations";
    
    /** This string is the fully-qualified name of the JML compiler messages file */
    /*@ non_null*/
    public static final String messagesJML = "org.jmlspecs.openjml.messages";
    
    /** This array gives the suffixes recognized as JML specification files, in order of priority */
    /*@ non_null*/
    public static final String[] suffixes = { ".refines-java", ".refines-spec", ".refines-jml", ".java", ".spec", ".jml"   };
    
    /** This gives the character that marks a mock directory (cf. JmlSpecs), mostly for use in testing */
    // FIXME - not yet used everywhere it should be
    public static final char mockDirChar = '$';
    
    /** A Java property name used to indicate the directory path on which to find specification files */
    /*@ non_null*/
    public static final String specsPathEnvironmentPropertyName = "org.jmlspecs.specspath";

    /** A Java property name giving the directory in which specifications for the Java system libraries are found */
    /*@ non_null*/
    public static final String systemSpecsLocationEnvironmentPropertyName = "org.jmlspecs.system.specs";
    
    /** Set this to the name of a Java property that contains the location of 
     * the project files in Eclipse, so that testing proceeds OK. 
     * If this directory is null or does not exist, it is ignored and tests will fail.
     */
    /*@ non_null*/
    public static final String eclipseProjectLocation = "openjml.eclipseProjectLocation";

    /** Set this to the name of a Java property that contains the location of 
     * the project files in Eclipse, so that testing proceeds OK. 
     * If this directory is null or does not exist, it is ignored and tests will fail.
     */
    /*@ non_null*/
    public static final String eclipseSpecsProjectLocation = "openjml.eclipseSpecsProjectLocation";
    
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
    
    /** This method is never actually executed.  It is here to provide a
     * convenient signature for a method used by ESC - that maps each class
     * to a distinct integer - not necessarily its hashCode (which are not
     * necessarily unique).
     * @param c
     * @return
     */
    public int distinct(Class<?> c) {
        return c.hashCode();
    }

}
