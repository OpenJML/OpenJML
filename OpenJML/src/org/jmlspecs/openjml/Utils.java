package org.jmlspecs.openjml;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Name;

/** This class holds a number of static constants and utility methods. */
public class Utils {

    /** Global utility value that enables printing of debugging information. */
    public static boolean jmldebug = false;

    /** A bit that distinguishes Java from JML declarations */
    final public static long JMLBIT = 1L << 50; // Any bit that does not conflict with bits in com.sun.tools.javac.code.Flags.

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
    public static boolean isJML(long flags) {
        return (flags & JMLBIT) != 0;
    }
    
    /** Sets the JML flag in the given modifiers.
     * 
     * @param mods The modifiers in which to set the JML flag
     */
    public static void setJML(JCModifiers mods) {
        mods.flags |= JMLBIT;
    }
    
    public static Object envString(Env<AttrContext> env) {
        return (env.tree instanceof JCCompilationUnit ? 
                ((JCCompilationUnit)env.tree).sourcefile : 
               env.tree instanceof JCClassDecl ? 
                       ((JCClassDecl)env.tree).name : 
                           env.tree.getClass());
    }

    final public static long JMLINSTRUMENTED = 1L << 51; // Any bit that does not conflict with bits in com.sun.tools.javac.code.Flags.

    public static boolean isInstrumented(long flags) {
        return (flags & JMLINSTRUMENTED) != 0;
    }
    public static void setInstrumented(JCModifiers mods) {
        mods.flags |= JMLINSTRUMENTED;
    }
    
    /** Unsets the JML flag in the given modifiers.
    * 
    * @param mods The modifiers in which to set the JML flag
    */
    public static void unsetJML(JCModifiers mods) {
        mods.flags &= ~JMLBIT;
    }
   
    /** Returns true if no standard modifiers or annotations have been set
     * @param mods the modifiers structure to check
     * @return true if any standard flags or annotations are set
     */  // FIXME - should this check for just JML annotations?
    public static boolean hasNone(JCModifiers mods) {
        return mods == null || ((mods.flags&Flags.StandardFlags) == 0 && (mods.annotations == null || mods.annotations.isEmpty()));
    }
    
    /** Returns true if any of the specified Java modifiers is set
     * @param mods the modifiers structure to check
     * @return true if any of the given flags are set
     */
    public static boolean hasAny(JCModifiers mods, long flags) {
        return mods == null || ((mods.flags&flags) != 0);
    }
    
    /** Returns true if any Java modifiers other than those specified are set
     * @param mods the modifiers structure to check
     * @return bit-vector of the offending flags
     */
    public static long hasOnly(JCModifiers mods, long flags) {
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
    public static JCTree.JCAnnotation findMod(/*@ nullable */ JCModifiers mods, Name m) {
        if (mods == null) return null;
        for (JCTree.JCAnnotation a: mods.annotations) {
            Type t = a.annotationType.type;
            if (t != null) {
                if (((Symbol.ClassSymbol)t.tsym).fullname.equals(m)) return a; 
            } else {
                // FIXME this is not going to work for unattributed and not-fully qualified annotations
                String s = a.annotationType.toString();
                if (m.toString().equals(s)) return a;
            }
        }
        return null;
    }
    
    /** A string giving the name of the package that JML annotations are in.
     */
    public static final String jmlAnnotationPackage = "org.jmlspecs.annotations";
    
    
    // The following are stored here globally (e.g., for all compilation
	// contexts). I expect they will always be constant, but one could, for
	// example, reset them by a command-line option. No guarantees on the
	// behavior of the tool if these are changed during processing.

    /** This string is the fully-qualified name of the JML compiler messages file */
    public static String messagesJML = "org.jmlspecs.openjml.messages";
    
    /** This array gives the suffixes recognized as JML specification files, in order of priority */
    // This is not final since it might be changed by command-line options
    public static String[] suffixes = { ".refines-java", ".refines-spec", ".refines-jml", ".java", ".spec", ".jml"   };
    
    /** This gives the character that marks a mock directory (cf. JmlSpecs), mostly for use in testing */
    // FIXME - not yet used everywhere it should be
    public static char mockDirChar = '$';
    
    /** A Java property name used to indicate the directory path on which to find specification files */
    public static String specsPathEnvironmentPropertyName = "org.jmlspecs.specspath";

    /** A Java property name giving the directory in which specifications for the Java system libraries are found */
    public static String systemSpecsLocationEnvironmentPropertyName = "org.jmlspecs.system.specs";
    
    /** Set this to the name of a Java property that contains the location of 
     * the project files in Eclipse, so that testing proceeds OK. 
     * If this directory is null or does not exist, it is ignored and tests will fail.
     */
    public static String eclipseProjectLocation = "openjml.eclipseProjectLocation";
}
