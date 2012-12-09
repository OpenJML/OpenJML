/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import java.io.File;
import java.io.FileInputStream;
import java.net.URL;
import java.util.HashSet;
import java.util.Properties;
import java.util.Set;

import org.jmlspecs.annotation.NonNull;

import com.sun.tools.javac.code.Flags;
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
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

/** This class holds a number of utility methods.  They could often be
 * static, but we make this a registerable tool, so that it can be 
 * overridden by some enterprising future person.
 */
public class Utils {
    ///////////////////////////////////////////////////////////////////////////////////////
    
    /** The context applicable for this instance of the Utils class. */
    protected Context context;
    
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
        log = Log.instance(context);
    }
    
    /** The error and warning log */
    public final Log log;
    
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
    
    /** The set of keys that control the use of optional comments, set from options */
    public Set<String> commentKeys = new HashSet<String>();
    
    /** A bit that indicates that a declaration was declared within a JML annotation */
    final public static long JMLBIT = 1L << 50; // Any bit that does not conflict with bits in com.sun.tools.javac.code.Flags.

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
    public ClassSymbol createAnnotationSymbol(String fullyQualifiedName) {
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
            helperAnnotationSymbol = createAnnotationSymbol(Strings.helperAnnotation);
        }
        return symbol.attribute(helperAnnotationSymbol)!=null;
    }

    /** Returns true if the given symbol is annotated as Pure */
    public boolean isPure(Symbol symbol) {
        if (pureAnnotationSymbol == null) {
            pureAnnotationSymbol = createAnnotationSymbol(Strings.pureAnnotation);
        }
        return symbol.attribute(pureAnnotationSymbol)!=null;
    }
    /** Caches the symbol for a Pure annotation, which is computed on demand. */
    private ClassSymbol pureAnnotationSymbol = null;

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
                if (JmlAttr.instance(context).hasAnnotation(sym,JmlToken.INSTANCE)) return false;
            } 
        }
        return true;
    }
    
     // FIXME - document
    public Object envString(/*@ non_null */Env<AttrContext> env) {
        return (env.tree instanceof JCCompilationUnit ? 
                ((JCCompilationUnit)env.tree).sourcefile : 
               env.tree instanceof JCClassDecl ? 
                       ((JCClassDecl)env.tree).name : 
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
                if (m.toString().equals(Strings.jmlAnnotationPackage + "."+s)) return a; // FIXME - fix attribution of annotations in MemberEnter
            }
        }
        return null;
    }
    
    /** Finds whether a specified annotation is present in the given modifiers,
     * returning it if it is; this method requires that the annotations have
     * already been attributed.
     * @param mods the modifiers to search
     * @param asym the symbol of the annotation type to find
     * @return the annotation AST if present, null if not
     */
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
        if (rac) log.warning(pos,"jml.not.implemented.rac",feature);
        else if (esc) log.warning(pos,"jml.not.implemented.esc",feature);
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
                  if (found && verbose) 
                      Log.instance(context).noticeWriter.println("Properties read from system classpath: " + s);
              } catch (java.io.IOException e) {
                  Log.instance(context).noticeWriter.println("Failed to read property file " + s); // FIXME - review
              }
          }
      }
      
      // In the user's home directory
      {
          String s = System.getProperty("user.home") + "/" + Strings.propertiesFileName;
          try {
              boolean found = readProps(properties,s);
              if (found && verbose) 
                  Log.instance(context).noticeWriter.println("Properties read from user's home directory: " + s);
          } catch (java.io.IOException e) {
              Log.instance(context).noticeWriter.println("Failed to read property file " + s); // FIXME - review
          }
      }

      // In the working directory
      {
          String s = System.getProperty("user.dir") + "/" + Strings.propertiesFileName;
          try {
              boolean found = readProps(properties,s);
              if (found && verbose) 
                  Log.instance(context).noticeWriter.println("Properties read from working directory: " + s);
          } catch (java.io.IOException e) {
              Log.instance(context).noticeWriter.println("Failed to read property file " + s); // FIXME - review
          }
      }
      
      // FIXME - add on the application classpath
      
      // FIXME - add on the command-line

      if (verbose) {
          // Print out the properties
          for (String key: new String[]{"user.home","user.dir"}) {
              Log.instance(context).noticeWriter.println("Environment:    " + key + " = " + System.getProperty(key));
          }
          for (java.util.Map.Entry<Object,Object> entry: properties.entrySet()) {
              Log.instance(context).noticeWriter.println("Local property: " + entry.getKey() + " = " + entry.getValue());
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
      File f = new File(filename);
      // Options may not be set yet
      if (f.exists()) {
          properties.load(new FileInputStream(f));
          return true;
      }
      return false;
  }

}
