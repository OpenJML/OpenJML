/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import java.io.File;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import org.eclipse.core.runtime.Platform;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.JmlExtension.MethodClause;
import org.jmlspecs.openjml.ext.*;
import org.osgi.framework.Bundle;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

/** This class manages extensions. It finds them at application startup, and
 * creates instances of individual extension classes for compilation contexts.
 * This class is a tool in the compiler tool chain, though without a
 * corresponding OpenJDK tool to mimic. This class is not expected to be
 * derived.
 *  */
public class Extensions {
    protected static final Context.Key<Extensions> extensionsKey =
            new Context.Key<Extensions>();

    /** The compilation context, set when the class is instantiated */
    protected /*@ non_null */ Context context;

    //@ public constraint context == \old(context);
    
    protected static Utils utils;
    
    /** A constructor for the class; this class should not be
     * instantiated directly by users - use instance instead to get a
     * singleton instance (for each compilation context).
     */
    protected Extensions(Context context) {
        context.put(extensionsKey, this);
        this.context = context;
    }
    
    /** A factory that returns a singleton instance of the class for the
     * given compilation context.
     */
    static public Extensions instance(Context context) {
        Extensions instance = context.get(extensionsKey);
        if (instance == null)
            instance = new Extensions(context);
        return instance;
    }
    
    /** Returns a (derived instance of) ExpressionExtension if there is one associated
     * with the given token.  Returns null if there is no
     * extension for the given token.
     * @param pos the position of the token, for error reporting
     * @param token the extension token
     * @param complain if true and failed to create an Extension instance, an error is issued
     * @return an instance of a ExpressionExtension object, or null if unrecoverable error
     */
    public @Nullable JmlExtension findE(int pos, String token, boolean complain) {
        JmlExtension e = extensionInstances.get(token);
        if (e == null) {
            Class<? extends JmlExtension> c = extensionClasses.get(token);
            if (c == null) {
                if (complain) Log.instance(context).error(pos,"jml.failure.to.create.JmlExtension",token);
                return null;
            }
            try {
                Constructor<? extends JmlExtension> constructor = c.getDeclaredConstructor(Context.class);
                JmlExtension instance = constructor.newInstance(context);
                extensionInstances.put(token,instance);
                e = instance;
            } catch (Exception ee) {
                if (complain) Log.instance(context).error(pos,"jml.failure.to.create.ExpressionExtension",token);
                return null;
            }
        }
        return e;
    }
    
    public @Nullable IJmlClauseKind findK(int pos, String token, boolean complain) {
        return allKinds.get(token);
    }
    
    // Finds a type or method clause type for the given keyword
    public @Nullable IJmlClauseKind findTM(int pos, String keyword, boolean complain) {
        IJmlClauseKind e = typeMethodClauses.get(keyword);
        if (e == null) {
            // ERROR needed
        }
        return e;
    }
    
    // Finds a statement or method clause type for the given keyword
    public @Nullable IJmlClauseKind findSM(int pos, String keyword, boolean complain) {
        IJmlClauseKind e = statementMethodClauses.get(keyword);
        if (e == null) {
            // ERROR needed
        }
        return e;
    }
    
    
    /** Last resort list of classes that add extensions to the Parser */
    static Class<?>[] extensions = { FunctionLikeExpressions.class, 
            // Expressions
            Arithmetic.class, 
            FunctionLikeExpressions.class, 
            //Erasure.class, 
            //Key.class, 
            ProgramLocation.class, 
            
            // Modifiers
            PureModifier.class,
            
            // Method clauses
            AssignableClauseExtension.class, 
            CallableClauseExtension.class, 
            MethodExprClauseExtensions.class, 
            MethodDeclClauseExtension.class, 
            SignalsClauseExtension.class, 
            SignalsOnlyClauseExtension.class, 
            ChooseClause.class, 
            
            // Statements
            EndStatement.class, 
            InlinedLoopStatement.class, 
            ReachableStatement.class, 
            SetStatement.class, 
            StatementExprExtensions.class, 
            
            // Type Clauses
            TypeExprClauseExtension.class, 
            TypeInClauseExtension.class, 
            TypeMapsClauseExtension.class, 
            TypeMonitorsForClauseExtension.class, 
            TypeRepresentsClauseExtension.class, 
            TypeRWClauseExtension.class, 
            };

    public @Nullable FieldExtension findField(int pos, String token, boolean complain) {
        FieldExtension e = fieldInstances.get(token);
        if (e == null) {
            Class<? extends FieldExtension> c = fieldClasses.get(token);
            if (c == null) {
                if (complain) Log.instance(context).error(pos,"jml.message","Failed to create a field extension object for " + token);
                return null;
            }
            try {
                Constructor<? extends FieldExtension> constructor = c.getDeclaredConstructor();
                FieldExtension instance = constructor.newInstance();
                fieldInstances.put(token,instance);
                e = instance;
            } catch (Exception ee) {
                if (complain) Log.instance(context).error(pos,"jml.message","Failed to create a field extension object for " + token);
                return null;
            }
        }
        return e;
    }
    
    /** A map from token name to the extension class that implements the token */
    static protected Map<String,Class<? extends JmlExtension>> extensionClasses = new HashMap<>();
    protected Map<String,JmlExtension> extensionInstances = new HashMap<>();

    static public Map<String,JmlExtension.ClassLike> classLike = new HashMap<>();
    static public Map<String,IJmlClauseKind> typeMethodClauses = new HashMap<>();
    static public Map<String,IJmlClauseKind> statementMethodClauses = new HashMap<>();
    static public Map<String,IJmlClauseKind> lineAnnotations = new HashMap<>();
    static public Map<String,IJmlClauseKind> expressionKinds = new HashMap<>();
    static public Map<String,IJmlClauseKind> allKinds = new HashMap<>();

    static protected Map<String,Class<? extends FieldExtension>> fieldClasses = new HashMap<>();

    protected Map<String,FieldExtension> fieldInstances = new HashMap<>();
    
    // This static method runs through all the extension classes and adds
    // appropriate information to the HashMap above, so extensions can be 
    // looked up at runtime. The extension classes include the predefined
    // package org.jmlspecs.openjml.ext and any classes or packages given in the
    // extensions option.
    public static void register(Context context) {
        Package p = Package.getPackage("org.jmlspecs.openjml.ext");
        try {
            registerPackage(context,p);
        } catch (java.io.IOException e) {
            throw new RuntimeException(e);
        }
        if (JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) return;
        String exts = JmlOption.value(context, JmlOption.EXTENSIONS);
        if (exts == null || exts.isEmpty()) return;
        for (String extname : exts.split(",")) {
            try {
                Class<?> cl = Class.forName(extname);
                if (cl == null || !registerClass(context,cl)) {
                    Log.instance(context).error("jml.extension.failed", extname, "Improperly formed extension");
                }
                continue;
            } catch (ClassNotFoundException e) {
                // OK - go on to see if it is a package
            }
            try {
                p = Package.getPackage(extname);
                if (p != null) {
                    registerPackage(context,p);
                } else {
                    Log.instance(context).error("jml.extension.failed", extname,"No such package found");
                }
            } catch (Exception e) {
                Log.instance(context).error("jml.extension.failed", extname, e.toString());
            }
        }
    }
    
    /** Register all the classes in the given package, as found by findClasses() */
    public static void registerPackage(Context context, Package p) throws java.io.IOException {
        java.util.List<Class<?>> extensions;
        extensions = findClasses(context,p);
        for (Class<?> cc: extensions) {
            registerClass(context,cc);
        }
    }
    
    private static final int mods = Flags.PUBLIC | Flags.STATIC | Flags.FINAL;
    public static boolean registerClass(Context context, Class<?> cc) {
        // Options self-register when constructor is called
//        if (JmlExtension.class.isAssignableFrom(cc)) {
//            for (Field f: cc.getDeclaredFields()) {
//                if (JmlOption.class.isAssignableFrom(f.getType())) {
//                    //if ((f.getModifiers() & mods) == mods)
//                    
//                }
//            }
//        }
        int mask = Flags.FINAL|Flags.STATIC|Flags.PUBLIC;
        for (Field f: cc.getDeclaredFields()) {
            int mods = f.getModifiers();
            // Look for final static public fields with type IJmlClauseKind
            if ((mods & mask) != mask) continue;
            if (IJmlClauseKind.class.isAssignableFrom(f.getType())) {
                try {
                    IJmlClauseKind kind = (IJmlClauseKind)f.get(null);
                    if (kind != null) allKinds.put(kind.name(), kind);
                    if (kind instanceof IJmlClauseKind.Expression) expressionKinds.put(kind.name(), kind);
                } catch (IllegalAccessException e) {
                    // Error - this should nnever happen
                }
            }
        }
        if (ExpressionExtension.class.isAssignableFrom(cc)) {
            @SuppressWarnings("unchecked")
            Class<ExpressionExtension> c = (Class<ExpressionExtension>)cc;
            JmlTokenKind[] tokens;
            try {
                Method m = c.getMethod("tokens");
                tokens = (JmlTokenKind[])m.invoke(null);
                if (tokens != null) for (JmlTokenKind t: tokens) {
                    extensionClasses.put(t.internedName(), c);
                    //clauseTypes.put(t.name(), t);
                }
                m = c.getMethod("clauseTypes");
                if (m != null) {
                    IJmlClauseKind[] kinds = (IJmlClauseKind[])m.invoke(null);
                    if (kinds != null) for (IJmlClauseKind t: kinds) {
                        expressionKinds.put(t.name(), t);
                    }
                }
            } catch (Exception e) {
                return false;
            }
            return true;
        } else if (FieldExtension.class.isAssignableFrom(cc)) {
            @SuppressWarnings("unchecked")
            Class<? extends FieldExtension> c = (Class<? extends FieldExtension>)cc;
            try {
                Method m = c.getMethod("ids");
                String[] ids = (String[])m.invoke(null);
                for (String t: ids) {
                    fieldClasses.put(t, c);
                }
            } catch (Exception e) {
                return false;
            }
            return true;
        } else if (JmlExtension.MethodClause.class.isAssignableFrom(cc)) {
            @SuppressWarnings("unchecked")
            Class<JmlExtension.MethodClause> c = (Class<JmlExtension.MethodClause>)cc;
            try {
                Constructor<MethodClause> cct = c.getConstructor();
                MethodClause occ = cct.newInstance();
                occ.register(context);
            } catch (Exception e) {
                return false;
            }
            return true;
        } else if (JmlExtension.TypeClause.class.isAssignableFrom(cc)) {
            @SuppressWarnings("unchecked")
            Class<JmlExtension.TypeClause> c = (Class<JmlExtension.TypeClause>)cc;
            try {
                Constructor<JmlExtension.TypeClause> cct = c.getConstructor();
                JmlExtension.TypeClause occ = cct.newInstance();
                occ.register(context);
            } catch (Exception e) {
                return false;
            }
            return true;
        } else if (JmlExtension.LineAnnotation.class.isAssignableFrom(cc)) {
            @SuppressWarnings("unchecked")
            Class<JmlExtension.LineAnnotation> c = (Class<JmlExtension.LineAnnotation>)cc;
            try {
                Constructor<JmlExtension.LineAnnotation> cct = c.getConstructor();
                JmlExtension.LineAnnotation occ = cct.newInstance();
                occ.register(context);
            } catch (Exception e) {
                return false;
            }
            return true;
        } else if (JmlExtension.Statement.class.isAssignableFrom(cc)) {
            @SuppressWarnings("unchecked")
            Class<JmlExtension.Statement> c = (Class<JmlExtension.Statement>)cc;
            try {
                Constructor<JmlExtension.Statement> cct = c.getConstructor();
                JmlExtension.Statement occ = cct.newInstance();
                occ.register(context);
            } catch (Exception e) {
                return false;
            }
            return true;
        } else if (JmlExtension.ClassLike.class.isAssignableFrom(cc)) {
            @SuppressWarnings("unchecked")
            Class<JmlExtension.ClassLike> c = (Class<JmlExtension.ClassLike>)cc;
            try {
                Constructor<JmlExtension.ClassLike> cct = c.getConstructor();
                JmlExtension.ClassLike occ = cct.newInstance();
                occ.register(context);
            } catch (Exception e) {
                return false;
            }
            return true;
        } else {
            return false;
        }
    }
    
    // This method finds all the classes in a given package that are OpenJML
    // extensions.
    // 0) When running from the command-line jar file mode, the first method works - iterating over the contents of the jar file
    //    at least for built-in extension classes
    // 1) In the development environment, the first method of finding elements
    //    of a class works, but that does not work in an Eclipse plug-in.
    // 2) In the plug-in, the Bundle approach works. Note though that the Extensions
    //    class is not a part of the OpenJMLUI plug-in, thus we need to reference 
    //    the plug-in ID as a literal; this approach won't work and may fail
    //    catastrophically when used outside of Eclipse.
    public static java.util.List<Class<?>> findClasses(Context context, Package p) throws java.io.IOException {
        ClassLoader classLoader = Thread.currentThread().getContextClassLoader();
        assert classLoader != null;
        String packageName = p.getName();
        String path = packageName.replace('.', '/');
        ArrayList<String> foundClassNames = new ArrayList<String>();
        int methodThatWorked = -1;
        
        // This approach works in the development environment
        Enumeration<URL> resources = classLoader.getResources(path);
        while (resources.hasMoreElements()) {
            URL resource = resources.nextElement();
            
            JarFile jar = null;
            try {
                String n = resource.toString().replace('\\', '/');
                String prefix = "jar:file:";
                if (n.startsWith(prefix)) {
                    int k = n.indexOf("!");
                    if (k < 0) continue;
                    jar = new JarFile(n.substring(prefix.length(),k));
                    Enumeration<JarEntry> entries = jar.entries();
//                    JarEntry je = jar.getJarEntry(path);
//                    System.out.println("JE: " + je.getName());
                    // Really would like to iterate over the directory named
                    // by 'path', instead of over every entry in the jar file
                    while (entries.hasMoreElements()) {
                        JarEntry entry = entries.nextElement();
                        String name = entry.getName();
                        if (name.startsWith(path)) {
                            name = name.substring(path.length()+1);
                            k = name.indexOf('.');
                            if (k < 0) continue;
                            name = name.substring(0,k);
                            //System.out.println("FOUND1 " + name);
                            foundClassNames.add(name);
                            methodThatWorked = 1;
                        }
                    }
                } else {

                    File dir = new File(resource.getFile());
                    File[] files = dir.listFiles();
                    if (files == null) continue;
                    for (File f: files) {
                        if (f.isDirectory()) continue;
                        String name = f.getName();
                        int k = name.indexOf('.');
                        if (k < 0) continue;
                        name = name.substring(0,k);
                        //System.out.println("FOUND2 " + name);
                        foundClassNames.add(name);
                        methodThatWorked = 2;
                    }
                }
            } catch (Exception e) {
                // Just continue - this method does not work
            } finally {
                if (jar != null) jar.close();
            }
        }

        bl: {
            // This approach works when running the plug-in in development mode
            try {
                Bundle b = Platform.getBundle("org.jmlspecs.OpenJMLUI");
                if (b == null) break bl;
                Enumeration<String> paths = b.getEntryPaths("/bin/" + path);
                while (paths.hasMoreElements()) {
                    String pn = paths.nextElement();
                    int k = pn.lastIndexOf('/');
                    if (k > 0) pn = pn.substring(k+1);
                    k = pn.lastIndexOf('.');
                    if (k > 0) pn = pn.substring(0,k);
                    //System.out.println("FOUND3 " + pn);
                    foundClassNames.add(pn);
                    methodThatWorked = 3;
                }
            } catch (Throwable e) {
                // This will happen if we are not in a plug-in
            }
        }
        ArrayList<Class<?>> classes = new ArrayList<Class<?>>();
        if (foundClassNames.isEmpty()) {
            //System.out.println("LAST RESORT EXTENSION");
            // Last resort
            Log.instance(context).warning("jml.internal.notsobad","Last resort loading of extensions");
            for (Class<?> cl : extensions) {
                try {
                    registerClass(context,cl);
                    if (Utils.instance(context).jmlverbose >= Utils.JMLDEBUG) Log.instance(context).getWriter(Log.WriterKind.NOTICE).println("Registered extensions using technique " + methodThatWorked);
                    classes.add(cl);
                } catch (Exception e) {
                    if (Utils.instance(context).jmlverbose >= Utils.JMLDEBUG) Log.instance(context).getWriter(Log.WriterKind.NOTICE).println("Failed to register " + cl.getName());
                }
            }
        } else {
        
            for (String name: foundClassNames) {
                String fullname = packageName + "." + name;
                try {
                    Class<?> c = Class.forName(fullname);
                    if (Modifier.isAbstract(c.getModifiers())) continue;
                    registerClass(context,c);
                    if (Utils.instance(context).jmlverbose >= Utils.JMLDEBUG) Log.instance(context).getWriter(Log.WriterKind.NOTICE).println("Registered extensions using technique " + methodThatWorked);
                    classes.add(c);
                } catch (Exception e) {
                    // Just skip if there is any exception, such as a
                    // Class or Method not found.
                    if (Utils.instance(context).jmlverbose >= Utils.JMLDEBUG) Log.instance(context).getWriter(Log.WriterKind.NOTICE).println("Failed to register " + fullname);
                }
            }
        }
        return classes;
    }
    
}
