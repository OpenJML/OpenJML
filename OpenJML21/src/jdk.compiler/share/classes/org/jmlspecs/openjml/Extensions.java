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

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.ext.*;

import com.sun.tools.javac.parser.JmlToken;
import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

/** This class manages classes that define extensions. It finds them at application startup, and
 * creates instances of individual extension classes for compilation contexts.
 * This class is a tool in the compiler tool chain, though without a
 * corresponding OpenJDK tool to mimic. This class is not expected to be
 * derived.
 *  */
public class Extensions {
	@SuppressWarnings("unused")
	private Extensions() {}
	
	public static @interface NonNull {}
	public static @interface Nullable {}
    protected static final Context.Key<Extensions> extensionsKey =
            new Context.Key<Extensions>();

    /** The compilation context, set when the class is instantiated */
    protected /*@ non_null */ Context context;

    //@ public constraint context == \old(context);
    
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
    
    // NOTE: The set of extensions is stored in allKinds and is independent 
    // of context.
    
    /** Finds the clause kind for the given token, if any */
    public static @Nullable IJmlClauseKind findKeyword(Token token) {
    	if (token instanceof JmlToken) {
    		JmlToken jt = (JmlToken)token;
    		if (jt.jmlclausekind == null) return jt.jmlclausekind;
            String id = jt.jmlkind.internedName();
            IJmlClauseKind k = allKinds.get(id);
            jt.jmlclausekind = k;
            return k;    		
    	} else if (token.kind == TokenKind.IDENTIFIER){
            return allKinds.get(token.name().toString());
    	} else {
    		return null;
    	}
    }
    
    /** Finds the clause kind for the given keyword, if any */
    public static @Nullable IJmlClauseKind findKeyword(Name name) {
        String id = name.toString();
        return allKinds.get(id);
    }
    
    /** Finds a type or method clause kind for the given keyword, if any */
    public static @Nullable IJmlClauseKind findTM(String keyword) {
        IJmlClauseKind ext = allKinds.get(keyword);
        if (ext instanceof IJmlClauseKind.TypeClause || ext instanceof IJmlClauseKind.MethodClauseKind) return ext;
        return null;
    }
    
    /** Finds a statement or method clause kind for the given keyword, if any */
    public static @Nullable IJmlClauseKind findSM(String keyword) {
        IJmlClauseKind ext = allKinds.get(keyword);
        if (ext instanceof IJmlClauseKind.IStatementKind || ext instanceof IJmlClauseKind.MethodClauseKind) return ext;
        return null;
    }
    
    public static @Nullable IJmlClauseKind.ModifierKind findModifier(String name) {
    	for (var k: allKinds.values()) {
    		if (k instanceof IJmlClauseKind.ModifierKind && ((IJmlClauseKind.ModifierKind)k).fullAnnotation.endsWith(name)) return (IJmlClauseKind.ModifierKind)k;
    	}
    	return null;
    }
    
    /** Last resort list of classes that add extensions to the Parser.
     *  Typically these are found by listing all the classes in
     *  the org.jmlspecs.openjml.ext package */  // TODO - fix this list
    static Class<?>[] extensions = { 
            // Expressions
            Arithmetic.class,
            FrameExpressions.class,
            Functional.class,
            FunctionLikeExpressions.class,
            MiscExpressions.class,
            QuantifiedExpressions.class,
            SingletonExpressions.class,
            StateExpressions.class,
            //Erasure.class, 
            //Key.class, 
            ProgramLocation.class, 
            
            // Modifiers
            Modifiers.class,
            
            // Method clauses
            AssignableClauseExtension.class, 
            CallableClauseExtension.class, 
            ChooseClause.class, 
            MethodResourceClauseExtension.class,
            MethodDeclClauseExtension.class, 
            MethodExprClauseExtensions.class, 
            MethodSimpleClauseExtensions.class, 
            SignalsClauseExtension.class, 
            SignalsOnlyClauseExtension.class, 
            
            // Statements
            Refining.class, 
            GhostModelStatement.class,
            InlinedLoopStatement.class, 
            ReachableStatement.class, 
            SetStatement.class, 
            ShowStatement.class,
            StatementExprExtensions.class, 
            
            // Type Clauses
            TypeDeclClauseExtension.class, 
            TypeExprClauseExtension.class, 
            TypeInClauseExtension.class, 
            TypeInitializerClauseExtension.class, 
            TypeMapsClauseExtension.class, 
            TypeMonitorsForClauseExtension.class, 
            TypeRepresentsClauseExtension.class, 
            TypeRWClauseExtension.class, 
            
            // Class-like data types
            DatatypeExt.class,
            
            // Field-like extensions
            ArrayFieldExtension.class,
            
            // Types
            JMLPrimitiveTypes.class,
            
            LineAnnotationClauses.class,
            MatchExt.class,
            StatementLocationsExtension.class,
            
            };
    
    static public Map<String,IJmlClauseKind> allKinds = new HashMap<>();

    // This static method runs through all the extension classes and adds
    // appropriate information to the HashMap above, so extensions can be 
    // looked up at runtime. The extension classes include the predefined
    // package org.jmlspecs.openjml.ext and any classes or packages given in the
    // extensions option.
    public static void register(Context context) {
        Package p = ClassLoader.getSystemClassLoader().getDefinedPackage("org.jmlspecs.openjml.ext");
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
                p = ClassLoader.getSystemClassLoader().getDefinedPackage(extname); // Package.getPackage(extname);
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
    
    public static boolean registerClass(Context context, Class<?> cce) {
        if (!JmlExtension.class.isAssignableFrom(cce)) {
//            Utils.instance(context).note("Skipped " + cce);
            String s = cce.toString();
            int k = s.indexOf('$');
            if (k > 0) s = s.substring(0, k);
            try { Class.forName(s); return true; } catch (ClassNotFoundException e) { 
 //           	Utils.instance(context).note("Not found " + s);
            }
        	return false; // Extension classes must inherit from JmlExtensionn
        }
        @SuppressWarnings("unchecked")
        Class<? extends JmlExtension> cc = (Class<? extends JmlExtension>)cce;
        try {
            cc.getConstructor().newInstance(); // Instance created only to perform static initialization
            //Utils.instance(context).note("Registered-A " + cc);
            return true;
        } catch (Exception e) {
        }
        try {
            cc.getConstructor(Context.class).newInstance(context);
            //Utils.instance(context).note("Registered-B " + cc);
            return true;
        } catch (Exception e) {
            String s = cce.toString();
            int k = s.indexOf('$');
            if (k > 0) s = s.substring(0, k);
            try { 
            	Class.forName(s);
                Utils.instance(context).note("Registered-C " + cc);
            	return true; 
            } 
            catch (ClassNotFoundException ee) { 
//            	Utils.instance(context).note("Not found " + s); 
            }
            Utils.instance(context).note("Failed " + cc + " " + e.getMessage());
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
        String prefix = "jar:file:";
       
        // This approach works in the development environment
        Enumeration<URL> resources = classLoader.getResources(path);
        while (resources.hasMoreElements()) {
            URL resource = resources.nextElement();
            
            JarFile jar = null;
            try {
                String n = resource.toString().replace('\\', '/').replaceAll("%20"," "); // FIXME - use toExternalForm?
                //System.out.println("RES " + n);
                if (n.startsWith(prefix)) {
                    int k = n.indexOf("!");
                    if (k < 0) continue;
                    jar = new JarFile(n.substring(prefix.length(),k));
                    Enumeration<JarEntry> entries = jar.entries();
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
                        }
                    }
                    methodThatWorked = 1;

                } else {

                    File dir = new File(resource.getFile().replaceAll("%20"," ")); // FIXME - use toExternalForm?
                    //System.out.println("DIR " + dir);
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
                    }
                    methodThatWorked = 2;
                }
            } catch (Exception e) {
                // Just continue - this method does not work
            } finally {
                if (jar != null) jar.close();
            }
        }

//        bl: {
//            // This approach works when running the plug-in in development mode
//            try {
//                Bundle b = Platform.getBundle("org.jmlspecs.OpenJMLUI");
//                if (b == null) break bl;
//                Enumeration<String> paths = b.getEntryPaths("/bin/" + path);
//                while (paths.hasMoreElements()) {
//                    String pn = paths.nextElement();
//                    int k = pn.lastIndexOf('/');
//                    if (k > 0) pn = pn.substring(k+1);
//                    k = pn.lastIndexOf('.');
//                    if (k > 0) pn = pn.substring(0,k);
//                    //System.out.println("FOUND3 " + pn);
//                    foundClassNames.add(pn);
//                }
//                methodThatWorked = 3;
//            } catch (Throwable e) {
//                // This will happen if we are not in a plug-in
//            }
//        }
        ArrayList<Class<?>> classes = new ArrayList<Class<?>>();
        if (foundClassNames.isEmpty()) {
            // Last resort
            Utils.instance(context).note("Last resort loading of extensions");
            for (Class<?> cl : extensions) {
                 classes.add(cl);
            }
            methodThatWorked = 4;

        } else {
        
            for (String name: foundClassNames) {
                String fullname = packageName + "." + name;
                try {
                    Class<?> c = Class.forName(fullname);
                    if (Modifier.isAbstract(c.getModifiers())) continue;
                    classes.add(c);
                } catch (Exception e) {
                    // Just skip if there is any exception, such as a
                    // Class or Method not found.
                	Utils.instance(context).note(true,"Failed to register " + fullname);
                }
            }
            methodThatWorked = 5;
        }
        Utils.instance(context).note(true,"Registered extensions using technique " + methodThatWorked);
        return classes;
    }
    
}
