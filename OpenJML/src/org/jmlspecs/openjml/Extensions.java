/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import java.io.File;
import java.lang.reflect.Constructor;
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
import org.jmlspecs.openjml.ext.Elemtype;
import org.jmlspecs.openjml.ext.Erasure;
import org.osgi.framework.Bundle;

import com.sun.tools.javac.parser.ExpressionExtension;
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
    public @Nullable ExpressionExtension find(int pos, JmlTokenKind token, boolean complain) {
        ExpressionExtension e = extensionInstances.get(token);
        if (e == null) {
            Class<? extends ExpressionExtension> c = extensionClasses.get(token);
            if (c == null) {
                if (complain) Log.instance(context).error(pos,"jml.failure.to.create.ExpressionExtension",token.internedName());
                return null;
            }
            try {
                Constructor<? extends ExpressionExtension> constructor = c.getDeclaredConstructor(Context.class);
                ExpressionExtension instance = constructor.newInstance(context);
                extensionInstances.put(token,instance);
                e = instance;
            } catch (Exception ee) {
                if (complain) Log.instance(context).error(pos,"jml.failure.to.create.ExpressionExtension",token.internedName());
                return null;
            }
        }
        return e;
    }
    
    /** The list of classes that add extensions to the Parser */
    static Class<?>[] extensions = { Elemtype.class, Erasure.class };

    /** A map from token type to the extension class that implements the token */
    static protected Map<JmlTokenKind,Class<? extends ExpressionExtension>> extensionClasses = new HashMap<JmlTokenKind,Class<? extends ExpressionExtension>>();
    protected Map<JmlTokenKind,ExpressionExtension> extensionInstances = new HashMap<JmlTokenKind,ExpressionExtension>();
    
    // This static block runs through all the extension classes and adds
    // appropriate information to the HashMap above, so extensions can be 
    // looked up at runtime.
    public static void register(Context context) {
        Package p = Package.getPackage("org.jmlspecs.openjml.ext");
        try {
            registerPackage(context,p);
        } catch (java.io.IOException e) {
            throw new RuntimeException(e);
        }
        if (JmlOption.isOption(context, JmlOption.STRICT)) return;
        String exts = JmlOption.value(context, JmlOption.EXTENSIONS);
        if (exts == null || exts.isEmpty()) return;
        for (String extname : exts.split(",")) {
            try {
                Class<?> cl = Class.forName(extname);
                if (!registerClass(cl)) {
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
    
    public static void registerPackage(Context context, Package p) throws java.io.IOException {
        java.util.List<Class<?>> extensions;
        extensions = findClasses(context,p);
        for (Class<?> cc: extensions) {
            registerClass(cc);
        }
    }
    
    public static boolean registerClass(Class<?> cc) {
        if (!ExpressionExtension.class.isAssignableFrom(cc)) return false;
        @SuppressWarnings("unchecked")
        Class<? extends ExpressionExtension> c = (Class<? extends ExpressionExtension>)cc;
        JmlTokenKind[] tokens;
        try {
            Method m = c.getMethod("tokens");
            tokens = (JmlTokenKind[])m.invoke(null);
            for (JmlTokenKind t: tokens) {
                extensionClasses.put(t, c);
            }
        } catch (Exception e) {
            return false;
        }
        return true;
    }
    
    // This method finds all the classes in a given package that are OpenJML
    // extensions.
    // 1) In the development environment, the first method of finding elements
    // of a class works, but that does not work in an Eclipse plug-in.
    // 2) In the plug-in, the Bundle approach works. Note though that the Extensions
    // class is not a part of the OpenJMLUI plug-in, thus we need to reference 
    // the plug-in ID as a literal; this approach won't work and may fail
    // catastrophically when used outside of Eclipse.
    public static java.util.List<Class<?>> findClasses(Context context, Package p) throws java.io.IOException {
        ClassLoader classLoader = Thread.currentThread().getContextClassLoader();
        assert classLoader != null;
        String packageName = p.getName();
        String path = packageName.replace('.', '/');
        ArrayList<String> foundClassNames = new ArrayList<String>();

        // This approach works in the development environment
        Enumeration<URL> resources = classLoader.getResources(path);
        while (resources.hasMoreElements()) {
            URL resource = resources.nextElement();

        	JarFile jar = null;
        	try {
        		String n = resource.toString().replace('\\', '/');
        		if (n.startsWith("jar:file:")) {
        			int k = n.indexOf("!");
        			if (k < 0) continue;
        			jar = new JarFile(n.substring(10,k));
        			Enumeration<JarEntry> entries = jar.entries();
        			// Really would like to iterator over the directory named
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
					//System.out.println("FOUND3 " + name);
        			foundClassNames.add(pn);
        		}
        	} catch (Throwable e) {
        		// This will happen if we are not in a plug-in
        	}
        }
        if (foundClassNames.isEmpty()) {
        	// Last resort
        	//Log.instance(context).warning("jml.internal.notsobad","Last resort loading of extensions");
        	String[] cn = { "Elemtype", "Erasure", "PureModifier", "ReachableStatement", "Arithmetic", "Key" };
        	foundClassNames.addAll(Arrays.asList(cn));
        }
        
        ArrayList<Class<?>> classes = new ArrayList<Class<?>>();
        for (String name: foundClassNames) {
        	String fullname = packageName + "." + name;
        	try {
        		Class<?> c = Class.forName(fullname);
        		if (Modifier.isAbstract(c.getModifiers())) continue;
        		Method m = c.getMethod("register",Context.class);
        		m.invoke(null,context); // Purposely fails if there is no static register method
        		classes.add(c);
        		//if (Utils.instance(context).jmlverbose >= Utils.JMLDEBUG) Log.instance(context).noticeWriter.println("Registered extension " + fullname);
        	} catch (Exception e) {
        		// Just skip if there is any exception, such as a
        		// Class or Method not found.
        		//if (Utils.instance(context).jmlverbose >= Utils.JMLDEBUG) Log.instance(context).noticeWriter.println("Failed to register " + fullname);
        		continue;
        	}
        }
        
        return classes;
    }
    
}
