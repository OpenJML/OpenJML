/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;

import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.ext.Elemtype;

import com.sun.tools.javac.parser.ExpressionExtension;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

/* FIXME - do more to implement extensions */

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
     * @return an instance of a ExpressionExtension object, or null if unrecoverable error
     */
    public @Nullable ExpressionExtension find(int pos, JmlToken token) {
        ExpressionExtension e = extensionInstances.get(token);
        if (e == null) {
            Class<? extends ExpressionExtension> c = extensionClasses.get(token);
            if (c == null) {
                Log.instance(context).error(pos,"jml.failure.to.create.ExpressionExtension",token.internedName());
                return null;
            }
            try {
                Constructor<? extends ExpressionExtension> constructor = c.getDeclaredConstructor(Context.class);
                ExpressionExtension instance = constructor.newInstance(context);
                extensionInstances.put(token,instance);
                e = instance;
            } catch (Exception ee) {
                Log.instance(context).error(pos,"jml.failure.to.create.ExpressionExtension",token.internedName());
                return null;
            }
        }
        return e;
    }
    
    /** The list of classes that add extensions to the Parser */
    static Class<?>[] extensions = { Elemtype.class };

    /** A map from token type to the extension class that implements the token */
    static protected Map<JmlToken,Class<? extends ExpressionExtension>> extensionClasses = new HashMap<JmlToken,Class<? extends ExpressionExtension>>();
    protected Map<JmlToken,ExpressionExtension> extensionInstances = new HashMap<JmlToken,ExpressionExtension>();
    
    // FIXME - change this to find extensions in various packages
    // This static block runs through all the extension classes and adds
    // appropriate information to the HashMap above, so extensions can be 
    // looked up at runtime.
    public static void register(Context context) {
        JmlToken[] tokens;
        for (Class<?> cc: extensions) {
            Class<? extends ExpressionExtension> c = (Class<? extends ExpressionExtension>)cc;
            try {
                Method m = c.getMethod("tokens");
                tokens = (JmlToken[])m.invoke(null);
            } catch (Exception e) {
                continue;
            }
            for (JmlToken t: tokens) {
                extensionClasses.put(t, c);
            }
        }
    }
    
}
