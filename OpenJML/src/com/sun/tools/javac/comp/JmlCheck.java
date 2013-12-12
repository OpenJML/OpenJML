/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.comp;

import static com.sun.tools.javac.code.TypeTags.FORALL;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlToken;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ForAll;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.Warner;

/** The Check class is specialized for JML in order to avoid unchecked-cast warnings
 * for uses of casts in JML expressions.  JML checks these logically. Also adjusts
 * warnings on use of old in method specifications.
 * <p>
 * [TODO: Give examples for clarity]
 * @author David R. Cok
 *
 */
public class JmlCheck extends Check {

    /** Creates a new instance - but use instance(), not this constructor, in order to
     * get the unique instance for the current compilation context.
     * @param context the compilation context this instance is for
     */
    protected JmlCheck(@NonNull Context context) {
        super(context);
        this.context = context;
    }
    
    /** Registers a singleton factory for JmlCheck against the checkKey, so that there is
     * just one instance per context.
     * @param context the context in which to register the instance
     */
    public static void preRegister(final Context context) {
        context.put(Check.checkKey, new Context.Factory<Check>() {
            public Check make(Context context) {
                return new JmlCheck(context); // Registers itself on construction
            }
        });
    }
    
    /** Returns the instance for the given context
     * 
     * @param context the context in which we are working
     * @return the non-null instance of JmlCheck for this context
     */
    public static JmlCheck instance(Context context) {
        Check instance = context.get(checkKey); 
        if (instance == null)
            instance = new JmlCheck(context); // Registers itself in the super constructor
        return (JmlCheck)instance; // If the registered instance is only a Check, something is catastrophically wrong
    }
    
    /** Set externally in order to control errors about old variables needing to be static. */
    public boolean staticOldEnv = false;
    
    /** Set by setInJml in order to avoid errors about generic casts.*/
    protected boolean isInJml = false;
    
    /** public method to control the inJml flag */
    public boolean setInJml(Boolean inJml) {
        boolean b = isInJml;
        isInJml = inJml;
        return b;
    }
    
    /** A warning object that issues no warnings.*/
    public static class NoWarningsAtAll extends Warner {
        public void warnUnchecked() {
        }
        public void silentUnchecked() {
        }
    }

    /** Overridden to avoid generic cast warnings in JML.
     */
    @Override
    protected Type checkCastable(DiagnosticPosition pos, Type found, Type req) {
        if (!isInJml) return super.checkCastable(pos,found,req);
        if (found.tag == FORALL) {
            instantiatePoly(pos, (ForAll) found, req, new NoWarningsAtAll());
            return req;
        } else if (types.isCastable(found, req, new NoWarningsAtAll())) {
            return req;
        } else {
            return typeError(pos,
                             diags.fragment("inconvertible.types"),
                             found, req);
        }
    }
    
    /** Overridden to avoid errors about static-ness of old variables in 
     * method specifications.
     */
    @Override
    long checkFlags(DiagnosticPosition pos, long flags, Symbol sym, JCTree tree) {
        JCTree.JCVariableDecl d = (tree instanceof JCTree.JCVariableDecl) ? (JCTree.JCVariableDecl) tree : null;
        if (staticOldEnv) flags &= ~Flags.STATIC;
        long k = super.checkFlags(pos,flags,sym,tree);
        if (staticOldEnv) { k |= Flags.STATIC; }
        if (d != null) {
            boolean isInstance = JmlAttr.instance(context).findMod(d.mods,JmlToken.INSTANCE) != null;
            if (isInstance) k &= ~Flags.STATIC;
        }
        return k;
    }
}
