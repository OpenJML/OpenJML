package com.sun.tools.javac.comp;

import static com.sun.tools.javac.code.TypeTags.FORALL;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ForAll;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Warner;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

import org.jmlspecs.annotations.*;

/** The Check class is specialized for JML in order to avoid unchecked-cast warnings
 * for uses of casts in JML expressions.  JML checks these logically.
 * @author David R. Cok
 *
 */
public class JmlCheck extends Check {

    /** Cache a copy of the compilation context, just in case we need it. */
    @NonNull
    protected Context context;
    
    /** Creates a new instance - but use instance(), not this method, in order to
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
            public Check make() {
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
        return (JmlCheck)instance; // If the registered instance is only an Attr, something is catastrophically wrong
    }
    
    boolean isInJml = false;
    
    public boolean setInJml(Boolean inJml) {
        boolean b = isInJml;
        isInJml = inJml;
        return b;
    }
    
    public static class NoWarningsAtAll extends Warner {
        public void warnUnchecked() {
        }
        public void silentUnchecked() {
        }
    }

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

}
