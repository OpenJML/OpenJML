/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 * Reviewed: 2018-03-17
 */
package com.sun.tools.javac.comp;

import static com.sun.tools.javac.tree.JCTree.Tag.APPLY;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.ext.Modifiers;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCTypeCast;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

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
        if (instance == null) throw new IllegalStateException("No Factory registered for JmlCheck");
//            instance = new JmlCheck(context); // Registers itself in the super constructor
        return (JmlCheck)instance; // If the registered instance is only a Check, something is catastrophically wrong
    }
    
    /** Set externally in order to control errors about old variables needing to be static. */
    public boolean staticOldEnv = false;
    
    /** Set by setInJml in order to avoid errors about generic casts.*/
    protected boolean isInJml = false;
    
    /** public method to control the isInJml flag; returns the previous value */
    public boolean setInJml(Boolean inJml) {
        boolean b = isInJml;
        isInJml = inJml;
        return b;
    }
    
    /** Overridden to avoid generic cast warnings in JML.
     */
    @Override
    protected Type checkCastable(DiagnosticPosition pos, Type found, Type req) {
        Utils utils = Utils.instance(context);
        if (found.isErroneous()) {
            // continue
        } else if (utils.isExtensionValueType(req)) {
            // Checks legality of explicit casts
            if (types.isSameType(found,req)) return req;
            if (types.isSameType(req, utils.extensionValueType("string"))
                    && types.isSameType(found, Symtab.instance(context).stringType)) {
                return req;
            }
            basicHandler.report(pos, diags.fragment("inconvertible.types", found, req));
            return types.createErrorType(found);
        } else if (utils.isExtensionValueType(found) &&
                !utils.isExtensionValueType(req)) {
            basicHandler.report(pos, diags.fragment("inconvertible.types", found, req));
            return types.createErrorType(found);
        }
        return super.checkCastable(pos,found,req);
    }
    
    /** Overridden to avoid errors about static-ness of old variables in 
     * method specifications and to remove static from instance declarations.
     */
    @Override
    long checkFlags(DiagnosticPosition pos, long flags, Symbol sym, JCTree tree) {
        if (sym.kind == Kinds.ERR) return flags;
        if (staticOldEnv) flags &= ~Flags.STATIC;
        long k = super.checkFlags(pos,flags,sym,tree);
        if (staticOldEnv) { k |= Flags.STATIC; }
        if (tree instanceof JCTree.JCVariableDecl) {
            JCTree.JCVariableDecl d =(JCTree.JCVariableDecl) tree;
            boolean isInstance = JmlAttr.instance(context).findMod(d.mods, Modifiers.INSTANCE) != null;
            if (isInstance) k &= ~Flags.STATIC;
        }
        return k;
    }
    
    @Override
    protected boolean is292targetTypeCast(JCTypeCast tree) { // OPENJML - changed from private to protected
        JCExpression expr = TreeInfo.skipParens(tree.expr);
        if (expr.hasTag(APPLY)) {
            JCMethodInvocation apply = (JCMethodInvocation)expr;
            if (apply.meth == null) return false;  // OPENJML - Overridden to add this check; apply.meth is null for function-like JML backslash operators
        }
        return super.is292targetTypeCast(tree);
    }

    
    @Override
    public Type checkType(DiagnosticPosition pos, Type found, Type req) {
        if (found != null && found.getTag() == TypeTag.ARRAY && req.getTag() == TypeTag.ARRAY &&
                found.toString().equals("org.jmlspecs.utils.IJMLTYPE[]") &&
                req.toString().equals("\\TYPE[]")) {
            // FIXME - can we do the above without converting to String
            // We need this for the implementation of JML.typeargs, but
            // does it cause problems elsewhere?
            return req;
        }
        return super.checkType(pos, found, req);
    }
    
    boolean noDuplicateWarn = false;
    
    void duplicateError(DiagnosticPosition pos, Symbol sym) {
        if (noDuplicateWarn) return;
        super.duplicateError(pos, sym);
    }
    
    // Overridden so that we can hide warnings about not-really-duplicate declarations, when needed
    @Override
    void varargsDuplicateError(DiagnosticPosition pos, Symbol sym1, Symbol sym2) {
        if (!noDuplicateWarn) super.varargsDuplicateError(pos, sym1, sym2);
    }
}
