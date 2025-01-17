/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 * Reviewed: 2018-03-17
 */
package com.sun.tools.javac.comp;

import static com.sun.tools.javac.tree.JCTree.Tag.APPLY;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.ext.JmlPrimitiveTypes;
import org.jmlspecs.openjml.ext.Modifiers;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.JmlTypes;
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
	
	public Context context;

    /** Creates a new instance - but use instance(), not this constructor, in order to
     * get the unique instance for the current compilation context.
     * @param context the compilation context this instance is for
     */
    protected JmlCheck(/*@non_null*/ Context context) {
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
    
    /** Set by setInJml in order to avoid errors about generic casts.*/
    protected boolean isInJml = false;
    
    /** public method to control the isInJml flag; returns the previous value */
    public boolean setInJml(Boolean inJml) {
        boolean b = isInJml;
        isInJml = inJml;
        return b;
    }
    
    /** Overridden to allow some explicit casts involving JML primitive types
     */
    @Override
    protected Type checkCastable(DiagnosticPosition pos, Type found, Type req) {
        
        Utils utils = Utils.instance(context);
        if (found.isErroneous()) {
            // continue
        } else if (utils.isExtensionValueType(req) || utils.isExtensionValueType(found)) {
            var REAL = JmlPrimitiveTypes.realTypeKind.getType(context);
            var BIGINT = JmlPrimitiveTypes.bigintTypeKind.getType(context);
            var STRING = JmlPrimitiveTypes.stringTypeKind.getType(context);
            var TYPE = JmlPrimitiveTypes.TYPETypeKind.getType(context);
            var javaString = Symtab.instance(context).stringType;
            var javaClass = types.erasure(Symtab.instance(context).classType);
            JmlTypes jtypes = (JmlTypes)types;
            // Checks legality of explicit casts
            if (types.isSameType(found,req)) return req;
            if (types.isSameType(found, STRING) && types.isSameType(req, javaString)) {
                // \string -> String
                return req;
            }
            if (types.isSameType(req, STRING) && types.isSameType(found, javaString)) {
                // String -> \string 
                return req;
            }
            if (types.isSameType(req, REAL) && jtypes.isAnyNumeric(found)) {
                // numeric -> \real
                return req;                
            }
            if (types.isSameType(found, REAL) && jtypes.isAnyNumeric(req)) {
                // \real -> numeric
                return req;                
            }
            if (types.isSameType(found, BIGINT) && jtypes.isAnyIntegral(req)) {
                // \bigint -> integral
                return req;                
            }
            if (types.isSameType(req, BIGINT) && jtypes.isAnyIntegral(found)) {
                // integral -> \bigint
                return req;                
            }
            if (types.isSameType(req, TYPE) && types.isSameType(types.erasure(found), javaClass)) {
                // Class<> -> \TYPE
                return req;                
            }
            utils.error(pos, "jml.message", "A " + found + " may not be cast to a " + req);
            return types.createErrorType(found);
        }
        return super.checkCastable(pos,found,req);
    }
    
    /** Overridden to avoid errors about static-ness of old variables in 
     * method specifications and to remove static from instance declarations.
     */
    @Override
    long checkFlags(DiagnosticPosition pos, long flags, Symbol sym, JCTree tree) {
        if (sym.kind == Kinds.Kind.ERR) return flags;
        boolean isModelField = sym.kind == Kinds.Kind.VAR && org.jmlspecs.openjml.Utils.instance(context).hasModifier(((JCTree.JCVariableDecl)tree).mods, Modifiers.MODEL);
        boolean isAbstractField =  isModelField && (((JCTree.JCVariableDecl)tree).mods.flags & Flags.ABSTRACT) != 0;
        //if (staticOldEnv) flags &= ~Flags.STATIC;
        long wasFinal = flags & Flags.FINAL;
        long k = super.checkFlags(pos,flags & ~(isModelField?Flags.ABSTRACT:0),sym,tree);
        if (isAbstractField) k |= Flags.ABSTRACT;
        //if (staticOldEnv) { k |= Flags.STATIC; }
        if (sym.kind == Kinds.Kind.VAR) {
            JCTree.JCVariableDecl d =(JCTree.JCVariableDecl) tree;
            boolean isInInterface = sym.owner.isInterface();
            boolean isInstance = JmlAttr.instance(context).isInstance(d.mods);
            if (isInstance) k &= ~Flags.STATIC;
            if ((wasFinal==0) && Utils.instance(context).isJML(flags) && sym.owner.isInterface()) {
            	k &= ~Flags.FINAL;
            }
        	if (isInInterface && (k&Flags.AccessFlags)==0) k |= Flags.PUBLIC;
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
    public Type checkType(DiagnosticPosition pos, Type found, Type req, final CheckContext checkContext) {
        var TYPE = JmlPrimitiveTypes.TYPETypeKind.getSymbol(context);
        Symbol BIGINT = JmlPrimitiveTypes.bigintTypeKind.getSymbol(context);

        if (found != null && found.getTag() == TypeTag.ARRAY && req.getTag() == TypeTag.ARRAY &&
                ((Type.ArrayType)found).getComponentType().tsym == TYPE &&
                ((Type.ArrayType)req).getComponentType().tsym == TYPE) {
            return req;
        }
        if (found == req) return found;
        JmlTypes jmltypes = JmlTypes.instance(context);
        // FIXME - all this in isAssignable?
        if (req.tsym == JmlPrimitiveTypes.realTypeKind.getSymbol(context)) {
        	if (found.isNumeric() || found.tsym == BIGINT) return found;
        } else if (req.tsym == BIGINT) {
        	if (found.isIntegral()) return found;
        }
        return super.checkType(pos, found, req, checkContext);
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
