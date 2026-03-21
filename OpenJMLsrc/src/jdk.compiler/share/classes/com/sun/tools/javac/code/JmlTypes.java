/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 * Reviewed: 2018-03-13
 */
package com.sun.tools.javac.code;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.ext.JmlPrimitiveTypes;

import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.OperatorSymbol;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.jvm.ByteCodes;
import com.sun.tools.javac.main.JmlCompiler;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Warner;


/** Extends Types to provide JML specific behavior, in particular support for
 * JML primitive types.
 */
public class JmlTypes extends Types {

    /** The owning compilation context - not to be changed after construction */
    final protected Context context;
    
    /** Returns the singleton instance of JmlTypes for this compilation context. */
    public static JmlTypes instance(Context context) {
        JmlTypes instance = (JmlTypes)context.get(typesKey);
        if (instance == null)
            instance = new JmlTypes(context);
        return instance;
    }
    
    /** Called to register the class to be used in the tool chain. */
    public static void preRegister(Context context) {
        context.put(Types.typesKey, new Context.Factory<Types>() {
            @Override
            public JmlTypes make(Context context) { 
                return new JmlTypes(context);
            }
        });
    }
    
    /** Constructs a new instance - should be used only by instance(), not called
     * directly; adds all function symbols for operations on JML primitive types.
     * @param context
     */
    protected JmlTypes(Context context) {
        super(context);
        this.context = context;
    }
        
    public Symbol.TypeSymbol TYPEsym(Context context) { return JmlPrimitiveTypes.TYPETypeKind.getSymbol(context); }
    public Symbol.TypeSymbol BIGINTsym(Context context) { return JmlPrimitiveTypes.bigintTypeKind.getSymbol(context); }
    public Symbol.TypeSymbol REALsym(Context context) { return JmlPrimitiveTypes.realTypeKind.getSymbol(context); }
    public Symbol.TypeSymbol STRINGsym(Context context) { return JmlPrimitiveTypes.stringTypeKind.getSymbol(context); }
    public Symbol.TypeSymbol RANGEsym(Context context) { return JmlPrimitiveTypes.rangeTypeKind.getSymbol(context); }
    public Symbol.TypeSymbol SETsym(Context context) { return JmlPrimitiveTypes.setTypeKind.getSymbol(context); }
    public Symbol.TypeSymbol SEQsym(Context context) { return JmlPrimitiveTypes.seqTypeKind.getSymbol(context); }
    public Symbol.TypeSymbol MAPsym(Context context) { return JmlPrimitiveTypes.mapTypeKind.getSymbol(context); }
    public Symbol.TypeSymbol ARRAYsym(Context context) { return JmlPrimitiveTypes.arrayTypeKind.getSymbol(context); }
    public Symbol.TypeSymbol LOCSETsym(Context context) { return JmlPrimitiveTypes.locsetTypeKind.getSymbol(context); }
    
    /** Overrides Types.isSameType with functionality for JML primitive types. */
    @Override
    public boolean isSameType(Type t, Type s) {
        if (isJmlType(t) || isJmlType(s)) {
            if (t.tsym != s.tsym) return false;
            var titer = t.getTypeArguments().iterator();
            var siter = s.getTypeArguments().iterator();
            while (titer.hasNext() && siter.hasNext()) {
                if (!isSameType(titer.next(),siter.next())) return false;
            }
            return !titer.hasNext() && !siter.hasNext();

        }
        return super.isSameType(t, s);
    }
    
    /** Overrides Types.disjointType with functionality for JML primitive types. */
    // FIXME - this is not a correct implementation given the comment on the overridden method
    @Override
    public boolean disjointType(Type t, Type s) {
        boolean bt = isJmlType(t);
        boolean bs = isJmlType(s);
        if (bt != bs) return true;
        if (!bt) return super.disjointType(t, s);
        return t != s;
    }
    
    boolean javaOnly = false;
    
    // FIXME - document
    public boolean isAssignable(boolean javaOnly, Type t, Type s, Warner warn) {
        this.javaOnly = javaOnly;
        try {
            return isAssignable(t,s,warn);
        } finally {
            this.javaOnly = false;
        }
    }
    
    /** Overrides Types.isAssignable with functionality for JML primitive types. */
    // is a t assignable to a variable of s, that is, is t implicitly convertible to s
    // FIXME - not sure when this is called
    @Override
    public boolean isAssignable(Type t, Type s, Warner warn) {
        //if (isJmlType(s) || isJmlType(t)) System.out.println("ISASSIGNABLE " + t + " " + s);
        if (s == t) return true;
        if (isSameType(s,t)) return true;
        if (!javaOnly) {
            if (s.tsym == BIGINTsym(context)) {
                if (isJavaIntegral(t)) return true;
                if (t.toString().contains("BigInteger")) return true; // FIXME - improve over string comparison
                return false;
            }
            if (s.tsym == REALsym(context)) {
                if (isNumeric(t)) return true; 
                if (t.tsym == BIGINTsym(context)) return true;
                if (t.toString().contains("BigInteger")) return true;
                return false;
            }
            // FIXME - should get rid of the following - not sure why it is here
            if ((s instanceof JmlListType) != (t instanceof JmlListType)) return false;
            if ((s instanceof JmlListType) && (t instanceof JmlListType)) {
                Iterator<Type> siter = ((JmlListType)s).types.iterator();
                Iterator<Type> titer = ((JmlListType)t).types.iterator();
                if (siter.hasNext() && titer.hasNext()) {
                    if (!isAssignable(titer.next(), siter.next(), warn)) return false;
                }
                if (!siter.hasNext() && !titer.hasNext()) return false;
            }
        }
        
        return super.isAssignable(t, s, warn);
    }
    
    /** True if the Java tag is a numeric type (not for JML types). */ // FIXME - this includes JML types
    public boolean isNumeric(Type t) {
        int i = t.getTag().ordinal();  // FIXME - should not have bigint here -- those calls should use isAnyNumeric
        return i >= TypeTag.BYTE.ordinal() && i <= TypeTag.DOUBLE.ordinal()|| t.tsym == BIGINTsym(context) || t.tsym == REALsym(context);
    }
    
    /** True if the type is an integral type including boxed and JML types. */
    public boolean isAnyNumeric(Type t) {
        if (isAnyIntegral(t)) return true;
        if (t.tsym == REALsym(context)) return true;
        if (t instanceof Type.TypeVar) return false;
        t = unboxedTypeOrType(t);
        return isNumeric(t);
    }
    
    /** True if the Java tag is a Java integral type. */
    public boolean isJavaIntegral(Type t) {
        return t.getTag().isSubRangeOf(TypeTag.LONG);
    }
    
    /** True if the type is an integral type including boxed and JML types. */
    public boolean isAnyIntegral(Type t) {
        if (t.tsym == BIGINTsym(context)) return true;
        if (t instanceof Type.TypeVar) return false;
        if (t.toString().equals("java.math.BigInteger")) return true; // FIXME - do better than String comparison
        t = unboxedTypeOrType(t);
        return isJavaIntegral(t);
    }
    
    /** Returns true if the type allows indexing by some type */
    public boolean isArray(Type t) {
        if (isJmlType(t)) {
            Type arrayLikeType = JmlAttr.instance(context).JMLArrayLike;
            return isSubtype(t, arrayLikeType);
        }
        return super.isArray(t);
    }
    
    /** Returns true if the type allows indexing by integer indices */
    public boolean isIntArray(Type t) {
        if (isJmlType(t)) {
            Type arrayLikeType = JmlAttr.instance(context).JMLIntArrayLike;
            return isSubtype(t, arrayLikeType);
        }
        return super.isArray(t);
    }
    
    /** Returns the element type of a Java array or JML collection type */
    public Type elemtype(Type t) {
        Type elemtype = super.elemtype(t);
        if (elemtype != null || !isArray(t)) return elemtype;
        List<Type> args = t.getTypeArguments();
        int n = args.length();
        if (n == 0) {
            if (t.tsym == STRINGsym(context)) return syms.charType;
            return syms.booleanType; // intset
        } else if (n == 1) {
            if (t.tsym == SETsym(context)) return syms.booleanType;
            return args.head;
        } else {
            return args.last();    // map
        }
    }
    
    /** Returns the index type of a Java array or JML collection type */
    public Type indexType(Type t) {
        if (t instanceof Type.ArrayType) return syms.intType;
        if (isIntArray(t)) return JmlPrimitiveTypes.bigintTypeKind.getType(context);
        List<Type> args = t.getTypeArguments();
        return args.head;
    }
    
    /** Overrides Types.isConvertible with functionality for JML primitive types. */
    // FIXME - not sure when this is called
    // Called at least to check whether an actual argument of a method call can be converted to a formal argument
    @Override
    public boolean isConvertible(Type t, Type s, Warner warn) {
        // For JML primitive types, these implicit conversions are allowed.
        //  t -> t
        //  integral -> \\bigint
        //  numeric -> \\real
        //  \\bigint -> \\real
        //  String -> \string
        if (isJmlType(s) || isJmlType(t)) {
            if (isSameType(t,s)) return true;
             if (t.getTag() == TypeTag.BOT) return false;
            
            //System.out.println("ISCONVERTIBLE " + t + " " + s);
            if (t.tsym == s.tsym) {
                if (t.getTypeArguments().nonEmpty()) return isSameType(t,s);
                return true;
            }
            if (s.tsym == BIGINTsym(context)) {
                return isJavaIntegral(t) || t.tsym == syms.bigIntegerType.tsym;
            }
            if (s.tsym == REALsym(context)) {
                if (isNumeric(t)) return true;
                if (t.tsym == BIGINTsym(context) && isJavaIntegral(t)) return true;
                return false;
            }
            if (s.tsym == STRINGsym(context)) {
                if (t.tsym == syms.stringType.tsym) return true;
                if (t.tsym == syms.charType.tsym) return true;
                return false;
            }
            return false;
        }
        return super.isConvertible(t, s, warn);
    }
    
    /** Overrides Types.isSubtypeUnchecked with functionality for JML primitive types. */
    // This call affects whether actuals match formals (perhaps among other things).
    // JML Primitive types are not considered subtypes of anything but themselves, not even of Object.
    // Permitted implicit conversions are implemented in isConvertible().
    @Override
    public boolean isSubtypeUnchecked(Type t, Type s, Warner warn) {
        if (isJmlType(s) || isJmlType(t)) return isSameType(t, s);  // FIXME - should this use the Warner?
        return super.isSubtypeUnchecked(t, s, warn);
    }
            
    /** Overrides Types.boxedClass with functionality for JML primitive types. */
    // JML types are subject to neither boxing or unboxing
    @Override
    public ClassSymbol boxedClass(Type t) {
        if (isJmlType(t)) return (ClassSymbol)t.tsym;
        return super.boxedClass(t);
    }

    /** Overrides Types.unboxedType with functionality for JML primitive types. */
    // JML types are subject to neither boxing or unboxing
    @Override
    public Type unboxedType(Type t) {
        if (isJmlType(t)) return t;
    	return super.unboxedType(t);
    }

//    /** Overrides Types.isSubtype with functionality for JML primitive types. */
//    @Override
//    public boolean isSubtype(Type t, Type s, boolean capture) {
//        if (t == s) return true;
//        return super.isSubtype(t, s, capture);
//    }
    
    /** Overrides Types.containsType with functionality for JML primitive types. */
    // This method compares the lower-upper bound ranges of two types -- that is, the
    // extends and super declarations of a type argument.
    @Override
    public boolean containsType(Type t, Type s) {
        if (t == s) return true;
        if (isJmlType(t) || isJmlType(s)) return false;
        return super.containsType(t, s);
    }
    
    /** Local method to create a binary operation on JML types, adding it to the collection of predefined operators */
    public OperatorSymbol enterBinop(String name,
            Type left, Type right, Type res) {
        OperatorSymbol opsym = new OperatorSymbol(
                Names.instance(context).fromString(name),
                new MethodType(List.of(left, right), res,
                        List.<Type>nil(), null),
                ByteCodes.nop,
                Symtab.instance(context).predefClass);

        Symtab.instance(context).predefClass.members().enter(opsym);
        return opsym;
    }
    
    /** Local method to create a unary operation on JML types, adding it to the collection of predefined operators */
    public OperatorSymbol enterUnop(String name,
            Type arg,
            Type res) {
        OperatorSymbol sym =
                new OperatorSymbol(names.fromString(name),
                        new MethodType(List.of(arg),
                                res,
                                List.<Type>nil(),
                                null),
                                ByteCodes.nop,
                                Symtab.instance(context).predefClass);
        Symtab.instance(context).predefClass.members().enter(sym);
        return sym;
    }

    
    /** Overrides Types.isCastable with functionality for JML primitive types;
     * true if Type t is castable to Type s. */
    // FIXME - not sure when this is called, e.g. compared to isConvertible
    @Override
    public boolean isCastable(Type t, Type s, Warner warn) {
        if (isJmlType(s) || isJmlType(t)) {
            if (isConvertible(t,s)) return true;
            if (t.tsym == s.tsym) return false;
            // allow explicit cast (that are not already allowed implicitly)
            var BIGINT = BIGINTsym(context);
            var REAL = REALsym(context);
            if (s.tsym == BIGINT) {
                return isJavaIntegral(t) || t.tsym == REAL;
            }
            if (s.tsym == REAL) {
                if (isNumeric(t)) return true;
                if (t.tsym == BIGINT) return true;
                return false;
            }
            if (t.tsym == BIGINT) {
                return isJavaIntegral(s);
            }
            if (t.tsym == REAL) {
                return isNumeric(s);
            }
        }
        return super.isCastable(t, s, warn);
    }
    
    /** Returns the class symbol for the given fully qualified name, creating and interning it if it does not already exist */
    public ClassSymbol createClass(String fqName) {
        try {
            return ClassReader.instance(context).enterClass(Names.instance(context).fromString(fqName));
        } catch (Throwable t) {
            t.printStackTrace(System.out);
            return null;
        }
    }
    
    /** Returns true if the given type is any JML primitive type. */
    public boolean isJmlType(Type ty) {
        if (!(ty instanceof Type.ClassType ct)) return false;
        if (ty.isErroneous()) return false;
        var prim = Symtab.instance(context).jmlPrimitiveType;
        // It is simpler and quicker to test the interfaces directly rather than using isSubType. This test presumes that
        // any JML types have IJmlPrimitiveType as a direct interface.
        for (var t: interfaces(ct)) {
            if (t.tsym == prim.tsym) return true;
        }
        if (ct.tsym.packge().toString().equals("org.jmlspecs.lang.internal")) {
            // This hack was added because the check above used to not always work.
            // (FIXME) Now it is a defensive test that the fix for the above does indeed work.
            // Possibly happens when there are significant parsing errors
            Utils.instance(context).warning(-1, "jml.message", "Type " + ty + " has lost its interfaces");
            return true;
        }
        return false;
    }
    

    /** Returns true iff the type is a datagroup. A field that is a model field and thereby a data group does not qualify. */
    public boolean isOnlyDatagroup(Type t) {
        // Careful: t can be something like (@org.jmlspecs.annotation.NonNull :: org.jmlspecs.lang.JMLDataGroup)
        return t == JmlPrimitiveTypes.datagroupTypeKind.getType(context);
        //return Utils.instance(context).isOnlyDatagroup(t);
    }
    
    /** Return true if this method is JML or declared in a JML file */
    @Override
    public boolean checkJML(MethodSymbol msym) { 
        if (Utils.isJML(msym.flags())) return true;
    	var e = com.sun.tools.javac.comp.Enter.instance(context).getEnv((Symbol.TypeSymbol)msym.owner);
    	if (e == null || e.toplevel.sourcefile.getKind() != JavaFileObject.Kind.SOURCE) return true; 
    	return false;
    }

}
