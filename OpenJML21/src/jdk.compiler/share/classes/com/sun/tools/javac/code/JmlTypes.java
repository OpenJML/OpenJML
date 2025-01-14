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
    
    /** Overrides Types.isSameType with functionality for JML primitive types. */
    @Override
    public boolean isSameType(Type t, Type s) {
        if (t == s) return true;
        if (t instanceof JmlType || s instanceof JmlType) return false;
        return super.isSameType(t, s);
    }
    
    /** Returns true if t and s are the same type or t is the repType of a JML type s */
    public boolean isSameTypeOrRep(Type t, Type s) {
        if (t == s) return true;
        return super.isSameType(t, s);
    }
    
    /** Overrides Types.disjointType with functionality for JML primitive types. */
    // FIXME - this is not a correct implementation given the comment on the overridden method
    @Override
    public boolean disjointType(Type t, Type s) {
        boolean bt = t instanceof JmlType;
        boolean bs = s instanceof JmlType;
        if (bt != bs) return true;
        if (!bt) return super.disjointType(t, s);
        return t != s;
    }
    
    /** Overrides Types.isAssignable with functionality for JML primitive types. */
    // is a t assignable to s, that is, is t a subtype of s
    @Override
    public boolean isAssignable(Type t, Type s, Warner warn) {
        if (s == t) return true;
        if (isSameType(s,t)) return true;
        if (s.tsym == JmlPrimitiveTypes.bigintTypeKind.getSymbol(context)) {
            if (isIntegral(t)) return true;
            if (t.toString().contains("BigInteger")) return true;
            return false;
        }
        if (s.tsym == JmlPrimitiveTypes.realTypeKind.getSymbol(context)) {
            if (isNumeric(t)) return true; 
            if (t.tsym == JmlPrimitiveTypes.bigintTypeKind.getSymbol(context)) return true;
            if (t.toString().contains("BigInteger")) return true;
            return false;
        }
        if ((s instanceof JmlListType) != (t instanceof JmlListType)) return false;
        if ((s instanceof JmlListType) && (t instanceof JmlListType)) {
            Iterator<Type> siter = ((JmlListType)s).types.iterator();
            Iterator<Type> titer = ((JmlListType)t).types.iterator();
            if (siter.hasNext() && titer.hasNext()) {
                if (!isAssignable(titer.next(), siter.next(), warn)) return false;
            }
            if (!siter.hasNext() && !titer.hasNext()) return false;
        }
        
        return super.isAssignable(t, s, warn);
    }
    
    /** True if the Java tag is a numeric type (not for JML types). */
    public boolean isNumeric(Type t) {
        int i = t.getTag().ordinal();  // FIXME - should not have bigint here -- those calls should use isAnyNumeric
        return i >= TypeTag.BYTE.ordinal() && i <= TypeTag.DOUBLE.ordinal()|| t.tsym == JmlPrimitiveTypes.bigintTypeKind.getSymbol(context) || t.tsym == JmlPrimitiveTypes.realTypeKind.getSymbol(context);
    }
    
    /** True if the type is an integral type including boxed and JML types. */
    public boolean isAnyNumeric(Type t) {
        if (isAnyIntegral(t)) return true;
        if (t.tsym == JmlPrimitiveTypes.realTypeKind.getSymbol(context)) return true;
        if (t instanceof Type.TypeVar) return false;
        t = unboxedTypeOrType(t);
        return isNumeric(t);
    }
    
    /** True if the Java tag is an integral type (not for JML types). */
    public boolean isIntegral(Type t) {
        return t.getTag().isSubRangeOf(TypeTag.LONG);
    }
    
    /** True if the type is an integral type including boxed and JML types. */
    public boolean isAnyIntegral(Type t) {
        if (t.tsym == JmlPrimitiveTypes.bigintTypeKind.getSymbol(context)) return true;
        if (t instanceof Type.TypeVar) return false;
        if (t.toString().equals("java.math.BigInteger")) return true;
        t = unboxedTypeOrType(t);
        return isIntegral(t);
    }
    
    public boolean isArray(Type t) {
        boolean b = super.isArray(t);
        if (!b && t.isReference()) {
            Type arrayLikeType = JmlAttr.instance(context).JMLArrayLike;
            return isSubtype(t, arrayLikeType);
        }
        return b;
    }
    
    public boolean isIntArray(Type t) {
        boolean b = super.isArray(t);
        if (!b && t.isReference()) {
            Type arrayLikeType = JmlAttr.instance(context).JMLIntArrayLike;
            return isSubtype(t, arrayLikeType);
        }
        return b;
    }
    
    public Type elemtype(Type t) {
        Type elemtype = super.elemtype(t);
        if (elemtype != null || !isArray(t)) return elemtype;
        List<Type> args = t.getTypeArguments();
        int n = args.length();
        String tt = t.tsym.toString().substring("org.jmlspecs.lang.".length());
        if (n == 0) {
            if (tt.equals("string")) return syms.charType;
            return syms.booleanType; // intset
        } else if (n == 1) {
            if (tt.equals("array")) return args.head;
            if (tt.equals("intmap")) return args.head;
            if (tt.equals("seq")) return args.head;
            return syms.booleanType; // set
        } else {
            return args.last();    // map
        }
    }
    
    public Type indexType(Type t) {
        if (t instanceof Type.ArrayType) return syms.intType;
        if (isIntArray(t)) return JmlPrimitiveTypes.bigintTypeKind.getType(context);
        List<Type> args = t.getTypeArguments();
        return args.head;
    }
    
    /** Overrides Types.isConvertible with functionality for JML primitive types. */
    @Override
    public boolean isConvertible(Type t, Type s, Warner warn) {
        if (s instanceof JmlType) {
            if (s == JmlPrimitiveTypes.bigintTypeKind.getType(context) && isIntegral(t)) return true;
            if (s == JmlPrimitiveTypes.realTypeKind.getType(context) && isNumeric(t)) return true;
            //if (s == REAL && repSym(REAL) == t.tsym) return true;
            return false;
        }
        return super.isConvertible(t, s, warn);
    }
    
    /** Overrides Types.isSubtypeUnchecked with functionality for JML primitive types. */
    @Override
    public boolean isSubtypeUnchecked(Type t, Type s, Warner warn) {
        if (t == s) return true;
        if (s == JmlPrimitiveTypes.realTypeKind.getType(context)) return isNumeric(t);
        if (s instanceof JmlType) {
            if (s == JmlPrimitiveTypes.bigintTypeKind.getType(context)) return isIntegral(t);
            else return false;  // FIXME - not sure about the semantics and logic here
        }
        return super.isSubtypeUnchecked(t, s, warn);
    }
            
    /** Overrides Types.boxedClass with functionality for JML primitive types. */
    @Override
    public ClassSymbol boxedClass(Type t) {
        if (Utils.instance(context).isExtensionValueType(t)) return (ClassSymbol)t.tsym;
        return super.boxedClass(t);
    }

    /** Overrides Types.unboxedType with functionality for JML primitive types. */
    @Override
    public Type unboxedType(Type t) {
        if (Utils.instance(context).isExtensionValueType(t)) return t;
    	return super.unboxedType(t);
    }

    /** Overrides Types.isSubtype with functionality for JML primitive types. */
    @Override
    public boolean isSubtype(Type t, Type s, boolean capture) {
        if (t == s) return true;
       // if (super.isSubtype(t, Utils.instance(context).interfaceForPrimitiveTypes()) || super.isSubtype(s, Utils.instance(context).interfaceForPrimitiveTypes())) return false;
        return super.isSubtype(t, s, capture);
    }
    
    /** Overrides Types.containsType with functionality for JML primitive types. */
    @Override
    public boolean containsType(Type t, Type s) {
        if (t == s) return true;
        if (Utils.instance(context).isExtensionValueType(t) || Utils.instance(context).isExtensionValueType(t)) return false;
        return super.containsType(t, s);
    }
    
    /** Local method to create a binary operation on JML types */
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
    
    /** Local method to create a unary operation on JML types */
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
    @Override
    public boolean isCastable(Type t, Type s, Warner warn) {
        if (s == t) return true;
        var BIGINT = JmlPrimitiveTypes.bigintTypeKind.getType(context);
        var REAL = JmlPrimitiveTypes.realTypeKind.getType(context);
        if (s == BIGINT) {
            if (isIntegral(t)) return true;
            return false;
        }
        if (t == BIGINT) {
            if (isIntegral(s)) return true;
            return false;
        }
        if (s == REAL) {
            if (isNumeric(t)) return true;
            if (t == BIGINT) return true;
            return false;
        }
        if (t == REAL) {
            if (isNumeric(s)) return true;
            if (s == BIGINT) return true;
            return false;
        }
        return super.isCastable(t, s, warn);
    }
    
    public ClassSymbol createClass(String fqName) {
        try {
        return ClassReader.instance(context).enterClass(Names.instance(context).fromString(fqName));
        } catch (Throwable t) {
            t.printStackTrace(System.out);
            return null;
        }
    }
    
    /** Returns true if the given type is any JML primitive type. */
    public boolean isJmlType(Type t) {
        return Utils.instance(context).isExtensionValueType(t);
    }
    

//    /** Returns true if the given token is the token for a JML primitive type. */
//    public boolean isJmlTypeToken(JmlTokenKind t) {
//        return jmltypes.get(t) != null;
//    }
//    
    /** Returns true iff the type is a datagroup. A field that is a model field and thereby a data group does not qualify. */
    public boolean isOnlyDataGroup(Type t) {
        // Careful: t can be something like (@org.jmlspecs.annotation.NonNull :: org.jmlspecs.lang.JMLDataGroup)
        return Utils.instance(context).isOnlyDatagroup(t);
        //return t.toString().contains("JMLDataGroup"); // FIXME - implement a better way
    }
    
    @Override
    public boolean checkJML(MethodSymbol msym) { 
    	// Return true if this method is JML or declared in a JML file
        if (Utils.instance(context).isJML(msym.flags())) return true;
    	var e = com.sun.tools.javac.comp.Enter.instance(context).getEnv((Symbol.TypeSymbol)msym.owner);
    	if (e == null || e.toplevel.sourcefile.getKind() != JavaFileObject.Kind.SOURCE) return true; 
    	return false;
    }

}
