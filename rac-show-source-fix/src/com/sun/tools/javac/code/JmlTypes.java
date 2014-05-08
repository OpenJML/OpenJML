package com.sun.tools.javac.code;

import java.util.HashMap;
import java.util.Map;

import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;

import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.OperatorSymbol;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ByteCodes;
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
    
    final protected Map<JmlToken,JmlType> jmltypes = new HashMap<JmlToken,JmlType>();

    /** The singleton instance for the \TYPE JML type */
    final public JmlType TYPE = new JmlType(JmlToken.BSTYPEUC,"org.jmlspecs.utils.IJMLTYPE");
    {
        jmltypes.put(JmlToken.BSTYPEUC, TYPE);
    }

    /** The singleton instance for the \real JML type */
    final public JmlType REAL = new JmlType(JmlToken.BSREAL,"org.jmlspecs.lang.Real");
    {
        jmltypes.put(JmlToken.BSREAL, REAL);
    }
    
    /** The singleton instance for the \bigint JML type */
    final public JmlType BIGINT = new JmlType(JmlToken.BSBIGINT,"java.math.BigInteger");
    {
        jmltypes.put(JmlToken.BSBIGINT, BIGINT);
    }

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
        
        Symtab syms = Symtab.instance(context);
        syms.initType(BIGINT,"\\bigint");
        syms.initType(TYPE,"\\TYPE");
        syms.initType(REAL,"\\real");
        
        enterBinop("==", TYPE, TYPE, syms.booleanType);
        enterBinop("!=", TYPE, TYPE, syms.booleanType);

        enterBinop("==", BIGINT, BIGINT, syms.booleanType);
        enterBinop("!=", BIGINT, BIGINT, syms.booleanType);
        enterBinop(">", BIGINT, BIGINT, syms.booleanType);
        enterBinop("<", BIGINT, BIGINT, syms.booleanType);
        enterBinop("<=", BIGINT, BIGINT, syms.booleanType);
        enterBinop(">=", BIGINT, BIGINT, syms.booleanType);
        
        enterUnop("-", BIGINT, BIGINT);
        enterUnop("++", BIGINT, BIGINT);
        enterUnop("--", BIGINT, BIGINT);

        enterBinop("+", BIGINT, BIGINT, BIGINT);
        enterBinop("-", BIGINT, BIGINT, BIGINT);
        enterBinop("*", BIGINT, BIGINT, BIGINT);
        enterBinop("/", BIGINT, BIGINT, BIGINT);
        enterBinop("%", BIGINT, BIGINT, BIGINT);
        
        // FIXME - shift operators???

        enterBinop("==", REAL, REAL, syms.booleanType);
        enterBinop("!=", REAL, REAL, syms.booleanType);
        enterBinop(">", REAL, REAL, syms.booleanType);
        enterBinop("<", REAL, REAL, syms.booleanType);
        enterBinop("<=", REAL, REAL, syms.booleanType);
        enterBinop(">=", REAL, REAL, syms.booleanType);

        enterUnop("-", REAL, REAL);
        enterUnop("++", REAL, REAL);
        enterUnop("--", REAL, REAL);

        enterBinop("+", REAL, REAL, REAL);
        enterBinop("-", REAL, REAL, REAL);
        enterBinop("*", REAL, REAL, REAL);
        enterBinop("/", REAL, REAL, REAL);
        enterBinop("%", REAL, REAL, REAL);
    }
    
    /** Overrides Types.isSameType with functionality for JML primitive types. */
    @Override
    public boolean isSameType(Type t, Type s) {
        if (t == s) return true;
        if (t instanceof JmlType || s instanceof JmlType) return false;
        return super.isSameType(t, s);
    }
    
    /** Overrides Types.disjointType with functionality for JML primitive types. */
    @Override
    public boolean disjointType(Type t, Type s) {
        boolean bt = t instanceof JmlType;
        boolean bs = s instanceof JmlType;
        if (bt != bs) return true;
        if (!bt) return super.disjointType(t, s);
        return t != s;
    }
    
    /** Overrides Types.isAssignable with functionality for JML primitive types. */
    @Override
    public boolean isAssignable(Type t, Type s, Warner warn) {
        if (s == t) return true;
        if (s == BIGINT) {
            int tag = t.tag;
            if (isIntegral(tag)) return true;
            if (repSym((JmlType)s) == t.tsym) return true;
            return false;
        }
        if (s == REAL) {
            int tag = t.tag;
            if (isNumeric(tag)) return true; 
            if (repSym((JmlType)s) == t.tsym) return true;
            return false;
        }
        return super.isAssignable(t, s, warn);
    }
    
    /** True if the Java tag is a numeric type (not for JML types). */
    public boolean isNumeric(int tag) {
        return tag >= TypeTags.BYTE && tag <= TypeTags.DOUBLE;
    }
    
    /** True if the Java tag is an integral type (not for JML types). */
    public boolean isIntegral(int tag) {
        return tag >= TypeTags.BYTE && tag <= TypeTags.LONG;
    }
    
    /** Overrides Types.isConvertible with functionality for JML primitive types. */
    @Override
    public boolean isConvertible(Type t, Type s, Warner warn) {
        if (s instanceof JmlType) {
            if (s == BIGINT && isIntegral(t.tag)) return true;
            if (s == BIGINT && repSym(BIGINT) == t.tsym) return true;
            if (s == REAL && isNumeric(t.tag)) return true;
            if (s == REAL && repSym(REAL) == t.tsym) return true;
        }
        return super.isConvertible(t, s, warn);
    }
    
    /** Overrides Types.isSubtypeUnchecked with functionality for JML primitive types. */
    @Override
    public boolean isSubtypeUnchecked(Type t, Type s, Warner warn) {
        if (s instanceof JmlType) {
            if (s == BIGINT && isIntegral(t.tag)) return true;
            if (s == REAL && isNumeric(t.tag)) return true;
        }
        return super.isSubtypeUnchecked(t, s, warn);
    }
        
    /** Overrides Types.boxedClass with functionality for JML primitive types. */
    @Override
    public ClassSymbol boxedClass(Type t) {
        if (t instanceof JmlType) {
            return repSym((JmlType)t);
        }
        return reader.enterClass(syms.boxedName[t.tag]);
    }

    /** Overrides Types.unboxedType with functionality for JML primitive types. */
    @Override
    public Type unboxedType(Type t) {
        if (t.tsym == repSym(BIGINT)) return BIGINT;
        if (t.tsym == repSym(REAL)) return REAL;
        if (t.tsym == repSym(TYPE)) return TYPE;
    	return super.unboxedType(t);
    }

    /** Overrides Types.isSubtype with functionality for JML primitive types. */
    @Override
    public boolean isSubtype(Type t, Type s, boolean capture) {
        if (t == s) return true;
        if (t instanceof JmlType || s instanceof JmlType) return false;
        return super.isSubtype(t, s, capture);
    }
    
    /** Overrides Types.containsType with functionality for JML primitive types. */
    @Override
    public boolean containsType(Type t, Type s) {
        if (t == s) return true;
        if (t instanceof JmlType || s instanceof JmlType) return false;
        return super.containsType(t, s);
    }
    
    /** Local method to create a binary operation on JML types */
    private OperatorSymbol enterBinop(String name,
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
    private OperatorSymbol enterUnop(String name,
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
        if (s == BIGINT) {
            if (isIntegral(t.tag)) return true;
            return false;
        }
        if (t == BIGINT) {
            if (isIntegral(s.tag)) return true;
            return false;
        }
        if (s == REAL) {
            if (isNumeric(t.tag)) return true;
            if (t == BIGINT) return true;
            return false;
        }
        if (t == REAL) {
            if (isNumeric(s.tag)) return true;
            if (s == BIGINT) return true;
            return false;
        }
        return super.isCastable(t, s, warn);
    }
    
    /** Overrides Types.lowerBound with functionality for JML primitive types. */
    @Override
    public Type lowerBound(Type t) {
        if (t instanceof JmlType) return t;
        return super.lowerBound(t);
    }

    /** Overrides Types.upperBound with functionality for JML primitive types. */
    @Override
    public Type upperBound(Type t) {
        if (t instanceof JmlType) return t;
        return super.upperBound(t);
    }
    
    /** Returns an AST for the type representing the given JML primitive type */
    public JCExpression repType(DiagnosticPosition pos, JmlType t) {
        ClassSymbol sym = repSym(t);
        return JmlTree.Maker.instance(context).at(pos).Type(sym.type);
    }
    
    /** Returns the ClassSymbol for the RAC representation of the given JML primitive type */
    public ClassSymbol repSym(JmlType t) {
        if (t.repSym == null) {
            String fqName = t.fqName;
            t.repSym = JmlAttr.instance(context).createClass(fqName);
        }
        return t.repSym;
    }
    
    /** Returns true if the given type is a JML primitive type. */
    public boolean isJmlType(Type t) {
        return t.tag == TypeTags.UNKNOWN;
    }
    
    /** Returns true if the given type is a JML primitive type. */
    public boolean isJmlRepType(Type t) {
        return t.tsym == BIGINT.repSym || t.tsym == REAL.repSym || t.tsym == TYPE.repSym; // TODO - avoid having to list JML types
    }
    
    /** Returns true if the given token is the token for a JML primitive type. */
    public boolean isJmlTypeToken(JmlToken t) {
        return jmltypes.get(t) != null;
    }


}
