package com.sun.tools.javac.code;

import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;

import com.sun.tools.javac.code.Source;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.OperatorSymbol;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.comp.Attr;
import com.sun.tools.javac.comp.Check;
import com.sun.tools.javac.comp.Flow;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlFlow;
import com.sun.tools.javac.jvm.ByteCodes;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.JavacMessages;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;
import com.sun.tools.javac.util.Warner;


public class JmlTypes extends Types {

    protected Context context;

    final public JmlType TYPE = new JmlType(JmlToken.BSTYPEUC,null); 
    final public JmlType REAL = new JmlType(JmlToken.BSREAL,null);
    final public JmlType BIGINT = new JmlType(JmlToken.BSBIGINT,null);

    public static JmlTypes instance(Context context) {
        JmlTypes instance = (JmlTypes)context.get(typesKey);
        if (instance == null)
            instance = new JmlTypes(context);
        return instance;
    }
    
    public static void preRegister(Context context) {
        context.put(Types.typesKey, new Context.Factory<Types>() {
            @Override
            public JmlTypes make(Context context) { 
                return new JmlTypes(context);
            }
        });
    }
    
    protected JmlTypes(Context context) {
        super(context);
        this.context = context;
        
        Symtab syms = Symtab.instance(context);
        syms.initType(BIGINT,"\\bigint");
        syms.initType(TYPE,"\\TYPE");
        syms.initType(REAL,"\\real");
//        TYPE.repSym = repSym(TYPE);
//        BIGINT.repSym = repSym(BIGINT);
//        REAL.repSym = repSym(REAL);
        
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

        enterBinop("==", REAL, REAL, syms.booleanType);
        enterBinop("!=", REAL, REAL, syms.booleanType);
        enterBinop(">", REAL, REAL, syms.booleanType);
        enterBinop("<", REAL, REAL, syms.booleanType);
        enterBinop("<=", REAL, REAL, syms.booleanType);
        enterBinop(">=", REAL, REAL, syms.booleanType);

        enterUnop("-", REAL, REAL);

        enterBinop("+", REAL, REAL, REAL);
        enterBinop("-", REAL, REAL, REAL);
        enterBinop("*", REAL, REAL, REAL);
        enterBinop("/", REAL, REAL, REAL);
        enterBinop("%", REAL, REAL, REAL);
    }
    
    @Override
    public boolean isSameType(Type t, Type s) {
        if (t == s) return true;
        if (t instanceof JmlType || s instanceof JmlType) return false;
        return super.isSameType(t, s);
    }
    
    @Override
    public boolean disjointType(Type t, Type s) {
        boolean bt = t instanceof JmlType;
        boolean bs = s instanceof JmlType;
        if (bt != bs) return true;
        if (!bt) return super.disjointType(t, s);
        return t != s;
    }
    
    public boolean isAssignable(Type t, Type s, Warner warn) {
        if (s == t) return true;
        if (s == BIGINT) {
            int tag = t.tag;
            if (isIntegral(tag)) return true;
            return false; // FIXME - call the warner?
        }
        if (s == REAL) {
            int tag = t.tag;
            if (isNumeric(tag)) return true; 
            return false; // FIXME - call the warner?
        }
        return super.isAssignable(t, s, warn);
    }
    
    public boolean isNumeric(int tag) {
        return tag >= TypeTags.BYTE && tag <= TypeTags.DOUBLE;
    }
    
    public boolean isIntegral(int tag) {
        return tag >= TypeTags.BYTE && tag <= TypeTags.LONG;
    }
    
    public boolean isConvertible(Type t, Type s, Warner warn) {
        if (s instanceof JmlType) {
            if (s == BIGINT && isIntegral(s.tag)) return true;
            if (s == REAL && isNumeric(s.tag)) return true;
        }
        return super.isConvertible(t, s, warn);
    }
    
    @Override
    public boolean isSubtypeUnchecked(Type t, Type s, Warner warn) {
        if (s instanceof JmlType) {
            if (s == BIGINT && isIntegral(t.tag)) return true;
            if (s == REAL && isNumeric(s.tag)) return true;
        }
        return super.isSubtypeUnchecked(t, s, warn);
    }
        
    
    public ClassSymbol boxedClass(Type t) {
        if (t instanceof JmlType) {
            return repSym((JmlType)t);
        }
        return reader.enterClass(syms.boxedName[t.tag]);
    }



    @Override
    public boolean isSubtype(Type t, Type s, boolean capture) {
        if (t == s) return true;
        if (t instanceof JmlType || s instanceof JmlType) return false;
        return super.isSubtype(t, s, capture);
    }
    
    @Override
    public boolean containsType(Type t, Type s) {
        if (t == s) return true;
        if (t instanceof JmlType || s instanceof JmlType) return false;
        return super.containsType(t, s);
    }
    
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

    
    @Override
    public boolean isCastable(Type t, Type s, Warner warn) {
        if (s == t) return true;
        if (s == BIGINT) {
            int tag = t.tag;
            if (tag == TypeTags.INT || tag == TypeTags.LONG || tag == TypeTags.SHORT || tag == TypeTags.CHAR || tag == TypeTags.BYTE) return true;
            return false; // FIXME - call the warner?
        }
        if (t == BIGINT) {
            int tag = s.tag;
            if (tag == TypeTags.INT || tag == TypeTags.LONG || tag == TypeTags.SHORT || tag == TypeTags.CHAR || tag == TypeTags.BYTE) return true;
            return false; // FIXME - call the warner?
        }
        return super.isCastable(t, s,warn);
    }
    
    @Override
    public Type lowerBound(Type t) {
        if (t instanceof JmlType) return t;
        return super.lowerBound(t);
    }

    @Override
    public Type upperBound(Type t) {
        if (t instanceof JmlType) return t;
        return super.upperBound(t);
    }
    
    public JCExpression repType(DiagnosticPosition pos, JmlType t) {
        ClassSymbol sym = repSym(t);
        return JmlTree.Maker.instance(context).at(pos).Type(sym.type);
    }
    
    public ClassSymbol repSym(JmlType t) {
        if (t.repSym == null) {
            JmlToken token = t.jmlTypeTag;
            String n;
            if (token == JmlToken.BSTYPEUC) {
                n = "org.jmlspecs.utils.IJMLTYPE";
            } else if (token == JmlToken.BSBIGINT) {
                n = "java.math.BigInteger";
            } else if (token == JmlToken.BSREAL) {
                n = "java.lang.Double";
            } else {
                n = null;
                // FIXME
            }
            t.repSym = JmlAttr.instance(context).createClass(n);
        }
        return t.repSym;
    }
    
    public boolean isJmlType(Type t) {
        return t.tag == TypeTags.UNKNOWN;
    }


}
