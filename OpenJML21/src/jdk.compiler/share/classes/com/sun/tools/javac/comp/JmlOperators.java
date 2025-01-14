package com.sun.tools.javac.comp;

import org.jmlspecs.openjml.ext.JmlPrimitiveTypes;

import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Symbol.OperatorSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

public class JmlOperators extends Operators {

    Context context;
    public final Symtab syms; // Cached instance of Symtab for the given context

    protected JmlOperators(Context context) {
        super(context);
        this.context = context;
        syms = Symtab.instance(context);
    }

    public static void preRegister(Context context) {
        context.put(Operators.operatorsKey, new Context.Factory<Operators>() {
            @Override
            public JmlOperators make(Context context) { 
                return new JmlOperators(context);
            }
        });
    }

    public OperatorSymbol resolveBinary(DiagnosticPosition pos, JCTree.Tag tag, Type op1, Type op2) {
        JmlTypes jtype = JmlTypes.instance(context);
        boolean b1 = org.jmlspecs.openjml.Utils.instance(context).isExtensionValueType(op1);
        boolean b2 = org.jmlspecs.openjml.Utils.instance(context).isExtensionValueType(op2);
        Type REAL = JmlPrimitiveTypes.realTypeKind.getType(context);
        var BIGINT = JmlPrimitiveTypes.bigintTypeKind.getSymbol(context);

        if (b1 && !b2) {
            if (jtype.isSameType(op1, REAL)) {
                if (jtype.isAnyNumeric(op2)) op2 = op1; // allow conversion
            }

        } else if (b2 && !b1) {
            if (jtype.isSameType(op2, REAL)) {
                if (jtype.isAnyNumeric(op1)) op1 = op2; // allow conversion
            }
        }
        if ((b1 || jtype.isJmlType(op1)) || (b2 || jtype.isJmlType(op2))) {
            Name opName = operatorName(tag);
            Type eop1 = jtype.erasure(op1);
            Type eop2 = jtype.erasure(op2);
            for (var s: syms.predefClass.members().getSymbolsByName(opName, s -> s instanceof OperatorSymbol)) {
                OperatorSymbol op = (OperatorSymbol)s;
                var args = op.type.getParameterTypes();
                if (args.tail != null && jtype.isSameType(jtype.erasure(args.head),eop1) 
                        && jtype.isSameType(jtype.erasure(args.tail.head), eop2)) {
                    return op;
                }
            }
            if (op1 == REAL || op2 == REAL) {
                // This allows for implicit conversions
                for (var s: syms.predefClass.members().getSymbolsByName(opName, s -> s instanceof OperatorSymbol)) {
                    OperatorSymbol op = (OperatorSymbol)s;
                    var args = op.type.getParameterTypes();
                    if (args.head == REAL && args.tail.head == REAL) {
                        return op;
                    }
                } // FIXME - do we need to insert explicit conversions
            }
            if (op1.tsym == BIGINT || op2.tsym == BIGINT) {
                // This allows for implicit conversions
                for (var s: syms.predefClass.members().getSymbolsByName(opName, s -> s instanceof OperatorSymbol)) {
                    OperatorSymbol op = (OperatorSymbol)s;
                    var args = op.type.getParameterTypes();
                    if (args.head.tsym == BIGINT && args.tail.head.tsym == BIGINT) {
                        return op;
                    } // FIXME - do we need to insert explicit conversions
                }
            }
            org.jmlspecs.openjml.Utils.instance(context).error(pos, "jml.message", "No operator for " + op1 + " " + opName + " " + op2);
            return noOpSymbol;
        }
        return super.resolveBinary(pos,  tag,  op1, op2);
    }
    
    public OperatorSymbol resolveUnary(DiagnosticPosition pos, JCTree.Tag tag, Type op) {
    	JmlTypes jtype = JmlTypes.instance(context);
    	if (jtype.isJmlType(op) || org.jmlspecs.openjml.Utils.instance(context).isExtensionValueType(op)) {
    		Name opName = operatorName(tag);
    		for (var s: syms.predefClass.members().getSymbolsByName(opName, s -> s instanceof OperatorSymbol)) {
    			OperatorSymbol ops = (OperatorSymbol)s;
    			var args = ops.type.getParameterTypes();
    			if (types.isSameType(args.head,op)) return ops;
    		}
    		org.jmlspecs.openjml.Utils.instance(context).error(pos, "jml.message", "No operator for " + opName + " " + op);
			return noOpSymbol;
    	}
        return super.resolveUnary(pos,  tag,  op);
    }

}
