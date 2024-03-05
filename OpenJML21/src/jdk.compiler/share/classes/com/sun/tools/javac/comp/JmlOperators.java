package com.sun.tools.javac.comp;

import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Symbol.OperatorSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

public class JmlOperators extends Operators {

	Context context;
	
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
	
	public final Symtab syms;

    public OperatorSymbol resolveBinary(DiagnosticPosition pos, JCTree.Tag tag, Type op1, Type op2) {
    	JmlTypes jtype = JmlTypes.instance(context);
    	boolean b1 = org.jmlspecs.openjml.Utils.instance(context).isExtensionValueType(op1);
    	boolean b2 = org.jmlspecs.openjml.Utils.instance(context).isExtensionValueType(op2);
    	if (b1 && !b2) {
    	        
    	} else if (b2 && !b1) {
    	    
    	}
    	if (b1 && b2) {
    	    if (op1.toString().equals("org.jmlspecs.lang.string") && tag == JCTree.Tag.PLUS) {
    	        
    	    }
    	}
    	if (jtype.isJmlType(op1) || jtype.isJmlType(op2)) {
    		Name opName = operatorName(tag);
    		for (var s: syms.predefClass.members().getSymbolsByName(opName, s -> s instanceof OperatorSymbol)) {
    			OperatorSymbol op = (OperatorSymbol)s;
    			var args = op.type.getParameterTypes();
    			if (args.tail != null && args.head == op1 && args.tail.head == op2) {
    				return op;
    			}
    		}
    		if (op1 == jtype.REAL || op2 == jtype.REAL) {
    			// This allows for implicit conversions
    			for (var s: syms.predefClass.members().getSymbolsByName(opName, s -> s instanceof OperatorSymbol)) {
    				OperatorSymbol op = (OperatorSymbol)s;
        			var args = op.type.getParameterTypes();
        			if (args.head == jtype.REAL && args.tail.head == jtype.REAL) {
        				return op;
        			}
    			} // FIXME - do we need to insert explicit conversions
    		}
    		if (op1 == jtype.BIGINT || op2 == jtype.BIGINT) {
    			// This allows for implicit conversions
    			for (var s: syms.predefClass.members().getSymbolsByName(opName, s -> s instanceof OperatorSymbol)) {
    				OperatorSymbol op = (OperatorSymbol)s;
        			var args = op.type.getParameterTypes();
                    if (args.head == jtype.BIGINT && args.tail.head == jtype.BIGINT) {
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
    	if (jtype.isJmlType(op)) {
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
