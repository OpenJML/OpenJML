package com.sun.tools.javac.comp;

import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Symbol.OperatorSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
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
    	if (op1.toString().equals("\\bigint") || op2.toString().equals("\\bigint")) { // FIXME - compare types directly?
    		JmlType BIGINT = JmlTypes.instance(context).BIGINT;
    		Name n = operatorName(tag);
    		String nt = n + "(\\bigint,\\bigint)";
    		for (var s: syms.predefClass.members().getSymbolsByName(n, s -> s instanceof OperatorSymbol)) {
    			OperatorSymbol op = (OperatorSymbol)s;
    			if (op.toString().equals(nt)) return op;
    		}
    		return super.resolveBinary(pos,  tag,  BIGINT, BIGINT);
    	}
    	return super.resolveBinary(pos,  tag,  op1, op2);
    }
}
