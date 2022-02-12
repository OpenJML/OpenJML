package org.jmlspecs.openjml;

import com.sun.tools.javac.util.*;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.AttrContext;
import org.jmlspecs.openjml.visitors.*;
import static org.jmlspecs.openjml.JmlTree.*;


public class JmlCheckSpecs extends JmlTreeScanner {
	
	Context context;
	JmlSpecs specs;

    /** The method used to obtain the singleton instance of JmlEsc for this compilation context */
    public static JmlCheckSpecs instance(Context context) {
    	JmlCheckSpecs instance = context.get(JmlCheckSpecs.class);
        if (instance == null) {
            instance = new JmlCheckSpecs(context);
            context.put(JmlCheckSpecs.class,instance);
        }
        return instance;
    }
    
	java.util.Set<Symbol> checked = new java.util.HashSet<>();

	public void check() {
		var newItems = new java.util.LinkedList<Symbol>();
    	do {
    		newItems.clear();
        	specs.specsTypes.keySet().forEach(s -> { if (checked.add(s)) newItems.add(s); });
        	specs.specsMethods.keySet().forEach(s -> { if (checked.add(s)) newItems.add(s); });
        	specs.specsFields.keySet().forEach(s -> { if (checked.add(s)) newItems.add(s); });
        	newItems.forEach(s -> check(s));
    	} while (newItems.size() != 0);
    }
    
    public void check(Symbol s) {
    	//if (s instanceof Symbol.ClassSymbol) System.out.println("CHECKING " + s.owner + " " + s);
    	specs.getAttrSpecs(s);
    	if (s instanceof ClassSymbol) ((ClassSymbol)s).members().getSymbols().forEach(ss->check(ss));
    }

    private JmlCheckSpecs(Context context) {
        this.context = context;
        specs = JmlSpecs.instance(context);
    }
	
	// FIXME - what about initialization blocks
	
	// FIXME - check that we are getting model classes, methods, fields

}
