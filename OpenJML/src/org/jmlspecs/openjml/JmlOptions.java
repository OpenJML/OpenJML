package org.jmlspecs.openjml;

import java.util.LinkedHashMap;
import java.util.Stack;

import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCNewArray;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;

public class JmlOptions extends Options {

    protected Context context;
    
    protected Stack<LinkedHashMap<String,String>> stack = new Stack<>();
    
    protected JmlOptions(Context context) {
        super(context);
        this.context = context;
        defaults();
    }
    
    public static void preRegister(Context context) {
        context.put(Options.optionsKey, new JmlOptions(context));
    }
    
    public void defaults() {
        //System.out.println("SETTING DEFAULTS");
        for (JmlOption opt : JmlOption.values()) {
            Object d = opt.defaultValue();
            String s = d == null ? null : d.toString();
            put(opt.optionName(),s);
        }
    }
    
    public void pushOptions() {
        stack.push(values);
        LinkedHashMap<String,String> newvalues = new LinkedHashMap<String,String>();
        newvalues.putAll(values);
        values = newvalues;
    }
    
    public void popOptions() {
        values = stack.pop();
    }
    

}
