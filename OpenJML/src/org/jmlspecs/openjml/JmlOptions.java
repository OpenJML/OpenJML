package org.jmlspecs.openjml;

import java.io.File;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Properties;
import java.util.Stack;

import org.jmlspecs.annotation.NonNull;

import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCNewArray;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Log.WriterKind;

public class JmlOptions extends Options {

    protected Context context;
    
    protected Stack<LinkedHashMap<String,String>> stack = new Stack<>();
    
    protected JmlOptions(Context context) {
        super(context);
        this.context = context;
        defaults();
    }
    
    public static void preRegister(Context context) {
        //JmlOption.init();
        context.put(Options.optionsKey, new JmlOptions(context));
    }
    
    public void defaults() {
        //System.out.println("SETTING DEFAULTS");
        for (JmlOption opt : JmlOption.map.values()) {
            Object d = opt.defaultValue();
            String s = d == null ? null : d.toString();
            put(opt.optionName(),s);
        }
    }
    
    /** Pushes a copy of the current options on the options stack, so the current state of the options can
     * be reinstated by calling popOptions(); the options currently in effect are unchanged, but can be 
     * modified without affecting the pushed copy.
     */
    public void pushOptions() {
        stack.push(values);
        LinkedHashMap<String,String> newvalues = new LinkedHashMap<String,String>();
        newvalues.putAll(values);
        values = newvalues;
    }
    
    /** Deletes the current copy of the options, replacing it with the set of options popped off the options stack;
     * throws an exception if the options stack is empty (because of more pops than pushes).
     */
    public void popOptions() {
        values = stack.pop();
    }
    
}
