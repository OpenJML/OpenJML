package org.jmlspecs.openjml;

import java.io.File;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Properties;
import java.util.Stack;
import java.util.stream.Collectors;

import org.jmlspecs.annotation.NonNull;

import com.sun.tools.javac.main.Arguments;
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
        context.put(Options.optionsKey, new JmlOptions(context));
    }
    
    public static JmlOptions instance(Context context) {
    	return (JmlOptions)Options.instance(context);
    }
    
    public void defaults() {
        //System.out.println("SETTING DEFAULTS");
        for (JmlOption opt : JmlOption.map.values()) {
            Object d = opt.defaultValue();
            String s = d == null ? null : d.toString();
            put(opt.optionName(),s);
        }
    }

    /** Adds additional options to those already present (which may change 
     * previous settings). */
    public void addOptions(String... args) {
        Main.instance(context).processJmlArgs(args, Options.instance(context), null);
    }

    // FIXME - the options popped and pushed should not be ones that have modifier/annotation equivalents
    // So no nonnullbydefault/nullablebydefault and code-math and spec-math
    
    /** Pushes the current options on the option stack (cf. JmlOption), retaining a copy;
     * then adds the given modifiers to the current options.
     * @param mods
     */
    public void pushOptions(JCModifiers mods) {
    	Name optionName = Names.instance(context).fromString("org.jmlspecs.annotation.Options");

        JmlOptions.instance(context).pushOptions();
        JCAnnotation addedOptionsAnnotation = Utils.instance(context).findMod(mods, optionName);
        if (addedOptionsAnnotation != null) {
            List<JCExpression> exprs = addedOptionsAnnotation.getArguments();
            JCExpression rhs = ((JCAssign)exprs.head).rhs;
            String[] opts = rhs instanceof JCNewArray ? ((JCNewArray)rhs).elems.stream().map(e->e.toString()).collect(Collectors.toList()).toArray(new String[((JCNewArray)rhs).elems.size()])
                          : rhs instanceof JCLiteral ? new String[]{ rhs.toString() }
                          : null;
            addOptions(opts);
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
        Main.instance(context).setupOptions();
    }
    
    /** We replace the Arguments tool in order to validate the JML options 
     * when the Java options are validated (during the run-up to compilation 
     * in JavaCompiler).
     */
    public static class JmlArguments extends Arguments {
    	private Context context;
    	
    	public static void register(Context context) {
    		context.put(argsKey, new JmlArguments(context));
    	}
    	
    	public JmlArguments(Context context) {
    		super(context);
    		this.context = context;
    	}
    	
        @Override
    	public boolean validate() {
    		boolean b = super.validate();
    		return Main.instance(context).setupOptions() && b;
    	}
    }
    
}
