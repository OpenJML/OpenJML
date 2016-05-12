package org.jmlspecs.openjml.strongarm.transforms;

import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.tree.TreeScanner;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

public class AttributeMethod extends TreeScanner {

    final protected Log                    log;
    final protected Utils                  utils;
    final protected JmlTreeUtils           treeutils;
    final protected JmlTree.Maker          M;
    final protected Context                context;
    final Symtab syms;
    public static boolean inferdebug = false; 
    public static boolean verbose = false; 
    public static AttributeMethod instance;
    
    public Set<Name> locals = new HashSet<Name>();
    
    public AttributeMethod(Context context){
        
        this.context    = context;
        this.log        = Log.instance(context);
        this.utils      = Utils.instance(context);
        this.treeutils  = JmlTreeUtils.instance(context);
        this.M          = JmlTree.Maker.instance(context);
        this.syms       = Symtab.instance(context);
        
        this.inferdebug = JmlOption.isOption(context, JmlOption.INFER_DEBUG);           

        this.verbose = inferdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
            || utils.jmlverbose >= Utils.JMLVERBOSE;
    }
    
    public static void cache(Context context){
        if(instance==null){
            instance = new AttributeMethod(context);
        }
    }
    
    
    @Override
    public void visitVarDef(JCVariableDecl tree) {
        
        if(verbose){
            log.noticeWriter.println("[AttributeMethod] Found local: " + tree.toString());
        }
        
        // stash the local
        locals.add(tree.name);
        
        scan(tree.mods);
        scan(tree.vartype);
        scan(tree.init);
    }

    
        
    @Override
    public void scan(JCTree node) {
        super.scan(node);
    }
    
    public static AttributeMethod attribute(JCTree node){
        AttributeMethod m = new AttributeMethod(instance.context);
        
        m.scan(node);
        
        return m;
        
    }
    
}
