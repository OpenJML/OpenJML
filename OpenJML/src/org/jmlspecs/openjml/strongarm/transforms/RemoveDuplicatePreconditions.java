package org.jmlspecs.openjml.strongarm.transforms;

import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

public class RemoveDuplicatePreconditions extends JmlTreeScanner {

    public static RemoveDuplicatePreconditions instance;
    
    final protected Log                    log;
    final protected Utils                  utils;
    final protected JmlTreeUtils           treeutils;
    final protected JmlTree.Maker          M;
    final protected Context                context;
    final Symtab syms;
    public static boolean inferdebug = false; 
    public static boolean verbose = false; 
    
    public Set<JCIdent> idDone = new HashSet<JCIdent>();
    
    public RemoveDuplicatePreconditions(Context context){
        
        this.context = context;
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.syms = Symtab.instance(context);
        
        this.inferdebug = JmlOption.isOption(context, JmlOption.INFER_DEBUG);           

        this.verbose = inferdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
            || utils.jmlverbose >= Utils.JMLVERBOSE;

    }

    public static void cache(Context context){
        if(instance==null){
            instance = new RemoveDuplicatePreconditions(context);
        }
    }
    
    
    @Override
    public void visitIdent(JCIdent tree){
        //if (tree != null) System.out.println(">>IDENT: " + tree.toString() + " LIO: " + tree.getName().toString().lastIndexOf('_'));

        if(idDone.contains(tree)) return;
        
        if(tree.getName().toString().contains("_JML___result")){
            // transform results
            tree.name = treeutils.makeIdent(0, "\\result", syms.intType).name;
        }else{
            // remove the underscores
            if(tree.getName().toString().contains("_")){
                tree.name = tree.getName().subName(0, tree.getName().toString().lastIndexOf('_'));
            }
        }
        idDone.add(tree);
    }
    
    @Override
    public void scan(JCTree node) {
        //if (node != null) System.out.println("Node: "+ node.toString() + "<CLZ>" + node.getClass());
        super.scan(node);
    }
    
    public void reset(){
        idDone.clear();
    }
    
    public static void simplify(JCTree node){
        instance.reset();
        instance.scan(node);
    }
}
