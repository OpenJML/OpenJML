package org.jmlspecs.openjml.strongarm.transforms;

import static org.jmlspecs.openjml.ext.AssignableClauseExtension.assignableClauseKind;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

public class Purifier extends JmlTreeScanner {

    public static Purifier instance;
    private JmlMethodDecl currentMethod;

    final protected Log                    log;
    final protected Utils                  utils;
    final protected JmlTreeUtils           treeutils;
    final protected JmlTree.Maker          M;
    final protected Context                context;
    final Symtab syms;
    public static boolean inferdebug = false; 
    public static boolean verbose = false; 
    private int assignables;
    
    
    public Purifier(Context context) {

        this.context    = context;
        this.log        = Log.instance(context);
        this.utils      = Utils.instance(context);
        this.treeutils  = JmlTreeUtils.instance(context);
        this.M          = JmlTree.Maker.instance(context);
        this.syms       = Symtab.instance(context);
        
        this.inferdebug = JmlOption.isOption(context, org.jmlspecs.openjml.ext.OptionsInfer.INFER_DEBUG);           

        this.verbose = inferdebug 
                || JmlOption.isOption(context,"-verbose") // The Java verbose option
                || utils.jmlverbose >= Utils.JMLVERBOSE;


    }
    
    public static void cache(Context context){
        if(instance==null){
            instance = new Purifier(context);
        }
    }
    
   
    
    public boolean isPure(){
        return assignables == 0;
    }
    
    
    
   
    @Override
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef tree){
        if(tree.clauseKind==assignableClauseKind){
            assignables++;
        }
        
        super.visitJmlMethodClauseStoreRef(tree);
    }
    
    

    
    public static void simplify(JCTree node){
        instance.scan(node);
        
        if(instance.isPure()){
            JCExpression t = instance.M.Ident("org.jmlspecs.annotation.Pure");        
            JCAnnotation ann = instance.M.Annotation(t, List.<JCExpression> nil());

            if(instance.currentMethod.mods.annotations==null){
                instance.currentMethod.mods.annotations = List.of(ann);                
            }else{
                instance.currentMethod.mods.annotations = instance.currentMethod.mods.annotations.append(ann);

            }

        }
    }
    
    public static void simplify(JCTree node, JmlMethodDecl method){
        instance.currentMethod = method;
        instance.assignables = 0;
        Purifier.simplify(node);
    }
    
}
