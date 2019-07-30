package org.jmlspecs.openjml.strongarm.transforms;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import javax.lang.model.type.TypeKind;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.ext.MethodExprClauseExtensions;
import org.jmlspecs.openjml.ext.OptionsInfer;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

public class TreeContains extends JmlTreeScanner {

    
    final protected Log                    log;
    final protected Utils                  utils;
    final protected JmlTreeUtils           treeutils;
    final protected JmlTree.Maker          M;
    final protected Context                context;
    final Symtab syms;
    public static boolean inferdebug = false; 
    public static boolean verbose = false; 
    
    //
    // things we contain
    //
    private int ensuresClauses;
    
    public TreeContains(Context context){
        
        this.context    = context;
        this.log        = Log.instance(context);
        this.utils      = Utils.instance(context);
        this.treeutils  = JmlTreeUtils.instance(context);
        this.M          = JmlTree.Maker.instance(context);
        this.syms       = Symtab.instance(context);
        
        this.inferdebug = JmlOption.isOption(context, OptionsInfer.INFER_DEBUG);           

        this.verbose = inferdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
            || utils.jmlverbose >= Utils.JMLVERBOSE;
            
    }
    
    public boolean atLeastOneEnsuresClause(){
        return ensuresClauses > 0;
    }

    
    
    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {
        if(tree!=null && tree.clauseKind == MethodExprClauseExtensions.ensuresClauseKind){
            ensuresClauses += 1;
        }
        super.visitJmlMethodClauseExpr(tree);
    }
    
    public void scan(JCTree node) {
        super.scan(node);
    }
    
    public static TreeContains analyze(Context c, JCTree node){
        
        TreeContains tc = new TreeContains(c);
        
        tc.scan(node);
        
        return tc;
        
    }
}
