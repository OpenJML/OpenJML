package org.jmlspecs.openjml.strongarm.transforms;

import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.strongarm.translators.FeasibilityCheckerSMT;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCParens;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

public class PruneUselessClauses extends JmlTreeScanner{

    public JCTree currentReplacement;
    public static PruneUselessClauses instance;
    
    final protected Log                    log;
    final protected Utils                  utils;
    final protected JmlTreeUtils           treeutils;
    final protected JmlTree.Maker          M;
    final protected Context                context;
    final Symtab syms;
    public static boolean inferdebug = false; 
    public static boolean verbose = false; 
    
    public PruneUselessClauses(Context context){
        
        this.context    = context;
        this.log        = Log.instance(context);
        this.utils      = Utils.instance(context);
        this.treeutils  = JmlTreeUtils.instance(context);
        this.M          = JmlTree.Maker.instance(context);
        this.syms       = Symtab.instance(context);

        this.inferdebug = JmlOption.isOption(context, org.jmlspecs.openjml.ext.OptionsInfer.INFER_DEBUG);           
        
        this.verbose = inferdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
            || utils.jmlverbose >= Utils.JMLVERBOSE;
    }
    
    public static void cache(Context context){
        if(instance==null){
            instance = new PruneUselessClauses(context);
        }
    }
    
    @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {
        
        List<JmlSpecificationCase> replacedCases = null;
        
        if(tree.cases!=null){
            for(List<JmlSpecificationCase> cases = tree.cases; cases.nonEmpty(); cases = cases.tail)
            {
                int props = PropsInSubtree.count(cases.head);
                
                if(props > 0){
                    if(replacedCases == null){
                        replacedCases = List.of(cases.head);
                    }else{
                        replacedCases = replacedCases.append(cases.head);
                    }
                }
            }
     
            if(replacedCases == null){
                replacedCases = List.nil();
            }
            
            tree.cases = replacedCases;
        }
        super.visitJmlMethodClauseGroup(tree);        
    }
     
    public static void simplify(JCTree node){
        instance.scan(node);
    }
}