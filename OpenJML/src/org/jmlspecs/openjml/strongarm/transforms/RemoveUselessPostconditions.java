package org.jmlspecs.openjml.strongarm.transforms;

import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.ext.OptionsInfer;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.ext.AssignableClauseExtension;
import org.jmlspecs.openjml.ext.MethodExprClauseExtensions;
import org.jmlspecs.openjml.strongarm.translators.FeasibilityCheckerSMT;
import org.jmlspecs.openjml.strongarm.translators.SubstitutionEQProverSMT;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

public class RemoveUselessPostconditions extends JmlTreeScanner {

    public static RemoveUselessPostconditions instance;
    private JmlMethodDecl currentMethod;

    final protected Log                    log;
    final protected Utils                  utils;
    final protected JmlTreeUtils           treeutils;
    final protected JmlTree.Maker          M;
    final protected Context                context;
    final Symtab syms;
    public static boolean inferdebug = false; 
    public static boolean verbose = false; 

    
    public RemoveUselessPostconditions(Context context) {

        this.context    = context;
        this.log        = Log.instance(context);
        this.utils      = Utils.instance(context);
        this.treeutils  = JmlTreeUtils.instance(context);
        this.M          = JmlTree.Maker.instance(context);
        this.syms       = Symtab.instance(context);
        
        this.inferdebug = JmlOption.isOption(context, OptionsInfer.INFER_DEBUG);           

        this.verbose = inferdebug 
                || JmlOption.isOption(context,"-verbose") // The Java verbose option
                || utils.jmlverbose >= Utils.JMLVERBOSE;


    }
    
    public static void cache(Context context){
        if(instance==null){
            instance = new RemoveUselessPostconditions(context);
        }
    }
    
    protected boolean isUseful(List<JmlMethodClause> clauses){
        
        int assignable = 0, ensures = 0;
        
        for(JmlMethodClause c : clauses){
            
            if(c.clauseKind==MethodExprClauseExtensions.ensuresClauseKind){
                ensures++;
            }
            
            if(c.clauseKind==AssignableClauseExtension.assignableClauseKind){
                assignable++;
            }
        }
        
        return assignable + ensures > 0;

    }
    
    @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {
        
        Set<JmlMethodClauseExpr> props = null;
        
        List<JmlSpecificationCase> replacedCases = null;
        
        
        for(List<JmlSpecificationCase> cases = tree.cases; cases.nonEmpty(); cases = cases.tail ){
            
            //TODO - it's possible no cases will be feasible -- make sure 
            // to add some code to handle this edge case.
            
            if(cases.head == null || cases.head.clauses==null || cases.head.clauses.head==null){
                continue;
            }
            
            if(cases.head.clauses.head instanceof JmlMethodClauseExpr){
                if(isUseful(cases.head.clauses)){
                    if(replacedCases == null){
                        replacedCases = List.of(cases.head);
                    }else{
                        replacedCases = replacedCases.append(cases.head);
                    }
                }
            }else if(cases.head.clauses.head instanceof JmlMethodClauseGroup){
                if(PropsInSubtree.viable(cases.head)){
                    if(replacedCases == null){
                        replacedCases = List.of(cases.head);
                    }else{
                        replacedCases = replacedCases.append(cases.head);
                    }
                }
            }else{
                scan(cases.head.clauses.head);
                
                if(replacedCases == null){
                    replacedCases = List.of(cases.head);
                }else{
                    replacedCases = replacedCases.append(cases.head);
                }
            }
            
       }
       tree.cases = replacedCases;
    }
    
    public static void simplify(JCTree node){
        instance.scan(node);
    }
    
    public static void simplify(JCTree node, JmlMethodDecl method){
        instance.currentMethod = method;
        RemoveImpossibleSpecificationCases.simplify(node);
    }
    
}
