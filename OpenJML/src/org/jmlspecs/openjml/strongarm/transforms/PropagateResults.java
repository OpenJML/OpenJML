package org.jmlspecs.openjml.strongarm.transforms;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;


import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;

public class PropagateResults extends JmlTreeScanner {
    
    final protected Log                    log;
    final protected Utils                  utils;
    final protected JmlTreeUtils           treeutils;
    final protected JmlTree.Maker          M;
    final protected Context                context;
    final Symtab syms;
    public static boolean inferdebug = false; 
    public static boolean verbose = false; 
    public ArrayList<JCTree> subs = new ArrayList<JCTree>();
    
    public Set<JCIdent> idDone = new HashSet<JCIdent>();
    
    public PropagateResults(Context context){
        
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
    
    public boolean shouldConvert(JmlMethodClause clause){
        if(clause instanceof JmlMethodClauseExpr){
            JmlMethodClauseExpr mExpr = (JmlMethodClauseExpr)clause;
            
            if(mExpr.clauseKind == ensuresClauseKind && mExpr.expression instanceof JCBinary ){
                JCBinary expr = (JCBinary)mExpr.expression;

                if(expr == null || expr.lhs == null || expr.rhs==null){
                    return false;
                }
                
                if(expr.lhs.toString().equals("\\result") 
                        && expr.rhs.toString().startsWith(Strings.newObjectVarString)
                        
                        ){
                    
                    if(verbose){
                        log.getWriter(WriterKind.NOTICE).println("[PropagateResults] Will convert the clause " + clause.toString());
                    }
                    
                    return true;
                }
            }
        }
        
        return false;
    }
    
    /**
     * Locals removed if they are a formal and primative OR if they are just local. Fields stay.  
     */
    public boolean shouldRemove(JmlMethodClause clause){
        
        if(clause instanceof JmlMethodClauseExpr){
            JmlMethodClauseExpr mExpr = (JmlMethodClauseExpr)clause;
            
            if(mExpr.clauseKind == ensuresClauseKind && mExpr.expression instanceof JCBinary ){
                JCBinary expr = (JCBinary)mExpr.expression;
                
                if(expr == null || expr.lhs == null || expr.rhs==null){
                    return true;
                }
                
                if(expr.lhs.toString().equals("\\result") 
                        && (expr.rhs.toString().startsWith(Strings.newObjectVarString)
                        || expr.rhs.toString().startsWith(Strings.newArrayVarString))
                        ){
                    
                    if(verbose){
                        log.getWriter(WriterKind.NOTICE).println("[PropagateResults] Will remove the clause " + clause.toString());
                    }
                    
                    // add this expression!
                    return true;
                    
                }
                
                
                
                if(expr.rhs.toString().contains(Strings.newObjectVarString)
                   || expr.rhs.toString().contains(Strings.newArrayVarString)
                  ){
                    
                    if(verbose){
                        log.getWriter(WriterKind.NOTICE).println("[PropagateResults] Will remove the clause " + clause.toString());
                    }
                    
                    // add this expression!
                    return true;
                    
                }
                
            }
        }
        
        return false;
    }
    
    public JmlMethodClause convert(JmlMethodClause clause){
        
        if(clause instanceof JmlMethodClauseExpr){
            JmlMethodClauseExpr mExpr = (JmlMethodClauseExpr)clause;
            
            mExpr.expression = treeutils.makeIdent(0, "\\fresh(\\result)", syms.objectType);
            
            
        }
        return clause;
    }
    
    public void filterBlock(JmlSpecificationCase block){
        
        List<JmlMethodClause> replacedClauses = null;
        
        if(block.clauses==null){
            return;
            
        }
        for(List<JmlMethodClause> clauses = block.clauses; clauses.nonEmpty(); clauses = clauses.tail){
            if(shouldConvert(clauses.head)){               
            
                if(replacedClauses == null){
                    replacedClauses = List.of(convert(clauses.head));
                }else{
                    replacedClauses = replacedClauses.append(convert(clauses.head));
                }
            
            }else if(shouldRemove(clauses.head) == false){
                if(replacedClauses == null){
                    replacedClauses = List.of(clauses.head);
                }else{
                    replacedClauses = replacedClauses.append(clauses.head);
                }
            }else{
               
                JCBinary expr = (JCBinary)((JmlMethodClauseExpr)clauses.head).expression;
                // remove the clause and add it to the list.
                
                JCBinary newSub = treeutils.makeBinary(0, JCTree.Tag.EQ, expr.rhs, expr.lhs);
                
                if(verbose){
                    log.getWriter(WriterKind.NOTICE).println("[PropagateResults] Adding the substitution " + newSub.toString());
                }
                
                subs.add(newSub);
            }
        }
        
        block.clauses = replacedClauses;
    }

    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase tree) {

        filterBlock(tree);
       
        super.visitJmlSpecificationCase(tree);
    }
    
    
    public ArrayList<JCTree> getMappings(){
        return subs;
    }
    
    public void scan(JCTree node) {        
        super.scan(node);
    }
    
    public static ArrayList<JCTree> simplify(Context c, JCTree node){
        
        PropagateResults analysis = new PropagateResults(c);        
        
        analysis.scan(node);        
        
        return analysis.getMappings();
    }
    
    
}
