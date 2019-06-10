package org.jmlspecs.openjml.strongarm.transforms;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.ext.MethodExprClauseExtensions;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.requiresClauseKind;
import static org.jmlspecs.openjml.ext.RecommendsClause.*;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;

/**
 * Transformer that removes duplicate preconditions from NESTED specification cases. 
 *   
 */
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
    
    // this is a mapping from the block where the filter was found to the filters...
    protected Map<JmlSpecificationCase,HashSet<JmlMethodClauseExpr>> activeFilters = new HashMap<JmlSpecificationCase,HashSet<JmlMethodClauseExpr>>();
    
    public RemoveDuplicatePreconditions(Context context){
        
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
            instance = new RemoveDuplicatePreconditions(context);
        }
    }

    private void addFilterAtBlock(JmlSpecificationCase block, JmlMethodClauseExpr filter){
        
        if(activeFilters.get(block)==null){
            activeFilters.put(block,  new HashSet<JmlMethodClauseExpr>());
        }
        
        activeFilters.get(block).add(filter);
    }
    
    private void removeFiltersForBlock(JmlSpecificationCase block){
        activeFilters.remove(block);
    }
    
    protected Set<String> getFilterStrings(){
        Set<String> filters = new HashSet<String>();
        
        for(HashSet<JmlMethodClauseExpr> blockExprs : activeFilters.values()){
            for(JmlMethodClauseExpr expr : blockExprs){
                filters.add(expr.toString());
            }
        }
        
        return filters;
    }
    
    protected Set<JmlMethodClauseExpr> getFilters(){
        Set<JmlMethodClauseExpr> filters = new HashSet<JmlMethodClauseExpr>();
        
        for(HashSet<JmlMethodClauseExpr> blockExprs : activeFilters.values()){
            for(JmlMethodClauseExpr expr : blockExprs){
                filters.add(expr);
            }
        }
        
        return filters;
    }
    
    @Override
    public void scan(JCTree node) {
        //if (node != null) System.out.println("Node: "+ node.toString() + "<CLZ>" + node.getClass());
        super.scan(node);
    }
    
    public void filterBlock(JmlSpecificationCase block){
        
        // we keep repeating this 
        List<JmlMethodClause> replacedClauses = null;
        Set<String> filterSet = getFilterStrings();
        
        if(block.clauses==null) return;
        
        for(List<JmlMethodClause> clauses = block.clauses; clauses.nonEmpty(); clauses = clauses.tail){
                        
            if(clauses.head.clauseKind != requiresClauseKind || filterSet.contains(clauses.head.toString())==false){
                if(replacedClauses == null){
                    replacedClauses = List.of(clauses.head);
                }else{
                    replacedClauses = replacedClauses.append(clauses.head);
                }
            }
            
        }
        
        block.clauses = replacedClauses;
    }


    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase tree) {

        if (verbose) {
            log.getWriter(WriterKind.NOTICE).println("===========<ACTIVE FILTERS>================");
            for(String s : getFilterStrings()){
                log.getWriter(WriterKind.NOTICE).print(s + " ");
            }
            log.getWriter(WriterKind.NOTICE).println("\n===========</ACTIVE FILTERS>================");
        }

        //
        // filter this block
        //
        
        filterBlock(tree);
       
        //
        // add new filters if we need them
        //
        if(tree.clauses!=null){
            for(List<JmlMethodClause> clauses = tree.clauses; clauses.nonEmpty(); clauses = clauses.tail){
    
                if(clauses.head instanceof JmlMethodClauseExpr == false){ continue; }
                
                JmlMethodClauseExpr clauseExpr = (JmlMethodClauseExpr)clauses.head;
                
                // we want to filter out all requires clauses. 
                if(clauseExpr.clauseKind == requiresClauseKind){
                    addFilterAtBlock(tree, clauseExpr);
                }
            }
            
            super.visitJmlSpecificationCase(tree);
    
            
            //
            // Pop the filters for this block off (if we exit the scope)
            //
            removeFiltersForBlock(tree);
        }
    }

    
    public static void simplify(JCTree node){
        instance.scan(node);
    }
}
