package org.jmlspecs.openjml.strongarm.transforms;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import javax.lang.model.type.TypeKind;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;

public class RemoveDeadAssignments extends JmlTreeScanner {

    public static RemoveDeadAssignments instance;
    
    final protected Log                    log;
    final protected Utils                  utils;
    final protected JmlTreeUtils           treeutils;
    final protected JmlTree.Maker          M;
    final protected Context                context;
    final Symtab syms;
    public static boolean inferdebug = false; 
    public static boolean verbose = false; 
    private Set<Name> mappings;
    
    public Set<JCIdent> idDone = new HashSet<JCIdent>();
    
    public RemoveDeadAssignments(Context context){
        
        this.context    = context;
        this.log        = Log.instance(context);
        this.utils      = Utils.instance(context);
        this.treeutils  = JmlTreeUtils.instance(context);
        this.M          = JmlTree.Maker.instance(context);
        this.syms       = Symtab.instance(context);
        
        this.inferdebug = JmlOption.isOption(context, org.jmlspecs.openjml.ext.OptionsInfer.INFER_DEBUG);           

        this.verbose = inferdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
            || utils.jmlverbose >= Utils.JMLVERBOSE;
            
        AttributeMethod.cache(context);

    }
    
    public static void cache(Context context){
        if(instance==null){
            instance = new RemoveDeadAssignments(context);
        }
    }
    /**
     * Remove things that don't have a mapping (meaning it is redundant) 
     */
    public boolean shouldRemove(JmlMethodClause clause){
        
        if(clause instanceof JmlMethodClauseExpr){
            JmlMethodClauseExpr mExpr = (JmlMethodClauseExpr)clause;
            
            if(mExpr.expression instanceof JCBinary && ((JCBinary)mExpr.expression).lhs instanceof JCIdent){
                
                JCIdent ident = (JCIdent)((JCBinary)mExpr.expression).lhs;
                
                if(mappings.contains(ident.name)==false){
                    if(verbose){
                        log.getWriter(WriterKind.NOTICE).println("[RemoveDeadAssignments] Will remove clause due to missing mapping rules: " + clause.toString());
                    }
                    return true;
                }
            }
        }
        
        return false;
    }
    
    
    public Name replace(JCTree p){
        
        if(p instanceof JCExpression){
            
            if(p instanceof JCBinary){
                JCBinary bProp = (JCBinary)p;
                if(bProp.lhs instanceof JCIdent){
                    return ((JCIdent)bProp.lhs).getName();
                }else{
                    return null; //((JCLiteral)bProp.lhs).getValue();
                }
                
            }else{
                //log.error("jml.internal", "Unexpected node: " + p.getClass() + " found during replacement.");
            }
            
        }else if(p instanceof JCVariableDecl){
            JCVariableDecl pVarDecl = (JCVariableDecl)p;
            return pVarDecl.getName();
        }
        
        //log.error("jml.internal", "LHS Missing in Replacement");

        
        return null;
    }

    
    
    public void filterBlock(JmlSpecificationCase block){
        
        List<JmlMethodClause> replacedClauses = null;
        
        for(List<JmlMethodClause> clauses = block.clauses; clauses.nonEmpty(); clauses = clauses.tail){
                        
            if(shouldRemove(clauses.head) == false){
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
//
        //
        // filter this block
        //
        
        
        filterBlock(tree);
       
        super.visitJmlSpecificationCase(tree);
    }
    

    //TODO -- this needs to be made better - right now it's a bit of a hack.... 
    public void scan(JCTree node, Map<JCIdent, ArrayList<JCTree>> mappings) {
        
        if (verbose) {
            log.getWriter(WriterKind.NOTICE).println("===========<ACTIVE DEAD FILTERS>================");
        }
        
        this.mappings = new HashSet<Name>();
        
        for(ArrayList<JCTree> v : mappings.values()){
            
            for(JCTree t : v){
                this.mappings.add(replace(t));
                if(verbose){
                    log.getWriter(WriterKind.NOTICE).println("Added EXPR: " + replace(t));
                }
            }
        }
    
        if (verbose) {
            log.getWriter(WriterKind.NOTICE).println("===========</ACTIVE DEAD FILTERS>================");
        }
        
        super.scan(node);
    }
    
    
    public static void simplify(Map<JCIdent, ArrayList<JCTree>> mappings, JCTree contract){
        instance.scan(contract, mappings);
    }
}
