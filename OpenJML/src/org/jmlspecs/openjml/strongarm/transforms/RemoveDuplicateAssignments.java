package org.jmlspecs.openjml.strongarm.transforms;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import javax.lang.model.type.TypeKind;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.strongarm.JDKListUtils;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
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

public class RemoveDuplicateAssignments extends JmlTreeScanner {

    public static RemoveDuplicateAssignments instance;
    
    final protected Log                    log;
    final protected Utils                  utils;
    final protected JmlTreeUtils           treeutils;
    final protected JmlTree.Maker          M;
    final protected Context                context;
    final Symtab syms;
    public static boolean inferdebug = false; 
    public static boolean verbose = false; 
        
    public RemoveDuplicateAssignments(Context context){
        
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
            instance = new RemoveDuplicateAssignments(context);
        }
    }
    /* Type t = lhs.type;
        if (t.isPrimitive() && TypeTags.INT > t.tag) t = syms.intType;
        tree.operator = findOpSymbol(JCTree.EQ, t);*/
    public boolean shouldRemove(JmlMethodClause clause, List<JmlMethodClause> clauses){
        
        if(clause instanceof JmlMethodClauseExpr == false) return false;
        
        JmlMethodClauseExpr mExpr = (JmlMethodClauseExpr)clause;
        
        // see if it's an assignment statement. 
        if(mExpr.expression instanceof JCBinary && ((JCBinary)mExpr.expression).lhs !=null && ((JCBinary)mExpr.expression).operator.toString().startsWith("==")){

            
            String ident = ((JCBinary)mExpr.expression).lhs.toString();
            
            for(; clauses.nonEmpty(); clauses = clauses.tail){
                
                if(clauses.head instanceof JmlMethodClauseExpr){
                    JmlMethodClauseExpr mExpr2 = (JmlMethodClauseExpr)clauses.head;
                    
                    if(mExpr2.expression instanceof JCBinary && ((JCBinary)mExpr2.expression).operator.toString().startsWith("==")){

                        if(((JCBinary)mExpr2.expression).lhs==null){
                            return true;
                        }
                        
                        String ident2 = ((JCBinary)mExpr2.expression).lhs.toString();
                        
                        if(ident.equals(ident2)){
                            if(verbose){
                                log.getWriter(WriterKind.NOTICE).println("[RemoveDuplicateAssignments] Will remove clause since it will be reassigned: " + clause.toString());
                            }
                            return true;
                        }
                    }                    
                }
                            
            }
        }
        
        return false;
    }
    
    public boolean appearsTwice(JmlMethodClause clause, List<JmlMethodClause> clauses){
        return JDKListUtils.contains(clauses, clause, new ClauseEquals());
    }
      
    
    class ClauseEquals implements Comparator<JmlMethodClause>{

        @Override
        public int compare(JmlMethodClause o1, JmlMethodClause o2) {
            return o1.toString().compareTo(o2.toString());
        }
        
    }
    
    public void filterBlock(JmlSpecificationCase block){
        
        List<JmlMethodClause> replacedClauses = null;
        
        if(block.clauses==null) return;
        
        for(List<JmlMethodClause> clauses = block.clauses; clauses.nonEmpty(); clauses = clauses.tail){
                        
            if(shouldRemove(clauses.head, clauses.tail) == false && appearsTwice(clauses.head, clauses.tail) == false){
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
        filterBlock(tree);
       
        super.visitJmlSpecificationCase(tree);
    }
    

    public void scan(JCTree node) {              
        super.scan(node);
    }
    
    
    public static void simplify(JCTree contract){
        instance.scan(contract);
    }
}
