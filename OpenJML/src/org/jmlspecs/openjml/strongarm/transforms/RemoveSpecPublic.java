package org.jmlspecs.openjml.strongarm.transforms;

import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.ext.OptionsInfer;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.ext.MethodExprClauseExtensions;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.requiresClauseKind;
import static org.jmlspecs.openjml.ext.RecommendsClause.*;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCPrimitiveTypeTree;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import javax.lang.model.type.TypeKind;

public class RemoveSpecPublic extends JmlTreeScanner {

    public static RemoveSpecPublic instance;
    
    final protected Log                    log;
    final protected Utils                  utils;
    final protected JmlTreeUtils           treeutils;
    final protected JmlTree.Maker          M;
    final protected Context                context;
    final Symtab syms;
    public static boolean inferdebug = false; 
    public static boolean verbose = false; 
    private AttributeMethod attr;
    
    public Set<JCIdent> idDone = new HashSet<JCIdent>();
    
    public RemoveSpecPublic(Context context){
        
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
    
    public static void cache(Context context){
        if(instance==null){
            instance = new RemoveSpecPublic(context);
        }
    }
    
    private boolean remove(JmlMethodClause clause, JCBinary tree){
        
        if(tree.lhs instanceof JCFieldAccess){
            JCFieldAccess fa = (JCFieldAccess)tree.lhs;
        
            if(clause.clauseKind==requiresClauseKind && fa.toString().contains("null")){
                return true;
            }
        }
        
        return false;
    }
    private boolean remove(JmlMethodClause clause, JCUnary tree){
        return remove(clause, tree.arg);
    }
    
    private boolean remove(JmlMethodClause clause, JCExpression expr){
        
        if(expr instanceof JCBinary){
            return remove(clause, (JCBinary)expr);
            
        }else if(expr instanceof JCUnary){
            return remove(clause, (JCUnary)expr);                
        }
        
        return false;
    }
    public boolean shouldRemove(JmlMethodClause clause){
        
        if(clause instanceof JmlMethodClauseExpr){

            JmlMethodClauseExpr mExpr = (JmlMethodClauseExpr)clause;
            
            return remove(clause, mExpr.expression);
        }
        
        return false;
    }
    
    public void filterBlock(JmlSpecificationCase block){
        
        List<JmlMethodClause> replacedClauses = null;
        
        if(block.clauses==null){
            return;
        }
        
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
        // filter this block
        //
        
        filterBlock(tree);
       
        super.visitJmlSpecificationCase(tree);
    }
    
    
    
    public void scan(JCTree node) {        
        this.attr = attr;        
        super.scan(node);
    }
    
    
    public static void simplify(JmlMethodDecl methodDecl, JCTree contract){
        instance.scan(contract);
    }
}