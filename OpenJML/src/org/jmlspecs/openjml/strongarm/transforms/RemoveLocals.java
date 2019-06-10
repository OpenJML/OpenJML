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
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCPrimitiveTypeTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import javax.lang.model.type.TypeKind;

public class RemoveLocals extends JmlTreeScanner {

    public static RemoveLocals instance;
    
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
    
    public RemoveLocals(Context context){
        
        this.context    = context;
        this.log        = Log.instance(context);
        this.utils      = Utils.instance(context);
        this.treeutils  = JmlTreeUtils.instance(context);
        this.M          = JmlTree.Maker.instance(context);
        this.syms       = Symtab.instance(context);
        
        this.inferdebug = JmlOption.isOption(context, OptionsInfer.INFER_DEBUG);           

        this.verbose = inferdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
            || utils.jmlverbose >= Utils.JMLVERBOSE;
            
        AttributeMethod.cache(context);

    }
    
    public static void cache(Context context){
        if(instance==null){
            instance = new RemoveLocals(context);
        }
    }
    /**
     * Locals removed if they are a formal and primative OR if they are just local. Fields stay.  
     */
    public boolean shouldRemove(JmlMethodClause clause){
        
        if(clause instanceof JmlMethodClauseExpr){
            JmlMethodClauseExpr mExpr = (JmlMethodClauseExpr)clause;
            
            
            if(mExpr.expression instanceof JCIdent){
                if(verbose){
                    log.getWriter(WriterKind.NOTICE).println("[RemoveLocals] Will remove this clause because it has no effect. " + clause.toString());
                }
                
                return true;

            }
            
//            if(mExpr.expression.toString().contains("_JML___NEWOBJECT")){
//             
//                
//                if(verbose){
//                    log.getWriter(WriterKind.NOTICE).println("[RemoveLocals] Will remove this clause because it references \\fresh variables (which are not implemented). " + clause.toString());
//                }
//                
//                return true;
//
//            }

            if(mExpr.expression.toString().contains("null != null") || mExpr.expression.toString().contains("TRUE != null") || mExpr.expression.toString().contains("FALSE != null")){
                
                
                
                if(verbose){
                    log.getWriter(WriterKind.NOTICE).println("[RemoveLocals] Will remove this clause because it checks internal boolean properties. " + clause.toString());
                }
                
                return true;
            }
            
            
            if(mExpr.expression instanceof JCIdent){
                JCIdent ident = (JCIdent)mExpr.expression;
                
                if(ident.name.toString().startsWith(Strings.prePrefix)){ // TODO - this is NOT the right way to do this. 
                    if(verbose){
                        log.getWriter(WriterKind.NOTICE).println("[RemoveLocals] Will remove local precondition due to local variable rules: " + clause.toString());
                    }
                    return true; 
                }
                
                
                
            }
            //TODO: Add recursive expression handling. 
            
//            if(mExpr.expression instanceof JmlMethodClauseExpr){
//                return shouldRemove(mExpr.expression);
//            }
            
            if(mExpr.expression instanceof JCBinary && ((JCBinary)mExpr.expression).lhs instanceof JCIdent){
                
                JCIdent ident = (JCIdent)((JCBinary)mExpr.expression).lhs;

                if(attr.locals.contains(ident.name)){ 
                    if(verbose){
                        log.getWriter(WriterKind.NOTICE).println("[RemoveLocals] Will remove clause due to local variable rules: " + clause.toString());
                    }
                    return true;
                }
                
                if(ident.name.toString().startsWith("index_")){ // TODO - this is NOT the right way to do this.
                    if(verbose){
                        log.getWriter(WriterKind.NOTICE).println("[RemoveLocals] Will remove local index due to local variable rules: " + clause.toString());
                    }
                    return true; 
                }
               
                
                if(clause.clauseKind != requiresClauseKind && attr.formals.contains(ident.name) &&  ((JCBinary)mExpr.expression).lhs.type!=null && ((JCBinary)mExpr.expression).lhs.type.getKind() instanceof TypeKind){
                    if(verbose){
                        log.getWriter(WriterKind.NOTICE).println("[RemoveLocals] Will remove clause due to formal+primative variable rules: " + clause.toString());
                    }
                    return true;                    
                }
            }
        }
        
        return false;
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

        if (verbose) {
            log.getWriter(WriterKind.NOTICE).println("===========<ACTIVE LOCAL FILTERS>================");
            for(Name n : attr.locals){
                log.getWriter(WriterKind.NOTICE).println("Local Variable: " + n);
            }
            log.getWriter(WriterKind.NOTICE).println("===========</ACTIVE LOCAL FILTERS>================");
        }

        //
        // filter this block
        //
        
        filterBlock(tree);
       
        super.visitJmlSpecificationCase(tree);
    }
    
    
    
    public void scan(JCTree node, AttributeMethod attr) {        
        this.attr = attr;        
        super.scan(node);
    }
    
    
    public static void simplify(JmlMethodDecl methodDecl, JCTree contract){
        instance.scan(contract, AttributeMethod.attribute(methodDecl));
    }
}