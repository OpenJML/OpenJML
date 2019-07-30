package org.jmlspecs.openjml.strongarm.transforms;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import javax.lang.model.type.TypeKind;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
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
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;

public class SimplicyViaInternalSubstitutions extends JmlTreeScanner {

    public static SimplicyViaInternalSubstitutions instance;
    
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
    
    public SimplicyViaInternalSubstitutions(Context context){
        
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
            instance = new SimplicyViaInternalSubstitutions(context);
        }
    }

    public boolean shouldUse(JmlMethodClause clause){
        
        if(clause instanceof JmlMethodClauseExpr){
            JmlMethodClauseExpr mExpr = (JmlMethodClauseExpr)clause;
            
            if(mExpr.expression instanceof JCBinary && ((JCBinary)mExpr.expression).operator.toString().startsWith("==") &&  ((JCBinary)mExpr.expression).lhs instanceof JCIdent &&  ((JCBinary)mExpr.expression).rhs instanceof JCIdent){
                
                JCIdent rident = (JCIdent)((JCBinary)mExpr.expression).rhs;
                JCIdent lident = (JCIdent)((JCBinary)mExpr.expression).lhs;

                if(attr.locals.contains(rident.name) && !attr.locals.contains(lident.name)){
                    if(verbose){
                        log.getWriter(WriterKind.NOTICE).println("[SimplicityViaInternalSubstitutions] Found a clause with locals... " + clause.toString());
                    }
                    return true;
                }
            }
        }        
        return false;
    }
    
    public JCTree toReverseSub(JmlMethodClause clause){
        if(clause instanceof JmlMethodClauseExpr){
            JmlMethodClauseExpr mExpr = (JmlMethodClauseExpr)clause;
            
            if(mExpr.expression instanceof JCBinary && ((JCBinary)mExpr.expression).lhs instanceof JCIdent){                
                JCBinary e = (JCBinary)mExpr.expression;
                return treeutils.makeBinary(0, JCTree.Tag.EQ, e.rhs, e.lhs);
            }
        }
        return null; // will get skipped. 
    }
    
    public ArrayList<JCTree> extractSubstitutions(JmlSpecificationCase block){
        
        List<JmlMethodClause> replacedClauses = null;

        ArrayList<JCTree> subs = new ArrayList<JCTree>();
        
        //
        // Anytime we decide to use a clause we have to pull it out.  
        //
        if(block==null || block.clauses==null){
            return subs;
        }
        
        for(List<JmlMethodClause> clauses = block.clauses; clauses.nonEmpty(); clauses = clauses.tail){
                        
            if(shouldUse(clauses.head) == true){
                
                JCTree t = toReverseSub(clauses.head);
                
                if(t!=null){
                    subs.add(t);
                    
                    if(verbose){
                        log.getWriter(WriterKind.NOTICE).println("[SimplicityViaInternalSubstitutions] Translated " + clauses.head + " -> " + t);
                    }
                }else{
                    if(verbose){
                        log.getWriter(WriterKind.NOTICE).println("[SimplicityViaInternalSubstitutions] Strangely didn't find a substitution for clause: " + clauses.head);
                    }
                }
            }else{
                if(replacedClauses == null){
                    replacedClauses = List.of(clauses.head);
                }else{
                    replacedClauses = replacedClauses.append(clauses.head);
                }

            }
        }
        
        block.clauses = replacedClauses;
        
        return subs;
    }

    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase tree) {



        //
        // Make a list of things we could possibly substitute. 
        //
        ArrayList<JCTree> subs = extractSubstitutions(tree);
        
        // make the replacements
        
        if(subs!=null && subs.size() > 0){
            
            if (verbose) {
                log.getWriter(WriterKind.NOTICE).println("[SimplicyViaInternalSubstitutions] Found some substitutions to replace: " + subs.size());
            }


            for(List<JmlMethodClause> clauses = tree.clauses; clauses.nonEmpty(); clauses = clauses.tail){

                JCExpression e = null;
    
                String pre = clauses.head.toString();
                
                for(JCTree sub : subs){
                    
                    if(verbose){
                        log.getWriter(WriterKind.NOTICE).println("Trying: " + sub.toString());
                    }
                    
                    JCExpression tmpE;
                    
                     if(e!=null){
                         tmpE = SubstituteTree.replace(sub, e);
                     }else{
                         tmpE = SubstituteTree.replace(sub,  clauses.head);
                     }
                     
                     if(tmpE!=null){
                         e = tmpE;
                     }
                     
                 }
                
                String post = clauses.head.toString();
                
                // make sure this is an ENSURES clause
                if(pre.equals(post)==false){
                    clauses.head.clauseKind = MethodExprClauseExtensions.ensuresClauseKind;
                }
                
            }
        }
       
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
