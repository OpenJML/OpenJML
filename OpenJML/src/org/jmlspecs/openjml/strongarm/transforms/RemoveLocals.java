package org.jmlspecs.openjml.strongarm.transforms;

import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

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
        
        this.inferdebug = JmlOption.isOption(context, JmlOption.INFER_DEBUG);           

        this.verbose = inferdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
            || utils.jmlverbose >= Utils.JMLVERBOSE;
            
        AttributeMethod.cache(context);

    }
    
    public static void cache(Context context){
        if(instance==null){
            instance = new RemoveLocals(context);
        }
    }
    
    public boolean shouldRemove(JmlMethodClause clause){
        
        if(clause instanceof JmlMethodClauseExpr){
            JmlMethodClauseExpr mExpr = (JmlMethodClauseExpr)clause;
            
            if(mExpr.expression instanceof JCBinary && ((JCBinary)mExpr.expression).lhs instanceof JCIdent){
                
                JCIdent ident = (JCIdent)((JCBinary)mExpr.expression).lhs;
                
                if(attr.locals.contains(ident.name)){ 
                
                    log.noticeWriter.println("[RemoveLocals] Will remove clause due to local variable rules: " + clause.toString());

                    
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
            log.noticeWriter.println("===========<ACTIVE LOCAL FILTERS>================");
            for(Name n : attr.locals){
                log.noticeWriter.println("Local Variable: " + n);
            }
            log.noticeWriter.println("===========</ACTIVE LOCAL FILTERS>================");
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