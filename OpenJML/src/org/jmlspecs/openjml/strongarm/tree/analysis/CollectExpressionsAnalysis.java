package org.jmlspecs.openjml.strongarm.tree.analysis;

import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.ext.MethodExprClauseExtensions;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;
import static org.jmlspecs.openjml.ext.RecommendsClause.*;
import org.jmlspecs.openjml.strongarm.Strongarm;
import org.jmlspecs.openjml.strongarm.tree.PropTreeScanner;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log.WriterKind;

public class CollectExpressionsAnalysis extends JmlTreeAnalysis {

    private Set<JCTree> exprs = new HashSet<JCTree>();
    private final IJmlClauseKind clauseType;
    
    public CollectExpressionsAnalysis(Context context, IJmlClauseKind clauseType) {
        super(context);
        
        this.clauseType = clauseType;
    }
    
    @Override
    public void scan(JCTree node) {
        super.scan(node);
    }

    
    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {
        
        if(tree.clauseKind == clauseType){
            exprs.add(tree);
        }
        
        super.visitJmlMethodClauseExpr(tree);
    }

    
    public static Set<JCTree> analyze(JCTree tree){
        
        CollectExpressionsAnalysis analysis = new CollectExpressionsAnalysis(Strongarm._context, requiresClauseKind);
        
        
        analysis.scan(tree);
        
        return analysis.exprs;
        
    }


    public static Set<JCTree> analyze(JCTree tree, Context ctx, IJmlClauseKind clauseType){
        
        CollectExpressionsAnalysis analysis = new CollectExpressionsAnalysis(ctx, clauseType);
        
        
        analysis.scan(tree);
        
        return analysis.exprs;
        
    }
}
