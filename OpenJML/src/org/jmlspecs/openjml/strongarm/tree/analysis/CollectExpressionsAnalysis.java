package org.jmlspecs.openjml.strongarm.tree.analysis;

import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.DefaultJmlTokenKind;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.strongarm.Strongarm;
import org.jmlspecs.openjml.strongarm.tree.PropTreeScanner;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log.WriterKind;

public class CollectExpressionsAnalysis extends JmlTreeAnalysis {

    private Set<JCTree> exprs = new HashSet<JCTree>();
    private final JmlTokenKind kind;
    
    public CollectExpressionsAnalysis(Context context, JmlTokenKind kind) {
        super(context);
        
        this.kind = kind;
    }
    
    @Override
    public void scan(JCTree node) {
        super.scan(node);
    }

    
    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {
        
        if(tree.token == kind){
            exprs.add(tree);
        }
        
        super.visitJmlMethodClauseExpr(tree);
    }

    
    public static Set<JCTree> analyze(JCTree tree){
        
        CollectExpressionsAnalysis analysis = new CollectExpressionsAnalysis(Strongarm._context, DefaultJmlTokenKind.REQUIRES);
        
        
        analysis.scan(tree);
        
        return analysis.exprs;
        
    }


    public static Set<JCTree> analyze(JCTree tree, Context ctx, JmlTokenKind kind){
        
        CollectExpressionsAnalysis analysis = new CollectExpressionsAnalysis(ctx, kind);
        
        
        analysis.scan(tree);
        
        return analysis.exprs;
        
    }
}
