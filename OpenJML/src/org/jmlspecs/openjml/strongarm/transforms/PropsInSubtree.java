package org.jmlspecs.openjml.strongarm.transforms;

import static org.jmlspecs.openjml.ext.AssignableClauseExtension.assignableClause;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.ensuresClause;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.requiresClause;

import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTreeScanner;

import com.sun.tools.javac.tree.JCTree;

public class PropsInSubtree extends JmlTreeScanner{

    private int props;
    private int ensures;
    private int assignable;
    private int requires;
    
    public PropsInSubtree(){}
    
    
    
    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {
        props++;
        
        if(tree.clauseType==ensuresClause){
            ensures++;
        }
        
        if(tree.clauseType==assignableClause){
            assignable++;
        }
        
        if(tree.clauseType==requiresClause){
            requires++;
        }

        
        super.visitJmlMethodClauseExpr(tree);
    }



    public static int count(JCTree node){
        PropsInSubtree instance = new PropsInSubtree();
        instance.scan(node);
        
        return instance.props;
    }
    
    
    public static boolean viable(JCTree node){
        PropsInSubtree instance = new PropsInSubtree();
        instance.scan(node);
        
        return instance.assignable + instance.ensures > 0;
    }
    
    public static boolean any(JCTree node){
        PropsInSubtree instance = new PropsInSubtree();
        instance.scan(node);
        
        return instance.assignable + instance.ensures + instance.requires > 0;
    }
}