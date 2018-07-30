package org.jmlspecs.openjml.strongarm.transforms;

import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.strongarm.translators.FeasibilityCheckerSMT;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCParens;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

public class PropsInSubtree extends JmlTreeScanner{

    private int props;
    private int ensures;
    private int assignable;
    private int requires;
    
    public PropsInSubtree(){}
    
    
    
    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {
        props++;
        
        if(tree.token==JmlTokenKind.ENSURES){
            ensures++;
        }
        
        if(tree.token==JmlTokenKind.ASSIGNABLE){
            assignable++;
        }
        
        if(tree.token==JmlTokenKind.REQUIRES){
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