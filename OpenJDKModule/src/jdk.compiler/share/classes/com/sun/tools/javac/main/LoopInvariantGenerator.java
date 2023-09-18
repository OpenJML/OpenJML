// Senior Design Spring Fall 2023 group work

package com.sun.tools.javac.main;

import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree;

class LoopAssertionFinder extends JmlTreeScanner {

    JmlForLoop detectedForLoop = null;
    JmlWhileLoop detectedWhileLoop = null;
    JmlStatementExpr detectedAssertion = null;
    boolean complete = false;

    @Override
    public void visitJmlForLoop(JmlForLoop tree) {
        detectedWhileLoop = null;
        detectedForLoop = tree;
        super.visitJmlForLoop(tree);
    }

    @Override
    public void visitJmlWhileLoop(JmlWhileLoop tree) {
        detectedForLoop = null;
        detectedWhileLoop = tree;
        super.visitJmlWhileLoop(tree);
    }

    @Override
    public void visitJmlStatementExpr(JmlStatementExpr tree) {
        if (tree.keyword.equals("assert")) {
            if (detectedForLoop != null || detectedWhileLoop != null) {
                detectedAssertion = tree;
            }
            // tree.expression can be traversed using a new visitor
            //System.out.println(tree.expression);
        } 
        super.visitJmlStatementExpr(tree);
    }
}

public class LoopInvariantGenerator {
    
    // this gets called between the flow and desugar stages
    public static void generateInvariant(Env<AttrContext> env) {
        JCTree tree = env.tree; // the AST


        // System.out.println(tree);

        LoopAssertionFinder lAssertionFinder = new LoopAssertionFinder();
        lAssertionFinder.scan(tree);
    }
}