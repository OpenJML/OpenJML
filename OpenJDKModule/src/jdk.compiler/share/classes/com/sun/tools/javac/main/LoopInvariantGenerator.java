// Senior Design Spring Fall 2023 group work

package com.sun.tools.javac.main;

import org.jmlspecs.openjml.visitors.IJmlVisitor;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.tree.TreeScanner;

class LoopAssertionFinder extends JmlTreeScanner {

    JmlForLoop detectedForLoop = null;
    JmlWhileLoop detectedWhileLoop = null;
    JmlStatementExpr detectedAssertion = null;
    boolean complete = false;

    @Override
    public void visitJmlForLoop(JmlForLoop tree) {
        if (!complete) {
            detectedWhileLoop = null;
            detectedForLoop = tree;
        }
        super.visitJmlForLoop(tree);
    }

    @Override
    public void visitJmlWhileLoop(JmlWhileLoop tree) {
        if (!complete) {
            detectedForLoop = null;
            detectedWhileLoop = tree;
        }
        super.visitJmlWhileLoop(tree);
    }

    @Override
    public void visitJmlStatementExpr(JmlStatementExpr tree) {
        if (tree.keyword.equals("assert")) {
            if (!complete && (detectedForLoop != null || detectedWhileLoop != null)) {
                detectedAssertion = tree;
                complete = true;
            }
            // tree.expression can be traversed using a new visitor
            // System.out.println(tree.expression);
        }
        super.visitJmlStatementExpr(tree);
    }
}

class AssertionReader extends TreeScanner implements IJmlVisitor {
    @Override
    public void scan(JCTree tree) {
        if (tree != null) {
            if (tree instanceof JmlQuantifiedExpr) {
                JmlQuantifiedExpr temp = (JmlQuantifiedExpr) tree;
                // Print the tree and its class
                System.out.println(temp + " : " + temp.getClass().getSimpleName() + " Type=" + temp.kind);
            } else {
                System.out.println(tree + " : " + tree.getClass().getSimpleName());
            }
        }
        super.scan(tree);
    }

    @Override
    public void visitTree(JCTree tree) {
        // Generic visit for any trees not specially handled
        if (tree != null) {
            super.scan(tree);
        }
    }

    @Override
    // Covers expressions such as arr.length
    // "Selects through packages and classes"
    public void visitSelect(JCFieldAccess tree) {
        System.out.printf("FieldAccess: name=%s selected=%s sym=%s\n", tree.name, tree.selected, tree.sym);

        String selectedString = tree.selected.toString();
        String nameString = tree.name.toString();
        if ((selectedString.equals("arr") || selectedString.equals("a")) &&
                (nameString.equals("length") || nameString.equals("size"))) {
                    System.out.println("Possible array length expression: " + tree);
        }

        super.visitSelect(tree);
    }
}

public class LoopInvariantGenerator {

    private Context context;

    public LoopInvariantGenerator(Context context) {
        this.context = context;
    }

    // this gets called between the flow and desugar stages
    public void generateInvariant(Env<AttrContext> env) {
        JCTree tree = env.tree; // the AST

        // System.out.println(tree);

        LoopAssertionFinder lAssertionFinder = new LoopAssertionFinder();
        lAssertionFinder.scan(tree);

        if (!lAssertionFinder.complete) {
            return;
        }

        AssertionReader assertionReader = new AssertionReader();
        assertionReader.scan(lAssertionFinder.detectedAssertion.expression);

        // System.out.println(lAssertionFinder.detectedForLoop);
        // System.out.println(lAssertionFinder.detectedWhileLoop);
        // System.out.println(lAssertionFinder.detectedAssertion);
        // System.out.println(lAssertionFinder.complete);
    }
}