// Senior Design Spring Fall 2023 group work

package com.sun.tools.javac.main;

import org.jmlspecs.openjml.visitors.IJmlVisitor;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import java.util.ArrayList;

import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
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

    private ArrayList lhsNameList;

    public AssertionReader(ArrayList lhsNameList) {
        this.lhsNameList = lhsNameList;
    }

    public void visitIdent(JCIdent that) {
        if (!lhsNameList.contains(that.toString())) {
            System.out.println("Constant found, maybe: " + that);
        }
    }

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
}

// Collects variables being assigned to. Doesn't cover unaries like i++
class AssignmentLhsCollector extends TreeScanner implements IJmlVisitor {
    public ArrayList lhsNameList = new ArrayList<>();

    @Override
    public void visitAssign(JCAssign that) {
        lhsNameList.add(that.lhs.toString());
        super.visitAssign(that);
    }

    @Override
    public void visitAssignop(JCAssignOp that) {
        lhsNameList.add(that.lhs.toString());
        super.visitAssignop(that);
    }
}

public class LoopInvariantGenerator {

    // this gets called between the flow and desugar stages
    public static void generateInvariant(Env<AttrContext> env) {
        JCTree tree = env.tree; // the AST

        // System.out.println(tree);

        LoopAssertionFinder lAssertionFinder = new LoopAssertionFinder();
        lAssertionFinder.scan(tree);

        if (!lAssertionFinder.complete) {
            return;
        }

        AssignmentLhsCollector assignmentLhsCollector = new AssignmentLhsCollector();
        if (lAssertionFinder.detectedWhileLoop != null) {
            assignmentLhsCollector.scan(lAssertionFinder.detectedWhileLoop);
        } else {
            assignmentLhsCollector.scan(lAssertionFinder.detectedForLoop);
        }

        AssertionReader assertionReader = new AssertionReader(assignmentLhsCollector.lhsNameList);
        assertionReader.scan(lAssertionFinder.detectedAssertion.expression);

        

        //System.out.println(lAssertionFinder.detectedForLoop);
        //System.out.println(lAssertionFinder.detectedWhileLoop);
        //System.out.println(lAssertionFinder.detectedAssertion);
        //System.out.println(lAssertionFinder.complete);
    }
}