// Senior Design Spring Fall 2023 group work

package com.sun.tools.javac.main;

import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree;

class OurVisitor extends JmlTreeScanner {
    public OurVisitor() {
        super();
    }

    // methods we can override are in IJmlVisitor.java

    @Override
    // Covers a for loop along with its specifications (e.g. invariants)
    public void visitJmlForLoop(JmlForLoop tree) {
        System.out.println("Found a for loop!");
        System.out.println(tree);
        
        super.visitJmlForLoop(tree);
    }

    @Override
    // covers JML assert statements inside a method's body
    public void visitJmlStatementExpr(JmlStatementExpr tree) {
        if (tree.keyword.equals("assert")) {
            System.out.println("Found an assertion in a method's body!");
            System.out.println("\tfull statement: " + tree);
            System.out.println("\tjust the expression: " + tree.expression);
        }

        super.visitJmlStatementExpr(tree);
    }

    // override more stuff?
}

public class OurWork {
    
    // this gets called between the flow and desugar stages
    public static void doOurWork(Env<AttrContext> env) {
        JCTree tree = env.tree; // the AST

        // System.out.println(tree);

        OurVisitor ov = new OurVisitor();
        ov.scan(tree);
    }
}