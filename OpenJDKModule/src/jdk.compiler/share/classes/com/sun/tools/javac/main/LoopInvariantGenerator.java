// Senior Design Spring Fall 2023 group work

package com.sun.tools.javac.main;

import org.jmlspecs.openjml.visitors.IJmlVisitor;
import org.jmlspecs.openjml.visitors.JmlTreeCopier;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.jmlspecs.openjml.visitors.JmlTreeTranslator;
import org.jmlspecs.openjml.ext.StatementExprExtensions;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.source.tree.Tree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.tree.TreeScanner;

import java.util.ArrayList;

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
    public ArrayList<Tree> possible_vars;

    public AssertionReader() {
        possible_vars = new ArrayList<Tree>();
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
            possible_vars.add(tree);
            System.out.println("Possible array length expression: " + tree);
        }

        super.visitSelect(tree);
    }

    @Override
    public void visitLiteral(JCLiteral tree) {
        possible_vars.add(tree);
    }

    @Override
    public void visitIdent(JCIdent tree) {
        possible_vars.add(tree);
    }

    @Override
    public void visitJmlVariableDecl(JmlVariableDecl tree) {
        System.out.printf("Var Def Tree=%s\n", tree);
        possible_vars.add(tree);
    }          
}

class ConstantReplacer extends JmlTreeTranslator {
    Context context;
    Maker make;
    Symtab symtab;

    public ConstantReplacer(Context context) {
        this.context = context;
        this.make = Maker.instance(context);
        this.symtab = Symtab.instance(context);
    }

    @Override
    public void visitSelect(JCFieldAccess tree) {
        String nameString = tree.name.toString(); // in "arr.length", this would be "length"

        if (nameString.equals("length") || nameString.equals("size")) {
            result = makeVariableNode(tree); // current node will be replaced by 'result'
        } else {
            // If not a "array.length" node, don't change anything
            super.visitSelect(tree);
        }
    }

    private JCIdent makeVariableNode(JCFieldAccess tree) {
        JCIdent newIdent = make.Ident("fresh_variable");

        // ESC fails if we don't set a type and sym
        newIdent.setType(tree.type);
        newIdent.sym = new Symbol.VarSymbol(0, newIdent.getName(), symtab.intType, null);

        return newIdent;
    }
}

public class LoopInvariantGenerator {
    Context context;
    Maker make;
    ConstantReplacer constantReplacer;
    JmlTreeCopier copier;
    LoopAssertionFinder lAssertionFinder = new LoopAssertionFinder();
    AssertionReader assertionReader = new AssertionReader();

    public LoopInvariantGenerator(Context context) {
        this.context = context;
        this.make = Maker.instance(context);
        this.constantReplacer = new ConstantReplacer(context);
        this.copier = new JmlTreeCopier(context, this.make);
    }

    // this gets called between the flow and desugar stages
    public void generateInvariant(Env<AttrContext> env) {
        JCTree tree = env.tree; // the AST

        // System.out.println(tree);

        lAssertionFinder.scan(tree);

        if (!lAssertionFinder.complete) {
            return;
        }

        assertionReader.scan(lAssertionFinder.detectedAssertion.expression);
        System.out.println("Possible Variables: " + assertionReader.possible_vars);

        // make new invariant using the postcondition
        JmlStatementLoopExpr invariant = this.make.JmlStatementLoopExpr(
                StatementExprExtensions.loopinvariantClause,
                copier.copy(lAssertionFinder.detectedAssertion.expression));

        // modify the invariant's tree by replacing constants with variables
        invariant.accept(constantReplacer);

        IJmlLoop loop;
        List<JmlStatementLoop> specs = List.of(invariant);

        if (lAssertionFinder.detectedForLoop != null) {
            loop = lAssertionFinder.detectedForLoop;
            System.out.println("Before changing loop specs: ");
            System.out.println(loop);

            // attach our new invariants to the loop
            loop.setLoopSpecs(specs);

            System.out.println("After changing loop specs: ");
            System.out.println(loop);
        }

        // System.out.println(lAssertionFinder.detectedForLoop);
        // System.out.println(lAssertionFinder.detectedWhileLoop);
        // System.out.println(lAssertionFinder.detectedAssertion);
        // System.out.println(lAssertionFinder.complete);
    }
}