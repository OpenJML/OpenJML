// Senior Design Spring Fall 2023 group work

package com.sun.tools.javac.main;

import org.jmlspecs.openjml.visitors.IJmlVisitor;
import org.jmlspecs.openjml.visitors.JmlTreeCopier;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.jmlspecs.openjml.visitors.JmlTreeTranslator;
import org.jmlspecs.openjml.ext.StatementExprExtensions;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.source.tree.Tree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.tree.TreeScanner;

import java.util.HashSet;

/*
 * This visitor looks for a loop and assertion together (assertion after the loop).
 * If a pair is found, the boolean variable complete is marked as true and the loop invariant is genrated
 * based on the assertion.
 */
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
        }
        super.visitJmlStatementExpr(tree);
    }
}

/*
 * This visitor goes through the postcondition to look for variables to replace.
 * It also goes through the loop parameters to find replacement variables;
 * Potential variables (numeric, integer values) are placed into the possible_vars list.
 */
class AssertionReader extends TreeScanner implements IJmlVisitor {
    public HashSetWrapper possible_vars;
    private boolean loop_params = false;

    public AssertionReader() {
        possible_vars = new HashSetWrapper();
    }

    public AssertionReader(boolean loop_params) {
        possible_vars = new HashSetWrapper();
        this.loop_params = true;
    }

    /* 
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
    */

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
        if (this.loop_params) return;
        //System.out.printf("FieldAccess: name=%s selected=%s sym=%s\n", tree.name, tree.selected, tree.sym);
        String selectedString = tree.selected.toString();
        String nameString = tree.name.toString();
        if ((selectedString.equals("arr") || selectedString.equals("a")) &&
                (nameString.equals("length") || nameString.equals("size"))) {
            if (replaceable(tree.sym.type.getTag())) {
                possible_vars.add(tree);
            }
            //System.out.println("Possible array length expression: " + tree);
        }

        super.visitSelect(tree);
    }

    @Override
    public void visitLiteral(JCLiteral tree) {
        if (!replaceable(tree.typetag)) return;
        possible_vars.add(tree);
    }

    @Override
    public void visitIdent(JCIdent tree) {
        if (!replaceable(tree.sym.type.getTag())) return;
        possible_vars.add(tree);
    }
    
    private boolean replaceable(TypeTag tag) {
        return tag == TypeTag.BYTE || tag == TypeTag.SHORT || tag == TypeTag.INT || tag == TypeTag.LONG;
    }
}

/*
 * This object performs the replacement.
 * WORK IN PROGRESS
 */
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
    LoopAssertionFinder lAssertionFinder = new LoopAssertionFinder(); // used to find the loop and assertion pair
    AssertionReader assertionReader = new AssertionReader(); // used to read the assertion
    AssertionReader loopParamsReader = new AssertionReader(true); // used to read the loop parameters

    public LoopInvariantGenerator(Context context) {
        this.context = context;
        this.make = Maker.instance(context);
        this.constantReplacer = new ConstantReplacer(context);
        this.copier = new JmlTreeCopier(context, this.make);
    }

    // this gets called between the flow and desugar stages
    public void generateInvariant(Env<AttrContext> env) {
        JCTree tree = env.tree; // the AST

        lAssertionFinder.scan(tree); // find the loop + assertion

        // if a loop + assertion is not found, nothing happens
        if (!lAssertionFinder.complete) {
            return;
        }

        // This block of code reads the parameters of the loop to obtain possible replacement variables
        if (lAssertionFinder.detectedForLoop == null) {
            this.loopParamsReader.scan(lAssertionFinder.detectedWhileLoop.cond); // while loop condition
        } else {
            // for loop initialization
            if (lAssertionFinder.detectedForLoop.init != null) {
                for (JCStatement temp : lAssertionFinder.detectedForLoop.init) {
                    this.loopParamsReader.scan(temp);
                }
            }

            this.loopParamsReader.scan(lAssertionFinder.detectedForLoop.cond); // for loop condition 

            // for loop post-iteration operation
            if (lAssertionFinder.detectedForLoop.step != null) {
                for (JCExpressionStatement temp : lAssertionFinder.detectedForLoop.step) {
                    this.loopParamsReader.scan(temp);
                }
            }
        }

        System.out.println("Possible replacement variables: " + loopParamsReader.possible_vars.variables);

        assertionReader.scan(lAssertionFinder.detectedAssertion.expression); // read the assertion and store the possible variables to be replaced
        System.out.println("Possible variables to be replaced: " + assertionReader.possible_vars.variables);

        // make new invariant using the postcondition
        JmlStatementLoopExpr invariant = this.make.JmlStatementLoopExpr(
                StatementExprExtensions.loopinvariantClause,
                copier.copy(lAssertionFinder.detectedAssertion.expression));

        //this.make.JmlChained(null) // make the bounds for the replacement variable

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

/*
 * The hash code for two trees might be different despite representing the same identifier.
 * This HashSetWrapper puts the trees in the set if the string representation of the tree is unique.
 */
class HashSetWrapper {
    public HashSet<Tree> variables = new HashSet<>();
    private HashSet<String> duplicates = new HashSet<>();

    public void add(Tree tree) {
        if (!duplicates.contains(tree.toString())) {
            variables.add(tree);
            duplicates.add(tree.toString());
        }
    }

    public boolean contains(Tree tree) {
        return duplicates.contains(tree.toString());
    }
}