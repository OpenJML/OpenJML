// Senior Design Spring Fall 2023 group work

package com.sun.tools.javac.main;

import org.jmlspecs.openjml.visitors.IJmlVisitor;
import org.jmlspecs.openjml.visitors.JmlTreeCopier;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.jmlspecs.openjml.visitors.JmlTreeTranslator;
import org.jmlspecs.openjml.ext.StatementExprExtensions;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.JmlEsc;

import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.source.tree.Tree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.tree.TreeScanner;

import java.io.OutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
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
        if (this.loop_params) return; // JCFIeldAccess will probably be a constant in the parameters of a loop

        //System.out.printf("FieldAccess: name=%s selected=%s sym=%s\n", tree.name, tree.selected, tree.sym);

        String nameString = tree.name.toString();
        
        if (Util.isArrayLength(tree) || nameString.equals("size")) {
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

    private Tree old_constant;
    private Tree new_variable;

    public ConstantReplacer(Context context) {
        this.context = context;
        this.make = Maker.instance(context);
        this.symtab = Symtab.instance(context);
    }

    public void setOldConstant(Tree constant) {
        this.old_constant = constant;
    }

    public void setNewVariable(Tree variable) {
        this.new_variable = variable;
    }

    public Tree getOldConstant() {
        return this.old_constant;
    }

    
    @Override
    public void visitSelect(JCFieldAccess tree) {
        if (tree.toString().equals(this.old_constant.toString())) {
            result = makeVariableNode(tree);
        } else {
            super.visitSelect(tree);
        }
    }
    

    @Override
    public void visitIdent(JCIdent tree) {
        if (tree.toString().equals(this.old_constant.toString())) {
            result = makeVariableNode(tree);
        } else {
            super.visitIdent(tree);
        }
    }

    @Override
    public void visitLiteral(JCLiteral tree) {
        if (tree.toString().equals(this.old_constant.toString())) {
            result = makeVariableNode(tree);
        } else {
            super.visitLiteral(tree);
        }
    }

    private JCIdent makeVariableNode(JCTree tree) {
        return (JCIdent) (((JCTree)this.new_variable).clone());
    }
}

public class LoopInvariantGenerator {
    Context context;
    Maker make;
    ConstantReplacer constantReplacer;
    JmlTreeCopier copier;
    TreeMaker treeMaker;
    Names name;
    Symtab symtab;
    JmlEsc esc;
    LoopAssertionFinder lAssertionFinder = new LoopAssertionFinder(); // used to find the loop and assertion pair
    AssertionReader assertionReader = new AssertionReader(); // used to read the assertion
    AssertionReader loopParamsReader = new AssertionReader(true); // used to read the loop parameters

    public LoopInvariantGenerator(Context context) {
        this.context = context;
        this.make = Maker.instance(context);
        this.constantReplacer = new ConstantReplacer(context);
        this.copier = new JmlTreeCopier(context, this.make);
        this.treeMaker = TreeMaker.instance(context);
        this.name = Names.instance(context);
        this.symtab = Symtab.instance(context);
        this.esc = JmlEsc.instance(context);
    }

    // this gets called between the flow and desugar stages
    public void generateInvariant(Env<AttrContext> env) {
        JCTree tree = env.tree; // the AST

        lAssertionFinder.scan(tree); // find the loop + assertion

        // if a loop + assertion is not found, nothing happens
        if (!lAssertionFinder.complete) {
            return;
        }

        IJmlLoop loop = null;

        // This block of code reads the parameters of the loop to obtain possible replacement variables
        if (lAssertionFinder.detectedForLoop == null) {
            loop = lAssertionFinder.detectedWhileLoop;
            this.loopParamsReader.scan(lAssertionFinder.detectedWhileLoop.cond); // while loop condition
        } else {
            loop = lAssertionFinder.detectedForLoop;
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

        assertionReader.scan(lAssertionFinder.detectedAssertion.expression); // read the assertion and store the possible constants to be replaced
        System.out.println("Possible constants to be replaced: " + assertionReader.possible_vars.variables);

        if (loopParamsReader.possible_vars.variables.size() == 0 ||
                assertionReader.possible_vars.variables.size() == 0) {
            return; // no constants to replace, or no variables to replace with
        }

        // Replace constant with variable, trying each constant/variable combination until one works
        OUTER:
        for (Tree constant : assertionReader.possible_vars.variables) {
            constantReplacer.setOldConstant(constant); 
       
            for (Tree variable : loopParamsReader.possible_vars.variables) {
                constantReplacer.setNewVariable(variable);

                JmlStatementLoopExpr boundary = this.make.JmlStatementLoopExpr(
                        StatementExprExtensions.loopinvariantClause,
                        getBoundaryExpression(loop, (JCIdent) variable, (JCExpression) constant));
             
                // make new invariant using the postcondition
                JmlStatementLoopExpr invariant = this.make.JmlStatementLoopExpr(
                        StatementExprExtensions.loopinvariantClause,
                        copier.copy(lAssertionFinder.detectedAssertion.expression));

                // modify the invariant's tree by replacing constants with variables
                invariant.accept(constantReplacer);
        
                if (lAssertionFinder.detectedForLoop != null) {
                    // attach our new invariants to the loop
                    loop.setLoopSpecs(List.of(boundary, invariant));
        
                    System.out.println("Generated specs: ");
                    List.of(boundary, invariant).forEach(spec -> System.out.println(spec));
                }
                
                boolean verified = getEscVerificationResult(tree);
                System.out.printf("Replaced constant %s with variable %s: %sverified\n", constant, variable, (verified ? "" : "not "));
    
                if (verified) {
                    break OUTER; // early exit
                }
            }
        }
        
        
        //System.out.println("\n\n\n\n" + JmlPretty.write(env.tree) + "\n\n\n\n\n");
        

        // System.out.println(lAssertionFinder.detectedForLoop);
        // System.out.println(lAssertionFinder.detectedWhileLoop);
        // System.out.println(lAssertionFinder.detectedAssertion);
        // System.out.println(lAssertionFinder.complete);
    }

    private boolean getEscVerificationResult(JCTree tree) {
        esc.initCounts();
        esc.check(tree); // TODO silence console output?
        return (esc.classes == esc.classesOK);
    }

    /*
     * Makes a boundary expression for a given variable.
     * lower bound is the variable's initial value if we can find it, otherwise 0.
     * upper bound is the constant that the variable is replacing.
     * 
     * Caveat: this assumes that the iteration variable is increasing
     */
    private JmlChained getBoundaryExpression(IJmlLoop loop, JCIdent variable, JCExpression constant) {
        JmlChained boundary_expression;

        // try to get the initial value from the for loop's initializer
        JCExpression initialValue = getInitialValueOfVar(variable, loop);
        
        JCBinary binary_1;
        if (initialValue != null) {
            binary_1 = treeMaker.Binary(JCTree.Tag.LE, initialValue, variable);
        } else {
            // couldn't find initial value, so assume it is 0
            JCLiteral zero = treeMaker.Literal(0).setType(symtab.intType);
            binary_1 = treeMaker.Binary(JCTree.Tag.LE, zero, variable);
        }
        binary_1.setType(symtab.booleanType);
        
        JCBinary binary_2 = treeMaker.Binary(JCTree.Tag.LE, (JCTree.JCIdent)variable, constant);
            
        binary_2.setType(symtab.booleanType);
        
        boundary_expression = this.make.JmlChained(List.of(binary_1, binary_2));
        boundary_expression.setType(symtab.booleanType);
        return boundary_expression;
    }

    /**
     * @return the variable's initialized value, if found. otherwise null
     */
    private JCExpression getInitialValueOfVar(JCIdent variable, IJmlLoop loop) {
        // only doing for loops for now. with while loops we must read earlier declarations/assignments
        if (loop instanceof JCForLoop) {
            JCForLoop forLoop = (JCForLoop) loop;
            for (JCStatement statement : forLoop.init) {
                if (statement instanceof JCVariableDecl) {
                    JCVariableDecl decl = (JCVariableDecl) statement;
                    if (decl.name.toString().equals(variable.name.toString())) {
                        return decl.init;
                    }
                }
            }
        }
        return null; // no initialized value found
    }
}

/*
 * Stores trees in an ArrayList without duplicates.
 * Uses a tree's string representation to remove duplicates.
 */
class HashSetWrapper {
    public ArrayList<Tree> variables = new ArrayList<>();
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

    public Tree searchByString(String str) {
        for (Tree variable : variables) {
            if (variable.toString().equals(str)) {
                return variable;
            }
        }
        return null;
    }
}

class Util {
    // checks if we are accessing the length property of an array
    static boolean isArrayLength(Tree node) {
        if (!(node instanceof JCFieldAccess)) {
            return false; // not a property access
        }

        JCFieldAccess access = (JCFieldAccess) node;
        if (!(access.selected.type instanceof Type.ArrayType)) {
            return false; // not a property access on an array
        }
        
        return access.name.toString().equals("length");
    }
}