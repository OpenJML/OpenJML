// Senior Design Spring Fall 2023 group work

package com.sun.tools.javac.main;

import org.jmlspecs.openjml.visitors.IJmlVisitor;
import org.jmlspecs.openjml.visitors.JmlTreeCopier;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.jmlspecs.openjml.visitors.JmlTreeTranslator;
import org.jmlspecs.openjml.ext.StatementExprExtensions;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlOptions;
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
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;
import com.sun.tools.javac.tree.TreeScanner;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashSet;

/**
 * This visitor looks for a loop and assertion together (assertion after the loop).
 * If a pair is found, the boolean variable complete is marked as true and the loop invariant is generated
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

/**
 * This visitor tries to find the initial value of a given variable.
 */
class VariableInitFinder extends TreeScanner {

    public JCExpression initialValue = null; // stays null if initial value wasn't found
    public JCIdent variable;

    public VariableInitFinder(JCIdent variable) {
        this.variable = variable;
    }

    @Override
    public void visitVarDef(JCVariableDecl tree) {
        if (tree.name.toString().equals(variable.name.toString())) {
            this.initialValue = tree.init;
        }
        super.visitVarDef(tree);
    }
}

class AssertionReader extends TreeScanner implements IJmlVisitor {

    private final String ITERATOR_VAR = "iterator_var";
    private String old_iterator_name;
    private Context context;

    public AssertionReader(Context context) {
        this.context = context;
    }

    @Override
    public void scan(JCTree tree) {
        if (tree != null) {
            if (tree instanceof JmlVariableDecl) {
                JmlVariableDecl temp = (JmlVariableDecl) tree;
                this.old_iterator_name = temp.getName().toString();
                temp.name = Names.instance(context).fromString(ITERATOR_VAR);
            } else {
                if (tree instanceof JCIdent) {
                    JCIdent temp = (JCIdent) tree;
                    if (temp.getName().toString().equals(old_iterator_name)) {
                        temp.name = Names.instance(context).fromString(ITERATOR_VAR);
                    }
                }
            }
            super.scan(tree); 
        }

    }

    @Override
    public void visitTree(JCTree tree) {
        // Generic visit for any trees not specially handled
        if (tree != null) {
            super.scan(tree);
        }
    }
}

/**
 * This visitor goes through the postcondition to look for potential constants to replace.
 * It also goes through the loop parameters to find potential replacement variables;
 * The collected variables/constants (numeric, integer values) are placed into the "collected" list.
 */
class ReplaceCandidateFinder extends TreeScanner implements IJmlVisitor {
    // stores our collected variables/constants
    public ListWithoutDuplicates<JCTree> collected;

    // whether we are collecting constants for replacement, or replacement variables
    private boolean variableMode = false;

    public ReplaceCandidateFinder(boolean variableMode) {
        collected = new ListWithoutDuplicates<>();
        this.variableMode = variableMode;
    }

    @Override
    // Covers expressions such as arr.length
    // "Selects through packages and classes"
    public void visitSelect(JCFieldAccess tree) {
        if (this.variableMode) return; // JCFIeldAccess will probably be a constant in the parameters of a loop

        String nameOfSelectedField = tree.name.toString();
        
        if (Util.isArrayLength(tree) || nameOfSelectedField.equals("size")) {
            // this looks like an array length expression or a collection size expression
            collected.add(tree);
        }

        super.visitSelect(tree);
    }

    @Override
    public void visitLiteral(JCLiteral tree) {
        if (this.variableMode) return; // since literals are always constant

        // make sure the literal is of an integer value (not a string literal, etc)
        if (isIntegerType(tree.typetag)) {
            collected.add(tree);
        }
    }

    @Override
    public void visitIdent(JCIdent tree) {
        // make sure the identifier has an integer type
        if (isIntegerType(tree.sym.type.getTag())) {
            collected.add(tree);
        }
    }
    
    // checks if this is an integer type
    // for constants to replace, and for replacement variables
    private boolean isIntegerType(TypeTag tag) {
        return tag == TypeTag.BYTE || tag == TypeTag.SHORT || tag == TypeTag.INT || tag == TypeTag.LONG;
    }
}

/**
 * This object performs the replacement of constants with variables
 */
class ConstantReplacer extends JmlTreeTranslator {
    Context context;
    Maker make;
    Symtab symtab;

    private JCTree old_constant; // the constant we are replacing
    private JCTree new_variable; // the variable to replace the constant with

    public ConstantReplacer(Context context) {
        this.context = context;
        this.make = Maker.instance(context);
        this.symtab = Symtab.instance(context);
    }

    public void setOldConstant(JCTree constant) {
        this.old_constant = constant;
    }

    public void setNewVariable(JCTree variable) {
        this.new_variable = variable;
    }

    public JCTree getOldConstant() {
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
        return (JCIdent) (this.new_variable.clone());
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
    Env<AttrContext> env;
    LoopAssertionFinder lAssertionFinder = new LoopAssertionFinder(); // used to find the loop and assertion pair
    ReplaceCandidateFinder constantFinder = new ReplaceCandidateFinder(false); // used to read the assertion
    ReplaceCandidateFinder variableFinder = new ReplaceCandidateFinder(true); // used to read the loop parameters
    Log log;

    public LoopInvariantGenerator(Context context) {
        this.context = context;
        this.make = Maker.instance(context);
        this.constantReplacer = new ConstantReplacer(context);
        this.copier = new JmlTreeCopier(context, this.make);
        this.treeMaker = TreeMaker.instance(context);
        this.name = Names.instance(context);
        this.symtab = Symtab.instance(context);
        this.esc = JmlEsc.instance(context);
        this.log = Log.instance(context);
    }

    // this gets called between the flow and desugar stages
    public void generateInvariant(Env<AttrContext> env) {
        JCTree tree = env.tree; // the AST
        this.env = env;

        final String inputFilename = Paths.get(log.currentSourceFile().toUri()).getFileName().toString();
        final Path outputPath = Paths.get("_generated", inputFilename);

        // make this opt-in
        boolean enabled = JmlOptions.instance(context).getBoolean(JmlOption.INFER_INVARIANTS.optionName());
        if (!enabled) {
            return;
        }

        lAssertionFinder.scan(tree); // find the loop + assertion

        // if a loop + assertion is not found, nothing happens
        if (!lAssertionFinder.complete) {
            reportGenerationFailure("didn't find a loop and assertion");
            return;
        }

        new AssertionReader(context).scan(lAssertionFinder.detectedAssertion.expression);

        IJmlLoop loop = null;

        // This block of code reads the parameters of the loop to obtain possible replacement variables
        if (lAssertionFinder.detectedForLoop == null) {
            loop = lAssertionFinder.detectedWhileLoop;
            this.variableFinder.scan(lAssertionFinder.detectedWhileLoop.cond); // while loop condition
        } else {
            loop = lAssertionFinder.detectedForLoop;
            // for loop initialization
            if (lAssertionFinder.detectedForLoop.init != null) {
                for (JCStatement temp : lAssertionFinder.detectedForLoop.init) {
                    this.variableFinder.scan(temp);
                }
            }

            this.variableFinder.scan(lAssertionFinder.detectedForLoop.cond); // for loop condition 

            // for loop post-iteration operation
            if (lAssertionFinder.detectedForLoop.step != null) {
                for (JCExpressionStatement temp : lAssertionFinder.detectedForLoop.step) {
                    this.variableFinder.scan(temp);
                }
            }
        }

        constantFinder.scan(lAssertionFinder.detectedAssertion.expression); // read the assertion and store the possible constants to be replaced

        if (variableFinder.collected.items.size() == 0 ||
                constantFinder.collected.items.size() == 0) {
            reportGenerationFailure("no constants to replace, or no variables to replace with");
            return; // no constants to replace, or no variables to replace with
        }

        // Replace constant with variable, trying each constant/variable combination until one works
        boolean verified = false;
        OUTER:
        for (JCTree constant : constantFinder.collected.items) {
            for (JCTree variable : variableFinder.collected.items) {

                constantReplacer.setOldConstant(constant);
                constantReplacer.setNewVariable(variable);

                // make a boundary expression for our new variable
                JmlStatementLoopExpr boundary = this.make.JmlStatementLoopExpr(
                        StatementExprExtensions.loopinvariantClause,
                        makeBoundaryExpression(loop, (JCIdent) variable, (JCExpression) constant));
             
                // make new invariant using the postcondition
                JmlStatementLoopExpr invariant = this.make.JmlStatementLoopExpr(
                        StatementExprExtensions.loopinvariantClause,
                        copier.copy(lAssertionFinder.detectedAssertion.expression));

                // modify the invariant's tree by replacing constants with variables
                invariant.accept(constantReplacer);
        
                // attach our new invariants to the loop
                loop.setLoopSpecs(List.of(boundary, invariant));
                
                // check whether this constant/variable combination yielded a correct invariant
                verified = getEscVerificationResult(tree);
    
                // if successful, write output to file
                if (verified) {
                    try {
                        String output = env.tree.toString();

                        // remove extra "public static" annotation from output
                        output = output.replaceFirst("(?m)^\\s*public static $", "");

                        // write output to _generated/{filename}
                        Files.createDirectories(outputPath.getParent());
						Files.write(outputPath, output.getBytes());

                        log.printRawLines("Successfully determined loop invariants: " + outputPath);
					} catch (Exception e) {
						log.rawError(Position.NOPOS, "Cannot write to output file: " + e.toString());
					}
                    break OUTER; // early exit
                }
            }
        }

        if (!verified) {
            reportGenerationFailure("no valid constant replacement found");
        }
    }

    private void reportGenerationFailure(String reason) {
        log.rawWarning(Position.NOPOS, "Could not generate a loop invariant: " + reason);
    }

    private boolean getEscVerificationResult(JCTree tree) {
        esc.initCounts();
        esc.check(tree);
        return (esc.classes == esc.classesOK);
    }

    /**
     * Makes a boundary expression for a given variable.
     * lower bound is the variable's initial value if we can find it, otherwise 0.
     * upper bound is the constant that the variable is replacing.
     * 
     * Caveat: this assumes that the iteration variable increases by 1 each time
     */
    private JmlChained makeBoundaryExpression(IJmlLoop loop, JCIdent variable, JCExpression constant) {
        // try to get the initial value from the for loop's initializer
        JCExpression initialValue = getInitialValueOfVar(variable, loop);
        
        // make expression for the lower bound
        JCBinary lowerBound;
        if (initialValue != null) {
            lowerBound = treeMaker.Binary(JCTree.Tag.LE, initialValue, variable);
        } else {
            // couldn't find initial value, so assume it is 0
            JCLiteral zero = treeMaker.Literal(0).setType(symtab.intType);
            lowerBound = treeMaker.Binary(JCTree.Tag.LE, zero, variable);
        }
        lowerBound.setType(symtab.booleanType);
        
        // make expression for the upper bound
        JCBinary upperBound = treeMaker.Binary(JCTree.Tag.LE, (JCTree.JCIdent)variable, constant);  
        upperBound.setType(symtab.booleanType);
        
        // combine the two expressions into a single JmlChained
        JmlChained boundary_expression = this.make.JmlChained(List.of(lowerBound, upperBound));
        boundary_expression.setType(symtab.booleanType);

        return boundary_expression;
    }

    /**
     * @return the variable's initialized value, if found. otherwise null
     */
    private JCExpression getInitialValueOfVar(JCIdent variable, IJmlLoop loop) {
        if (loop instanceof JCForLoop) {
            // with for loops, search the init for initializations of the variable
            JCForLoop forLoop = (JCForLoop) loop;
            for (JCStatement statement : forLoop.init) {
                if (statement instanceof JCVariableDecl) {
                    JCVariableDecl decl = (JCVariableDecl) statement;
                    if (decl.name.toString().equals(variable.name.toString())) {
                        return decl.init;
                    }
                }
            }
        } else if (loop instanceof JCWhileLoop) {
            // with while loops, search the entire AST for initializations of the variable
            VariableInitFinder finder = new VariableInitFinder(variable);
            finder.scan(env.tree);
            return finder.initialValue;
        }
        return null; // no initialized value found
    }
}

/**
 * Stores items in an ArrayList without duplicates.
 * Uses an item's string representation to remove duplicates.
 */
class ListWithoutDuplicates<E> {
    public ArrayList<E> items = new ArrayList<>();
    private HashSet<String> duplicates = new HashSet<>();

    public void add(E item) {
        if (!duplicates.contains(item.toString())) {
            items.add(item);
            duplicates.add(item.toString());
        }
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