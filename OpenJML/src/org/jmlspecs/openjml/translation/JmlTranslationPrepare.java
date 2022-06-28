/**
 * This visitor deletes all the null expressions since Rapid syntax does not support null expressions.
 * Also, it classifies variables into 2 categories.
 * If one is assigned, it is classified as mutable variables.
 * The other is classified as constants.
 * You can change this class in general purpose to modify and parse the tree.
 * @author Kohei Koja
 */
package org.jmlspecs.openjml.translation;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.Stack;

import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.Maker;
import org.jmlspecs.openjml.ext.MethodSimpleClauseExtensions;
import org.jmlspecs.openjml.ext.Operators;

import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCAssignOp;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.Tag;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.util.List;

public class JmlTranslationPrepare extends JmlTranslator {

    static private JCTree        result     = null;

    static private boolean       context    = true;

    static private Stack<JCTree> stack      = new Stack<>();

    static private Maker         maker;

    /** To check if it's constant or not **/
    private boolean              isUpdating = false;

    public JmlTranslationPrepare(final Writer out, final boolean sourceOutput) {
        super(out, sourceOutput);
    }

    public static void prepare(final JCTree tree, final Maker make) {
        JmlTranslationPrepare.maker = make;
        final StringWriter sw = new StringWriter();
        final JmlTranslationPrepare d = new JmlTranslationPrepare(sw, false);
        if (tree != null) {
            tree.accept(d);
        }
        result = tree;
    }

    public static JCTree getResult() {
        return result;
    }

    @Override
    public void visitJmlClassDecl(final JmlClassDecl that) {
        for (final JCTree jcTree : that.defs) {
            if (jcTree instanceof JmlMethodDecl) {
                /**
                 * It doesn't support the overloaded methods (methods with the
                 * same name)
                 **/
                final JmlMethodDecl methodDecl = (JmlMethodDecl) jcTree;
                if (targetMethodName.equals(methodDecl.getName().toString())) {
                    methodDecl.accept(this);
                    allIdents.removeAll(vars);
                    consts.addAll(allIdents);
                    allIdents.addAll(consts);
                }
            }
        }
    }

    @Override
    public void visitJmlMethodClauseExpr(final JmlMethodClauseExpr that) {
        stack.push(that.expression);
        that.expression.accept(this);
        that.expression = (JCExpression) stack.pop();
        if (that.expression == null) {
            stack.pop();
            stack.push(null);
        }
    }

    @Override
    public void visitJmlSpecificationCase(final JmlSpecificationCase that) {
        // Presumes the output is already aligned before the call
        // Presumes the caller does any needed println() afterwards
        try {
            boolean modOrCodeOrBehavior = false;
            if (that.modifiers != null && (that.modifiers.flags != 0
                    || (that.modifiers.annotations != null
                            && !that.modifiers.annotations.isEmpty()))) {
                that.modifiers.accept(this); // presumes that this call adds a
                                             // trailing space
                modOrCodeOrBehavior = true;
            }
            if (that.code) {
                print(MethodSimpleClauseExtensions.codeID);
                print(" ");
                modOrCodeOrBehavior = true;
            }
            if (that.token == MethodSimpleClauseExtensions.modelprogramClause) {
                print(MethodSimpleClauseExtensions.modelprogramID);
                print(" ");
                that.block.accept(this);
                return;
            }
            if (that.token == null) {
                // lightweight
            } else {
                print(that.token.keyword);
                if (that.name != null) {
                    print(" ");
                    print(that.name);
                    print(": ");
                }
                modOrCodeOrBehavior = true;
            }
            if (modOrCodeOrBehavior) {
                println();
                align();
            }
            try {
                // Note - the output is already aligned, so we have to bump up
                // the alignment
                indentAndRealign();
                List<JmlMethodClause> validClauses = List.nil();
                boolean first = true;
                if (that.clauses != null) {
                    for (final JmlMethodClause c : that.clauses) {
                        if (first) {
                            first = false;
                        } else {
                            println();
                            align();
                        }
                        stack.push(c);
                        c.accept(this);
                        if (stack.pop() != null) {
                            validClauses = validClauses.append(c);
                        }
                    }
                }
                that.clauses = validClauses;
                if (that.block != null) {
                    println();
                    align();
                    that.block.accept(this);
                }
            } finally {
                undent();
            }
        } catch (final IOException e) {
            perr(that, e);
        }
    }

    @Override
    public void visitUnary(final JCUnary tree) {
        try {
            final int ownprec = TreeInfo.opPrec(tree.getTag());
            final JCLiteral one = maker.Literal(1);
            switch (tree.getTag()) {
                case NOT:
                    context = !context;
                    stack.push(tree.arg);
                    printExpr(tree.arg, ownprec);
                    tree.arg = (JCExpression) stack.pop();
                    break;
                case PREINC:
                case POSTINC:
                    (maker.Assignop(Tag.PLUS_ASG, tree.arg, one)).accept(this);
                    break;
                case PREDEC:
                case POSTDEC:
                    (maker.Assignop(Tag.MINUS_ASG, tree.arg, one)).accept(this);
                    break;
                default:
                    super.visitUnary(tree);
            }
        } catch (final IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitBinary(final JCBinary that) {
        try {
            final int ownprec = TreeInfo.opPrec(that.getTag());
            final String opname = operatorName(that.getTag());
            open(prec, ownprec);
            stack.push(that.lhs);
            printExpr(that.lhs, ownprec);
            that.lhs = (JCExpression) stack.pop();
            print(" " + opname + " ");
            stack.push(that.rhs);
            printExpr(that.rhs, ownprec + 1);
            that.rhs = (JCExpression) stack.pop();
            close(prec, ownprec);
            if (that.lhs == null && that.rhs == null) {
                stack.pop();
                stack.push(null);
            } else if (that.lhs != null && that.rhs == null) {
                stack.pop();
                stack.push(that.lhs);
            } else if (that.lhs == null && that.rhs != null) {
                stack.pop();
                stack.push(that.rhs);
            } else {
                if (!isNullLiteral(that.lhs) && !isNullLiteral(that.rhs)) {
                    // do nothing
                } else if (isNullLiteral(that.lhs) && isNullLiteral(that.rhs)) {
                    stack.pop();
                    if (opname.equals("!=")) {
                        context = false; // (null != null) is always false
                    }
                    if (opname.equals("==")) {
                        context = true; // (null == null) is always true
                    }
                    stack.push(createBoolExpr());
                } else {
                    stack.pop();
                    stack.push(null);
                    // stack.push(createBoolExpr());
                }
            }
        } catch (final IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitJmlBinary(final JmlBinary that) {
        stack.push(that.lhs);
        that.lhs.accept(this);
        that.lhs = (JCExpression) stack.pop();
        stack.push(that.rhs);
        that.rhs.accept(this);
        that.rhs = (JCExpression) stack.pop();
        stack.pop();
        stack.push(createJmlExpr(that));
    }

    private JCExpression createJmlExpr(final JmlBinary that) {
        switch (that.op.name()) {
            case Operators.equivalenceID:
                return maker.Binary(Tag.AND,
                        maker.JmlBinary(Operators.impliesKind, that.lhs,
                                that.rhs),
                        maker.JmlBinary(Operators.impliesKind, that.rhs,
                                that.lhs));
            case Operators.inequivalenceID:
                return maker.Unary(Tag.NOT,
                        maker.Binary(Tag.AND,
                                maker.JmlBinary(Operators.impliesKind, that.lhs,
                                        that.rhs),
                                maker.JmlBinary(Operators.impliesKind, that.rhs,
                                        that.lhs)));
            default:
                return that;
        }
    }

    private JCLiteral createBoolExpr() {
        if (context) {
            context = !context;
            return maker.Literal(TypeTag.BOOLEAN, Integer.valueOf(1));
        } else {
            context = !context;
            return maker.Literal(TypeTag.BOOLEAN, Integer.valueOf(0));
        }
    }

    private boolean isNullLiteral(final JCExpression e) {
        if (e instanceof JCLiteral) {
            final JCLiteral l = (JCLiteral) e;
            return l.getValue() == null;
        }
        return false;
    }

    @Override
    public void visitSelect(final JCFieldAccess that) {
        try {
            switch (that.name.toString()) {
                case "MAX_VALUE":
                    stack.pop();
                    if (that.type.toString().equals("int")) {
                        stack.push(maker.Literal(Integer.MAX_VALUE));
                    } else {
                        throw new Exception(
                                "Cannot parse this type: " + that.type);
                    }
                    break;
                case "MIN_VALUE":
                    stack.pop();
                    if (that.type.toString().equals("int")) {
                        stack.push(maker.Literal(Integer.MIN_VALUE));
                    } else {
                        throw new Exception(
                                "Cannot parse this type: " + that.type);
                    }
                    break;
                default:
                    super.visitSelect(that);
            }
        } catch (final Exception e) {
        }
    }

    @Override
    public void visitAssign(final JCAssign tree) {
        try {
            open(prec, TreeInfo.assignPrec);
            isUpdating = true;
            printExpr(tree.lhs, TreeInfo.assignPrec + 1);
            isUpdating = false;
            print(" = ");
            printExpr(tree.rhs, TreeInfo.assignPrec);
            close(prec, TreeInfo.assignPrec);
        } catch (final IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitAssignop(final JCAssignOp tree) {
        final JCBinary rhs = maker.Binary(tree.getTag().noAssignOp(), tree.lhs,
                tree.rhs);
        final JCAssign assign = maker.Assign(tree.lhs, rhs);
        assign.accept(this);
    }

    @Override
    public void visitIdent(final JCIdent tree) {
        try {
            if (isUpdating) {
                vars.add(tree.getName().toString());
            }
            allIdents.add(tree.getName().toString());
            print(tree.name);
        } catch (final IOException e) {
            throw new UncheckedIOException(e);
        }
    }

}
