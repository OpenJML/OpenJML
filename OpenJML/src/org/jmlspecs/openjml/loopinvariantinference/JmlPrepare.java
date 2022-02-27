/**
 * This visitor deletes all the null expressions since Rapid syntax does not support null expressions.
 * You can change this class in general purpose to modify the tree.
 * @author Kohei Koja
 */
package org.jmlspecs.openjml.loopinvariantinference;

import java.io.StringWriter;
import java.io.Writer;
import java.util.Stack;

import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.Maker;
import org.jmlspecs.openjml.ext.Operators;

import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.Tag;

public class JmlPrepare extends JmlConversionVisitor {

    static private JCTree        result  = null;

    static private boolean       context = true;

    static private Stack<JCTree> stack   = new Stack<>();

    static private Maker         make;

    public JmlPrepare(Writer out, boolean sourceOutput) {
        super(out, sourceOutput);
    }

    public static void prepare(JCTree tree, Maker make) {
        JmlPrepare.make = make;
        StringWriter sw = new StringWriter();
        JmlPrepare d = new JmlPrepare(sw, false);
        if (tree != null) {
            tree.accept(d);
        }
        result = tree;
    }

    public static JCTree getResult() {
        return result;
    }

    @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        for (JCTree jcTree : that.defs) {
            if (jcTree instanceof JmlMethodDecl) {
                /**
                 * It doesn't support the overloaded methods (methods with the
                 * same name)
                 **/
                JmlMethodDecl methodDecl = (JmlMethodDecl) jcTree;
                if (targetMethodName.equals(methodDecl.getName().toString())) {
                    methodDecl.methodSpecsCombined.cases.accept(this);
                }
            }
        }
    }

    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        stack.push(that.expression);
        that.expression.accept(this);
        JCExpression e = (JCExpression) stack.pop();
        if (e == null) {
            that.expression = createExpr();
        } else {
            that.expression = e;
        }
    }

    @Override
    public void visitUnary(JCUnary that) {
        context = (that.getTag() == Tag.NOT) ? false : true;
        super.visitUnary(that);
    }

    @Override
    public void visitBinary(JCBinary that) {
        stack.push(that.lhs);
        that.lhs.accept(this);
        that.lhs = (JCExpression) stack.pop();
        stack.push(that.rhs);
        that.rhs.accept(this);
        that.rhs = (JCExpression) stack.pop();
        if (!isNullValue(that.lhs) && !isNullValue(that.rhs)) {
            // do nothing
        } else if (isNullValue(that.lhs) && isNullValue(that.rhs)) {
            stack.pop();
            context = (that.getTag() == Tag.NE) ? false : true;
            stack.push(createExpr());
        } else {
            stack.pop();
            stack.push(createExpr());
        }
    }

    @Override
    public void visitJmlBinary(JmlBinary that) {
        stack.push(that.lhs);
        that.lhs.accept(this);
        that.lhs = (JCExpression) stack.pop();
        stack.push(that.rhs);
        that.rhs.accept(this);
        that.rhs = (JCExpression) stack.pop();
        stack.pop();
        stack.push(createJmlExpr(that));
    }

    private JCExpression createJmlExpr(JmlBinary that) {
        switch (that.op.name()) {
            case Operators.equivalenceID:
                return make.Binary(Tag.AND,
                        make.JmlBinary(Operators.impliesKind, that.lhs,
                                that.rhs),
                        make.JmlBinary(Operators.impliesKind, that.rhs,
                                that.lhs));
            case Operators.inequivalenceID:
                return make.Unary(Tag.NOT,
                        make.Binary(Tag.AND,
                                make.JmlBinary(Operators.impliesKind, that.lhs,
                                        that.rhs),
                                make.JmlBinary(Operators.impliesKind, that.rhs,
                                        that.lhs)));
            default:
                return that;
        }
    }

    private JCLiteral createExpr() {
        if (context) {
            context = !context;
            return make.Literal(TypeTag.BOOLEAN, Integer.valueOf(1));
        } else {
            context = !context;
            return make.Literal(TypeTag.BOOLEAN, Integer.valueOf(0));
        }
    }

    private boolean isNullValue(JCExpression e) {
        if (e instanceof JCLiteral) {
            JCLiteral l = (JCLiteral) e;
            return l.getValue() == null;
        }
        return false;
    }

    @Override
    public void visitSelect(JCFieldAccess that) {
        try {
            switch (that.name.toString()) {
                case "MAX_VALUE":
                    stack.pop();
                    if (that.type.toString().equals("int"))
                        stack.push(make.Literal(Integer.MAX_VALUE));
                    else
                        throw new Exception(
                                "Cannot parse this type: " + that.type);
                    break;
                case "MIN_VALUE":
                    stack.pop();
                    if (that.type.toString().equals("int"))
                        stack.push(make.Literal(Integer.MIN_VALUE));
                    else
                        throw new Exception(
                                "Cannot parse this type: " + that.type);
                    break;
                default:
                    super.visitSelect(that);
            }
        } catch (Exception e) {
        }
    }
}
