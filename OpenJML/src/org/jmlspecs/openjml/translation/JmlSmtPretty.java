/**
 * This visitor converts JML syntax into SMT-LIB syntax that Rapid supports.
 * @author Kohei Koja
 */
package org.jmlspecs.openjml.translation;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.HashMap;
import java.util.Map;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlBlock;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.ext.Operators;
import org.jmlspecs.openjml.ext.QuantifiedExpressions;
import org.jmlspecs.openjml.ext.SingletonExpressions;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCAssignOp;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCParens;
import com.sun.tools.javac.tree.JCTree.JCReturn;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.Tag;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.util.List;

public class JmlSmtPretty extends JmlTranslator {
    /** JML specs **/
    private List<JmlSpecificationCase>            jmlSpecs     = null;

    /** pre-conditions **/
    private final java.util.List<JmlMethodClause> preconds     = new java.util.ArrayList<>();

    /** post-conditions **/
    private final java.util.List<JmlMethodClause> postconds    = new java.util.ArrayList<>();

    /** desugared pre-condition **/
    private final JmlMethodClause                 precond      = null;

    /** desugared post-condition **/
    private final JmlMethodClause                 postcond     = null;

    /** Tree maker for **/
    static private TreeMaker                      maker;

    /** boolean to check if the expression is the return expression */
    private boolean                               isReturnExpr = false;

    /** if the expression is in the post condition */
    private boolean                               isPostCond   = false;

    private static Map<String, String>            opsMap       = new HashMap<>();

    public JmlSmtPretty(final Writer out, final boolean sourceOutput) {
        super(out, sourceOutput);
    }

    static {
        opsMap.put("AND", "and");
        opsMap.put("OR", "or");
        opsMap.put("EQ", "=");
        opsMap.put("NE", "!=");
        opsMap.put("LT", "<");
        opsMap.put("GT", ">");
        opsMap.put("LE", "<=");
        opsMap.put("GE", ">=");
        opsMap.put("PLUS", "+");
        opsMap.put("MINUS", "-");
        opsMap.put("MUL", "*");
        opsMap.put("DIV", "/");
        opsMap.put("MOD", "%");
    }

    static public @NonNull String write(@NonNull final JCTree tree,
            final boolean source) {
        final StringWriter sw = new StringWriter();
        final JmlSmtPretty p = new JmlSmtPretty(sw, source);
        p.width = 2;
        if (tree != null) {
            tree.accept(p);
        }
        return sw.toString();
    }

    /**
     * A method used to report exceptions that happen on writing to the writer
     *
     * @param that
     *            a non-null AST node
     * @param e
     *            the exception that is being reported
     */
    @Override
    protected void perr(/* @ non_null */final JCTree that,
            /* @ non_null */final Exception e) {
        System.err.println(
                e.getClass() + " error in JMLSmtPretty: " + that.getClass());
        e.printStackTrace(System.err);
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
                    methodDecl.methodSpecsCombined.cases.accept(this);
                }
                methodDecl.accept(this);
            }
        }

        if (jmlSpecs != null) {
            for (final JmlSpecificationCase jmlSpecCase : jmlSpecs) {
                jmlSpecCase.accept(this);
            }
        }
    }

    @Override
    public void visitJmlMethodDecl(final JmlMethodDecl that) {
        if (that.body != null) {
            that.body.accept(this);
        }
    }

    @Override
    public void visitJmlBlock(final JmlBlock that) {
        if (that.type == null && specOnly) {
            return;
        }
        for (final JCStatement stat : that.stats) {
            if (stat instanceof JCReturn) {
                stat.accept(this);
            }
        }
    }

    @Override
    public void visitJmlMethodSpecs(final JmlMethodSpecs that) {
        if (that.cases.isEmpty()) {
            return;
        }
        if (jmlSpecs == null) {
            jmlSpecs = that.cases;
        }
    }

    @Override
    public void visitJmlSpecificationCase(final JmlSpecificationCase that) {
        if (that.clauses.isEmpty()) {
            return;
        }
        try {
            for (final JmlMethodClause clause : that.clauses) {
                if (clause.keyword.equals("requires")) {
                    preconds.add(clause);
                } else if (clause.keyword.equals("ensures")) {
                    postconds.add(clause);
                }
            }
            for (final JmlMethodClause precond : preconds) {
                print("(axiom");
                indent();
                printlnAndAlign();
                precond.accept(this);
                println();
                undent();
                println(")\n");
            }
            isPostCond = true;
            for (final JmlMethodClause postcond : postconds) {
                print("(conjecture");
                indent();
                printlnAndAlign();
                postcond.accept(this);
                println();
                undent();
                println(")\n");
            }
            isPostCond = false;
            // print("(assert-not");
            // println();
            // indentAndRealign();
            // if (!preconds.isEmpty()) {
            // if (preconds.size() != 1) {
            // precond = preconds.stream().reduce(null, this::conjoin);
            // } else {
            // precond = preconds.get(0);
            // }
            // print("(=>");
            // println();
            // align();
            // indentAndRealign();
            // precond.accept(this);
            // }
            // println();
            // align();
            // if (!postconds.isEmpty()) {
            // if (postconds.size() != 1) {
            // postcond = postconds.stream().reduce(null, this::conjoin);
            // } else {
            // postcond = postconds.get(0);
            // }
            // isPostCond = true;
            // postcond.accept(this);
            // isPostCond = false;
            // }
            // if (!preconds.isEmpty()) {
            // println();
            // undent();
            // align();
            // print(")");
            // }
            // println();
            // undent();
            // align();
            // print(")");
        } catch (final IOException e) {
            perr(that, e);
        }
    }

    private JmlMethodClause conjoin(final JmlMethodClause first,
            final JmlMethodClause second) {
        if (first == null) {
            return second;
        }
        if (first instanceof JmlMethodClauseExpr
                && second instanceof JmlMethodClauseExpr) {
            final JmlMethodClauseExpr f = (JmlMethodClauseExpr) first;
            final JmlMethodClauseExpr s = (JmlMethodClauseExpr) second;
            f.expression = maker.Binary(Tag.AND, f.expression, s.expression);
            return f;
        } else {
            throw new IllegalArgumentException("Invalid arguments are passed");
        }
    }

    @Override
    public void visitJmlMethodClauseExpr(final JmlMethodClauseExpr that) {
        that.expression.accept(this);
    }

    @Override
    public void visitParens(final JCParens that) {
        that.expr.accept(this);
    }

    @Override
    public void visitBinary(final JCBinary that) {
        try {
            print("(");
            printOp(that.opcode);
            print(" ");
            // printlnAndAlign();
            // indentAndRealign();
            that.lhs.accept(this);
            print(" ");
            // printlnAndAlign();
            that.rhs.accept(this);
            // printlnAndUndent();
            print(")");
        } catch (final IOException e) {
            perr(that, e);
        }
    }

    @Override
    public void visitJmlBinary(final JmlBinary that) {
        try {
            print("(");
            printOp(that.op);
            printlnAndAlign();
            indentAndRealign();
            that.lhs.accept(this);
            printlnAndAlign();
            that.rhs.accept(this);
            printlnAndUndent();
            print(")");
            printlnAndAlign();
        } catch (final IOException e) {
            perr(that, e);
        }
    }

    /**
     * Print string, replacing all non-ascii character with unicode escapes.
     */
    @Override
    public void print(final Object s) throws IOException {
        if (varMap.containsKey(s.toString())) {
            super.print(varMap.get(s.toString()));
        } else {
            super.print(s);
        }
    }

    private void printOp(final IJmlClauseKind op) {
        try {
            switch (op.name()) {
                case Operators.impliesID:
                    print("=>");
                    break;
                case Operators.equivalenceID:
                    break;
                case Operators.inequivalenceID:
                    break;
            }
        } catch (final IOException e) {
        }
    }

    private void printOp(final Tag opcode) {
        try {
            if (opsMap.containsKey(opcode.name())) {
                print(opsMap.get(opcode.name()));
            }
        } catch (final IOException e) {
        }
    }

    @Override
    public void visitJmlQuantifiedExpr(final JmlQuantifiedExpr that) {
        final int savedPrec = prec;
        prec = TreeInfo.noPrec;
        try {
            print(that.kind.keyword.replace('\\', '('));
            print(" (");
            String sep = "";
            for (final JCVariableDecl n : that.decls) {
                print(sep);
                print("(");
                String varName = n.name.toString();
                int i = 0;
                while (vars.contains(varName)) {
                    varName = n.name.toString() + i++;
                }
                if (i != 0) {
                    vars.add(varName);
                    varMap.put(n.name.toString(), varName);
                }
                n.accept(this);
                print(")");
                sep = " ";
            }
            println(")");
            align();
            indentAndRealign();
            switch (that.kind.name()) {
                case QuantifiedExpressions.qforallID:
                    println("(=>");
                    break;
                case QuantifiedExpressions.qexistsID:
                    println("(and");
                    break;
                default:
                    super.visitJmlQuantifiedExpr(that);
            }
            align();
            indentAndRealign();
            if (that.range != null) {
                that.range.accept(this);
            }
            printlnAndAlign();
            if (that.value != null) {
                that.value.accept(this);
            } else {
                print("????:"); //$NON-NLS-1$
            }
            printlnAndUndent();
            print(")");
            printlnAndUndent();
            print(")");
        } catch (final IOException e) {
            perr(that, e);
        } finally {
            prec = savedPrec;
        }
    }

    @Override
    public void visitJmlVariableDecl(final JmlVariableDecl that) {
        try {
            print(that.name);
            print(" ");
            printExpr(that.vartype);
        } catch (final IOException e) {
            perr(that, e);
        }
    }

    @Override
    public void visitJmlSingleton(final JmlSingleton that) {
        try {
            if (that.kind == SingletonExpressions.informalCommentKind) {
                print("(*");
                print(that.info);
                print("*)");
            } else if (that.kind == SingletonExpressions.resultKind) {
                if (returnExpr != null) {
                    isReturnExpr = true;
                    returnExpr.accept(this);
                    isReturnExpr = false;
                }
            } else {
                print(that);
            }
        } catch (final IOException e) {
            perr(that, e);
        }
    }

    @Override
    public void visitIndexed(final JCArrayAccess that) {
        try {
            print("(");
            that.indexed.accept(this);
            print(" ");
            that.index.accept(this);
            print(")");
        } catch (final IOException e) {
            perr(that, e);
        }
    }

    @Override
    public void visitUnary(final JCUnary tree) {
        try {
            final JCLiteral one = maker.Literal(1);
            switch (tree.getTag()) {
                case NOT:
                    print("(not");
                    println();
                    indentAndRealign();
                    tree.arg.accept(this);
                    printlnAndUndent();
                    print(")");
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
                    throw new IOException(
                            "Does not support this tag:" + tree.getTag());
            }
        } catch (final IOException e) {
            perr(tree, e);
        }
    }

    @Override
    public void visitIdent(final JCIdent that) {
        final boolean isVariableInPostCond = isPostCond
                && vars.contains(that.name.toString())
                && !varMap.containsKey(that.name.toString());
        try {
            if (isVariableInPostCond) {
                if (isReturnExpr) {
                    print("(");
                }
            }
            printVarName(that.name.toString());
            if (isVariableInPostCond) {
                print(" main_end");
                if (isReturnExpr) {
                    print(")");
                }
            }
        } catch (final IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitSelect(final JCFieldAccess tree) {
        try {
            if (tree.selected instanceof JCIdent) {
                print(((JCIdent) tree.selected).name.toString());
            } else {
                printExpr(tree.selected, TreeInfo.postfixPrec);
            }
            print(tree.name);
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
    public void visitReturn(final JCReturn tree) {
        // do nothing
    }

}
