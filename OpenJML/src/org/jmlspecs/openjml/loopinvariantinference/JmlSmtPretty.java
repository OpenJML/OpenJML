/**
 * This visitor converts JML syntax into SMT2-lib syntax that Rapid supports.
 * @author Kohei Koja
 */
package org.jmlspecs.openjml.loopinvariantinference;

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
import org.jmlspecs.openjml.ext.SingletonExpressions;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCParens;
import com.sun.tools.javac.tree.JCTree.JCReturn;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.Tag;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.util.List;

public class JmlSmtPretty extends JmlConversionVisitor {
    /** JML specs **/
    private List<JmlSpecificationCase>            jmlSpecs   = null;

    /** return value **/
    protected static JCExpression                 returnExpr = null;

    /** pre-conditions **/
    private final java.util.List<JmlMethodClause> preconds   = new java.util.ArrayList<>();

    /** post-conditions **/
    private final java.util.List<JmlMethodClause> postconds  = new java.util.ArrayList<>();

    /** desugared pre-condition **/
    private JmlMethodClause                       precond    = null;

    /** desugared post-condition **/
    private JmlMethodClause                       postcond   = null;

    /** Tree maker for **/
    static private TreeMaker                      make;

    private static Map<String, String>            opsMap     = createOpsMap();

    public JmlSmtPretty(final Writer out, final boolean sourceOutput) {
        super(out, sourceOutput);
    }

    private static Map<String, String> createOpsMap() {
        final Map<String, String> map = new HashMap<>();
        map.put("AND", "and");
        map.put("OR", "or");
        map.put("EQ", "=");
        map.put("NE", "!=");
        map.put("LT", "<");
        map.put("GT", ">");
        map.put("LE", "<=");
        map.put("GE", ">=");
        map.put("PLUS", "+");
        map.put("MINUS", "-");
        map.put("MUL", "*");
        map.put("DIV", "/");
        map.put("MOD", "%");
        return map;
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

    public static String write(final JCTree tree, final boolean b,
            final String mName, final TreeMaker make) {
        JmlSmtPretty.make = make;
        targetMethodName = mName;
        return write(tree, b);
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
            print("(assert-not");
            println();
            indentAndRealign();
            if (!preconds.isEmpty()) {
                if (preconds.size() != 1) {
                    precond = preconds.stream().reduce(null, this::concat);
                } else {
                    precond = preconds.get(0);
                }
                print("(=>");
                println();
                align();
                indentAndRealign();
                precond.accept(this);
            }
            println();
            align();
            if (!postconds.isEmpty()) {
                if (postconds.size() != 1) {
                    postcond = postconds.stream().reduce(null, this::concat);
                } else {
                    postcond = postconds.get(0);
                }
                postcond.accept(this);
            }
            if (!preconds.isEmpty()) {
                println();
                undent();
                align();
                print(")");
            }
            println();
            undent();
            align();
            print(")");
        } catch (final IOException e) {
            perr(that, e);
        }
    }

    private JmlMethodClause concat(final JmlMethodClause first,
            final JmlMethodClause second) {
        if (first == null) {
            return second;
        }
        if (first instanceof JmlMethodClauseExpr
                && second instanceof JmlMethodClauseExpr) {
            final JmlMethodClauseExpr f = (JmlMethodClauseExpr) first;
            final JmlMethodClauseExpr s = (JmlMethodClauseExpr) second;
            f.expression = make.Binary(Tag.AND, f.expression, s.expression);
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
            println();
            align();
            indentAndRealign();
            that.lhs.accept(this);
            println();
            align();
            that.rhs.accept(this);
            println();
            undent();
            align();
            print(")");
            println();
            align();
        } catch (final IOException e) {
            perr(that, e);
        }
    }

    @Override
    public void visitJmlBinary(final JmlBinary that) {
        try {
            print("(");
            printOp(that.op);
            println();
            align();
            indentAndRealign();
            that.lhs.accept(this);
            println();
            align();
            that.rhs.accept(this);
            println();
            undent();
            align();
            print(")");
            println();
            align();
        } catch (final IOException e) {
            perr(that, e);
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
            boolean first = true;
            for (final JCVariableDecl n : that.decls) {
                print("(");
                if (!first) {
                    print(", "); //$NON-NLS-1$
                } else {
                    first = false;
                }
                final String varName = n.name.toString();
                if (vars.contains(varName)) {
                    throw new IOException(
                            "You must declare the different variables from the ones in the source code.");
                }
                n.accept(this);
                print(")");
            }
            print(")");
            println();
            align();
            indentAndRealign();
            print("(=>");
            println();
            align();
            indentAndRealign();
            if (that.range != null) {
                that.range.accept(this);
            }
            println();
            align();
            if (that.value != null) {
                that.value.accept(this);
            } else {
                print("????:"); //$NON-NLS-1$
            }
            println();
            undent();
            align();
            print(")");
            println();
            undent();
            align();
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
            printType(that.type);
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
                    print("(");
                    print(returnExpr.toString());
                    print(" main_end)");
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
    public void visitReturn(final JCReturn that) {
        returnExpr = that.expr;
    }

    @Override
    public void visitUnary(final JCUnary that) {
        try {
            if (that.getTag() == Tag.NOT) {
                print("(not");
                println();
                align();
                indentAndRealign();
            } else {
                throw new IOException(
                        "Does not support this tag:" + that.getTag());
            }
            that.arg.accept(this);
            println();
            undent();
            align();
            print(")");
        } catch (final IOException e) {
            perr(that, e);
        }
    }

}
