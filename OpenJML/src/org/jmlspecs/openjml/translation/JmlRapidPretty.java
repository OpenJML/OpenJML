/**
 * This visitor converts java code to Rapid syntax
 * @author Kohei Koja
 */
package org.jmlspecs.openjml.translation;

import static com.sun.tools.javac.code.Flags.ENUM;
import static com.sun.tools.javac.code.Flags.INTERFACE;
import static com.sun.tools.javac.code.Flags.VARARGS;
import static com.sun.tools.javac.tree.JCTree.Tag.NEWCLASS;
import static com.sun.tools.javac.tree.JCTree.Tag.PARENS;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlTree.JmlBlock;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoopExpr;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotatedType;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCArrayTypeTree;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCAssignOp;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIf;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCNewClass;
import com.sun.tools.javac.tree.JCTree.JCReturn;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.JCWhileLoop;
import com.sun.tools.javac.tree.JCTree.Tag;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Pair;

public class JmlRapidPretty extends JmlTranslator {

    /** Parameters of the target function **/
    private List<JCVariableDecl> params = null;

    static public @NonNull String write(@NonNull final JCTree tree,
            final boolean source) {
        final StringWriter sw = new StringWriter();
        final JmlRapidPretty p = new JmlRapidPretty(sw, source);
        p.width = 2;
        if (tree != null) {
            tree.accept(p);
        }
        return sw.toString();
    }

    public JmlRapidPretty(final Writer out, final boolean sourceOutput) {
        super(out, sourceOutput);
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
                e.getClass() + " error in JMLRapidPretty: " + that.getClass());
        e.printStackTrace(System.err);
    }

    @Override
    public void visitJmlClassDecl(final JmlClassDecl that) {
        if (that instanceof org.jmlspecs.openjml.ext.DatatypeExt.JmlDatatypeDecl) {
            final org.jmlspecs.openjml.ext.DatatypeExt.JmlDatatypeDecl d = (org.jmlspecs.openjml.ext.DatatypeExt.JmlDatatypeDecl) that;
            try {
                print("datatype " + that.name.toString() + " {");
                indent();
                boolean first = true;
                for (final Pair<Name, List<JCTree.JCVariableDecl>> p : d.constructors) {
                    if (!first) {
                        print(",");
                    } else {
                        first = false;
                    }
                    println();
                    align();
                    print(p.fst.toString());
                    print("(");
                    print(p.snd.toString());
                    print(")");
                }
                undent();
                println();
                align();
                print("}");
                println();
                visitClassDef(that);
            } catch (final IOException e) {
                perr(that, e);
            }
        } else {
            visitClassDef(that);
        }
    }

    @Override
    public void visitClassDef(final JCClassDecl tree) {
        try {
            final Name enclClassNamePrev = enclClassName;
            enclClassName = tree.name;
            if ((tree.mods.flags & INTERFACE) != 0) {
                throw new Exception("Interface is not supported in Rapid.");
            } else if ((tree.mods.flags & ENUM) != 0) {
                throw new Exception("Interface is not supported in Rapid.");
            } else {
                printStats(tree.defs);
            }
            enclClassName = enclClassNamePrev;
        } catch (final IOException e) {
            throw new UncheckedIOException(e);
        } catch (final Exception e) {
            perr(tree, e);
        }
    }

    @Override
    public void visitJmlMethodDecl(final JmlMethodDecl that) {
        if (targetMethodName.equals(that.getName().toString())) {
            try {
                print("func main()");
                println();
                params = that.params;
                if (that.body != null) {
                    that.body.accept(this);
                }
                allIdents.removeAll(vars);
                consts.addAll(allIdents);
                allIdents.addAll(consts);
            } catch (final IOException e) {
                perr(that, e);
            }
        }
    }

    @Override
    public void visitJmlBlock(final JmlBlock that) {

        if (that.type == null && specOnly) {
            return;
        }

        try {
            printFlags(that.flags);
            printBlock(that.stats);
        } catch (final IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /**
     * Print a block.
     */
    @Override
    public void printBlock(final List<? extends JCTree> stats)
            throws IOException {
        println("{");
        indent();
        /** declaring all the params inside the block. **/
        if (params != null) {
            printParams(params);
            params = null;
        }
        printStats(stats);
        undent();
        align();
        print("}");
    }

    /**
     * If statement has to have else block
     */
    @Override
    public void visitIf(final JCIf tree) {
        try {
            print("if ");
            if (tree.cond.hasTag(PARENS)) {
                printExpr(tree.cond);
                tree.cond = null;
            } else {
                print("(");
                printExpr(tree.cond);
                print(")");
            }
            print(" ");
            printStat(tree.thenpart);
            if (tree.elsepart != null) {
                print(" else ");
                printStat(tree.elsepart);
            } else {
                print(" else { skip; }");
            }
        } catch (final IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private void printParams(final List<JCVariableDecl> params) {
        for (final JCVariableDecl param : params) {
            try {
                align();
                param.accept(this);
                println();
                if (param.type instanceof Type.ArrayType) {
                    /** print length variable for an array **/
                    align();
                    print("const Int ");
                    print(param.getName());
                    print("length;");
                    println();
                }
            } catch (final IOException e) {
                perr(param, e);
            }
        }
    }

    @Override
    public void visitJmlVariableDecl(final JmlVariableDecl that) {
        try {
            printDocComment(that);
            if ((that.mods.flags & ENUM) != 0) {
                print("/*public static final*/ ");
                print(that.name);
                if (that.init != null) {
                    if (sourceOutput && that.init.hasTag(NEWCLASS)) {
                        print(" /*enum*/ ");
                        final JCNewClass init = (JCNewClass) that.init;
                        if (init.args != null && init.args.nonEmpty()) {
                            print("(");
                            print(init.args);
                            print(")");
                        }
                        if (init.def != null && init.def.defs != null) {
                            print(" ");
                            printBlock(init.def.defs);
                        }
                        return;
                    }
                    print(" /* = ");
                    printExpr(that.init);
                    print(" */");
                }
            } else {
                // printExpr(that.mods);
                if ((that.mods.flags & VARARGS) != 0) {
                    JCTree vartype = that.vartype;
                    List<JCAnnotation> tas = null;
                    if (vartype instanceof JCAnnotatedType) {
                        tas = ((JCAnnotatedType) vartype).annotations;
                        vartype = ((JCAnnotatedType) vartype).underlyingType;
                    }
                    printExpr(((JCArrayTypeTree) vartype).elemtype);
                    if (tas != null) {
                        print(' ');
                        printTypeAnnotations(tas);
                    }
                    print("... " + that.name);
                } else {
                    if (consts.contains(that.name.toString())) {
                        print("const ");
                    }
                    printExpr(that.vartype);
                    print(" " + that.name);
                }
                if (that.init != null) {
                    print(" = ");
                    printExpr(that.init);
                }
                if (prec == TreeInfo.notExpression) {
                    print(";");
                }
            }
        } catch (final IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitUnary(final JCUnary tree) {
        final JCLiteral one = maker.Literal(1);
        switch (tree.getTag()) {
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
    }

    @Override
    public void visitReturn(final JCReturn that) {
        returnExpr = that.expr;
        // final IExpr result = smtTranslator.convertExpr(returnExpr);
        // Mapper.addReturnExpr(result);
    }

    @Override
    public void visitJmlForLoop(final JmlForLoop that) {
        try {
            for (final JCStatement stat : that.init) {
                printStat(stat);
                printlnAndAlign();
            }
            List<JCStatement> stats = List.nil();
            if (that.body instanceof JmlBlock) {
                final JmlBlock jmlBlock = (JmlBlock) that.body;
                stats = stats.appendList(jmlBlock.stats);
            } else {
                stats = stats.append(that.body);
            }
            for (final JCExpressionStatement stat : that.step) {
                stats = stats.append(stat);
            }
            final JmlBlock body = maker.Block(0, stats);
            final JCWhileLoop whileLoop = maker.WhileLoop(that.cond, body);
            whileLoop.accept(this);
        } catch (final IOException e) {
            perr(that, e);
        }
    }

    @Override
    public void visitSelect(final JCFieldAccess tree) {
        try {
            if (tree.toString().equals("Integer.MAX_VALUE")) {
                print(Integer.MAX_VALUE);
            } else if (tree.toString().equals("Integer.MIN_VALUE")) {
                print(0);
            } else {
                printExpr(tree.selected, TreeInfo.postfixPrec);
                print(tree.name);
            }
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
    public void visitJmlStatementExpr(final JmlStatementExpr that) {
        // print nothing
    }

    @Override
    public void visitAnnotation(final JCAnnotation tree) {
        // print nothing
    }

    @Override
    public void visitJmlStatementLoopExpr(final JmlStatementLoopExpr that) {
        // print nothing
    }

}
