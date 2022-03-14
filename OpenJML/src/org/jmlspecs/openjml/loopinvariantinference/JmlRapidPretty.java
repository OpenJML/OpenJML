/**
 * This visitor converts java code to Rapid syntax
 * @author Kohei Koja
 */
package org.jmlspecs.openjml.loopinvariantinference;

import static com.sun.tools.javac.tree.JCTree.Tag.PARENS;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlBlock;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCIf;
import com.sun.tools.javac.tree.JCTree.JCReturn;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.Tag;
import com.sun.tools.javac.util.List;

public class JmlRapidPretty extends JmlConversionVisitor {

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

    public static String write(final JCTree tree, final boolean b,
            final String mName) {
        targetMethodName = mName;
        return write(tree, b);
    }

    public JmlRapidPretty(final Writer out, final boolean sourceOutput) {
        super(out, sourceOutput);
    }

    @Override
    public void visitJmlClassDecl(final JmlClassDecl that) {
        for (final JCTree jcTree : that.defs) {
            if (jcTree instanceof JmlTree.JmlMethodDecl) {
                ((JmlTree.JmlMethodDecl) jcTree).accept(this);
            }
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
                println();
                // TODO generate conditions (visit JmlSpecs$MethodSpecs)
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
        print("{");
        println();
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
                if (param.type instanceof Type.ArrayType) {
                    final Type.ArrayType arrayType = (Type.ArrayType) param.type;
                    print("const ");
                    printType(arrayType.elemtype);
                    print(" [] ");
                    print(param.getName().toString());
                    print(";");
                    println();
                    align();
                    /** print length variable for an array **/
                    print("const Int ");
                    print(param.getName().toString() + "length");
                    print(";");
                    println();
                } else {
                    print("const ");
                    printType(param.type);
                    print(" ");
                    print(param.getName().toString());
                    print(";");
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
            /** Add this variable name to the declared set */
            if (!vars.contains(that.name.toString())) {
                vars.add(that.name.toString());
            }
            printType(that.type);
            print(" ");
            print(that.name);
            print(" = ");
            print(that.init);
            print(";");
            println();
        } catch (final IOException e) {
            perr(that, e);
        }
    }

    @Override
    public void visitUnary(final JCUnary that) {
        try {
            print(that.arg.toString());
            print(" = ");
            print(that.arg.toString());
            if (that.getTag() == Tag.POSTINC || that.getTag() == Tag.PREINC) {
                print(" + ");
            } else if (that.getTag() == Tag.POSTDEC
                    || that.getTag() == Tag.PREDEC) {
                print(" - ");
            }
            print("1");
        } catch (final IOException e) {
            perr(that, e);
        }
    }

    @Override
    public void visitReturn(final JCReturn that) {}
}
