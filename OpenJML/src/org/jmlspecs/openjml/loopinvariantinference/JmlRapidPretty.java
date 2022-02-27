/**
 * This visitor converts java code to Rapid syntax
 * @author Kohei Koja
 */
package org.jmlspecs.openjml.loopinvariantinference;

import static com.sun.tools.javac.tree.JCTree.Tag.PARENS;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.HashMap;
import java.util.Map;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.Pretty.UncheckedIOException;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;

public class JmlRapidPretty extends JmlConversionVisitor {

    /** Parameters of the target function **/
    private List<JCVariableDecl> params = null;

    static public @NonNull String write(@NonNull JCTree tree, boolean source) {
        StringWriter sw = new StringWriter();
        JmlRapidPretty p = new JmlRapidPretty(sw,source);
        p.width = 2;
        if(tree!=null)
            tree.accept(p);
        return sw.toString();
    }

    public static String write(JCTree tree, boolean b, String mName) {
        targetMethodName = mName;
        return write(tree, b);
    }

    public JmlRapidPretty(Writer out, boolean sourceOutput) {
        super(out, sourceOutput);
    }

    @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        for (JCTree jcTree : that.defs) {
            if (jcTree instanceof JmlTree.JmlMethodDecl) {
                ((JmlTree.JmlMethodDecl) jcTree).accept(this);
            }
        }
    }
    
    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
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
            } catch (IOException e) { perr(that,e); }
        }
    }
    
    @Override
    public void visitJmlBlock(JmlBlock that) {
        
        if(that.type==null && specOnly){
            return;
        }
        
        try {
            printFlags(that.flags);
            printBlock(that.stats);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
    
    /** Print a block.
     */
    @Override
    public void printBlock(List<? extends JCTree> stats) throws IOException {
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
    
    /** If statement has to have else block
     */
    @Override
    public void visitIf(JCIf tree) {
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
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private void printParams(List<JCVariableDecl> params) {
        for (JCVariableDecl param : params) {
            try {
                align();
                if (param.type instanceof Type.ArrayType) {
                    Type.ArrayType arrayType = (Type.ArrayType) param.type;
                    print("const ");
                    printType(arrayType.elemtype);
                    print(" [] ");
                    print(param.getName().toString());
                    print(";"); println(); align();
                    /** print length variable for an array **/
                    print("const Int ");
                    print(param.getName().toString() + "length");
                    print(";"); println();
                } else {
                    printType(param.type);
                    print(" ");
                    print(param.getName().toString());
                    print(";"); println();
                }
            } catch (IOException e) { perr(param,e); }
        }
    }

    @Override
    public void visitJmlVariableDecl(JmlVariableDecl that) {
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
            print(";"); println();
        } catch (IOException e) { perr(that,e); }
    }

    @Override
    public void visitUnary(JCUnary that) {
        try {
            print(that.arg.toString());
            print(" = ");
            print(that.arg.toString());
            if (that.getTag() == Tag.POSTINC || that.getTag() == Tag.PREINC) {
                print(" + ");
            } else if (that.getTag() == Tag.POSTDEC || that.getTag() == Tag.PREDEC) {
                print(" - ");
            }
            print("1");
        } catch (IOException e) { perr(that,e); }
    }

    @Override
    public void visitReturn(JCReturn that) {
    }
}
