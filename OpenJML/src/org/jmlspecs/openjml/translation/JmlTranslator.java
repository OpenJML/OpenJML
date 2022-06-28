package org.jmlspecs.openjml.translation;

import java.io.IOException;
import java.io.Writer;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.Maker;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCPrimitiveTypeTree;
import com.sun.tools.javac.util.List;

public abstract class JmlTranslator extends JmlPretty {
    public static String                 targetMethodName = null;

    /** Tree maker **/
    public static Maker                  maker;

    /** all identifiers **/
    protected static Set<String>         allIdents        = new HashSet<>();

    /** variable name set **/
    protected static Set<String>         vars             = new HashSet<>();

    /** constants name set **/
    protected static Set<String>         consts           = new HashSet<>();

    /** return value **/
    protected static JCExpression        returnExpr       = null;

    /**
     * variable map to avoid using the same variable names across Rapid and
     * SMT-LIB
     **/
    protected static Map<String, String> varMap           = new HashMap<>();

    public JmlTranslator(final Writer out, final boolean sourceOutput) {
        super(out, sourceOutput);
    }

    protected void printlnAndAlign() throws IOException {
        println();
        align();
    }

    protected void printlnAndUndent() throws IOException {
        println();
        undent();
        align();
    }

    protected void println(final Object s) throws IOException {
        print(s);
        println();
    }

    /** Avoid printing package decl **/
    @Override
    public void visitJmlCompilationUnit(final JmlCompilationUnit tree) {
        try {
            for (List<JCTree> l = tree.defs; l.nonEmpty(); l = l.tail) {
                if (l.head.getTag() == JCTree.Tag.IMPORT) {
                } else {
                    printStat(l.head);
                }
            }
            if (!inSequence && tree.specsCompilationUnit != null
                    && !useJMLComments) {
                final boolean prevInSequence = inSequence; // should always be
                                                           // false, since we
                                                           // don't call this
                                                           // more than one
                                                           // level deep
                inSequence = true;
                try {
                    println();
                    print("// Specifications: ");
                    print(tree.specsCompilationUnit.sourcefile.getName());
                    println();
                    final JmlCompilationUnit jcu = tree.specsCompilationUnit;
                    print("// Specification file: " + jcu.sourcefile.getName());
                    println();
                    jcu.accept(this);
                    println();
                } finally {
                    inSequence = prevInSequence;
                }
            }
        } catch (final IOException e) {
            perr(tree, e);
        }
    }

    protected void printVarName(final String name) throws IOException {
        if (varMap.containsKey(name)) {
            print(varMap.get(name));
        } else {
            print(name);
        }
    }

    @Override
    public void visitTypeIdent(final JCPrimitiveTypeTree tree) {
        try {
            switch (tree.typetag) {
                case BYTE:
                    print("byte");
                    break;
                case CHAR:
                    print("char");
                    break;
                case SHORT:
                    print("short");
                    break;
                case INT:
                    print("Int");
                    break;
                case LONG:
                    print("long");
                    break;
                case FLOAT:
                    print("float");
                    break;
                case DOUBLE:
                    print("double");
                    break;
                case BOOLEAN:
                    print("Bool");
                    break;
                case VOID:
                    print("void");
                    break;
                default:
                    print("error");
                    break;
            }
        } catch (final IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
