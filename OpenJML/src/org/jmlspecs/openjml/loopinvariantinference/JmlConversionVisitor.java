package org.jmlspecs.openjml.loopinvariantinference;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.Writer;
import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.util.List;

public abstract class JmlConversionVisitor extends JmlPretty {
    protected static String targetMethodName = null;
    
    /** variable name set **/
    protected static Set<String> vars = new HashSet<>();

    public JmlConversionVisitor(Writer out, boolean sourceOutput) {
        super(out, sourceOutput);
    }

    /** Avoid printing package decl **/
    @Override
    public void visitJmlCompilationUnit(JmlCompilationUnit tree) {
        try {
            for (List<JCTree> l = tree.defs; l.nonEmpty(); l = l.tail) {
                if (l.head.getTag() == JCTree.Tag.IMPORT) {
                } else {
                    printStat(l.head);
                }
            }
            if (!inSequence && tree.specsCompilationUnit != null && !useJMLComments) {
                boolean prevInSequence = inSequence; // should always be false, since we don't call this more than one level deep
                inSequence = true;
                try {
                    println();
                    print("// Specifications: ");
                    print(tree.specsCompilationUnit.sourcefile.getName());
                    println();
                    JmlCompilationUnit jcu = tree.specsCompilationUnit;
                    print("// Specification file: " + jcu.sourcefile.getName()); 
                    println();
                    jcu.accept(this);
                    println();
                } finally {
                    inSequence = prevInSequence;
                }
            }
        } catch (IOException e) {
            perr(tree,e);
        }
    }

    @Override
    public void visitSelect(JCFieldAccess that) {
        try {
            print(that.selected.toString() + that.name.toString());
        } catch (IOException e) { perr(that, e); }
    }

    protected void printType(Type elemtype) throws IOException {
        if (elemtype instanceof Type.JCPrimitiveType) {
             String typeName = ((Type.JCPrimitiveType)elemtype).toString();
             if (typeName.equals("int")) {
                 print("Int");
             } else if (typeName.equals("boolean")) {
                 print("Bool");
             } else {
                 // TODO error handling
             }
        } else {
            // TODO error handling
        }
    }
    
}
