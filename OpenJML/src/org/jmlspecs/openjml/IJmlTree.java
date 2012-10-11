package org.jmlspecs.openjml;

import com.sun.source.tree.*;
import com.sun.tools.javac.tree.JCTree.Visitor;

// TODO: This interface needs completing, documentation, and to be used throughout.

public interface IJmlTree {
    
    public static interface IJmlCompilationUnit extends CompilationUnitTree {
        // TODO: methods for JML fields
        public void accept(Visitor v);
        public <R,D> R accept(TreeVisitor<R,D> v, D d);
    }
    
    public static interface IJmlBinary extends BinaryTree {
        public ExpressionTree getLeftOperand();
        public JmlToken getOp();
        public ExpressionTree getRightOperand();
    }


}