package org.jmlspecs.openjml;

import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import org.jmlspecs.openjml.ext.Arithmetic.Mode;

import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCUnary;

public interface IArithmeticMode {
    //@ pure
    public Mode mode();
 
    public JCExpression rewriteUnary(JmlAssertionAdder rewriter, JCUnary that);
    public JCExpression rewriteBinary(JmlAssertionAdder rewriter, JCBinary that, boolean alreadyConverted);

}