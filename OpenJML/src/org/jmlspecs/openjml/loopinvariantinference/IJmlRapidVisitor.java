package org.jmlspecs.openjml.loopinvariantinference;

import org.jmlspecs.openjml.loopinvariantinference.JmlRapidTree.*;
import org.jmlspecs.openjml.vistors.IJmlVisitor;

import com.sun.tools.javac.tree.JCTree.JCReturn;

public interface IJmlRapidVisitor extends IJmlVisitor {
    public void visitJmlReturn(JCReturn that);

    public void visitJmlRapidParen(JmlRapidParens that);

    public void visitJmlRapidBinary(JmlRapidBinary that);

    public void visitJmlRapidFieldAccess(JmlRapidFieldAccess that);

    public void visitJmlRapidUnary(JmlRapidUnary that);

    public void visitJmlRapidReturn(JmlRapidReturn that);
}
