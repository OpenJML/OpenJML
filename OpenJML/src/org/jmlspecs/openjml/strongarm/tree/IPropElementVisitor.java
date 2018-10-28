package org.jmlspecs.openjml.strongarm.tree;

public interface IPropElementVisitor {
    public void visitAnd(And p);
    public void visitOr(Or p);
    public void visitProp(Prop p);

}
