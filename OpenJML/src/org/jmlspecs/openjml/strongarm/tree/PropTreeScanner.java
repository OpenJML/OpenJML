package org.jmlspecs.openjml.strongarm.tree;

public class PropTreeScanner implements IPropElementVisitor {

    public void scan(Prop tree) {
        if(tree!=null) tree.accept(this);
    }

    
    @Override
    public void visitAnd(And p) {
        scan(p.p1);
        scan(p.p2);
    }

    @Override
    public void visitOr(Or p) {
        scan(p.p1);
        scan(p.p2);        
    }

    @Override
    public void visitProp(Prop p) {
        scan(p);
    }

    

}
