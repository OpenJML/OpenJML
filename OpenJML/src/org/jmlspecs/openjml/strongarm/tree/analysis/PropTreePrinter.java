package org.jmlspecs.openjml.strongarm.tree.analysis;

import org.jmlspecs.openjml.strongarm.tree.And;
import org.jmlspecs.openjml.strongarm.tree.Or;
import org.jmlspecs.openjml.strongarm.tree.Prop;
import org.jmlspecs.openjml.strongarm.tree.PropTreeScanner;

public class PropTreePrinter extends PropTreeScanner {

    


    @Override
    public void visitAnd(And p) {
        System.out.print("(");
        scan(p.p1);
        System.out.print("&");
        scan(p.p2);
        System.out.print(")");
    }

    @Override
    public void visitOr(Or p) {
        System.out.print("(");
        scan(p.p1);
        System.out.print("|");
        scan(p.p2);
        System.out.print(")");
    }

    @Override
    public void visitProp(Prop p) {
        System.out.print(p.p.toString());
    }

    

}
