package org.jmlspecs.openjml.strongarm;

import com.sun.tools.javac.tree.JCTree.JCExpression;

public class And<T extends JCExpression> extends Prop<T> {

    public Prop<T> p1;
    public Prop<T> p2;
    
    public And(Prop<T> p1, Prop<T> p2){
        this.p1 = p1;
        this.p2 = p2;
    }
  
    public static <E extends JCExpression> And<E> of(Prop<E> p1, Prop<E> p2){
        return new And<E>(p1, p1);
    }
    
}
