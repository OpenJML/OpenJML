package org.jmlspecs.openjml.strongarm;

import com.sun.tools.javac.tree.JCTree.JCExpression;

public class Or<T extends JCExpression> extends Prop<T> {

    public Prop<T> p1;
    public Prop<T> p2;
    
    public Or(Prop<T> p1, Prop<T> p2){
        this.p1 = p1;
        this.p2 = p2;
    }
  
    public static <E extends JCExpression> Or<E> of(Prop<E> p1, Prop<E> p2){
        return new Or<E>(p1, p1);
    }
    
}
