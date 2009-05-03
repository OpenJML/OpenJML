// This class tests that jmldoc knonws how to print all kinds of expressions

public class PP {
    
    int i;
    boolean b;
    Object o;
    int a[] = new int[10];
    
    //@ pure
    int m() { return 0; }
    
    //@ pure
    int mq(int a, boolean b, Object o) { return 0; }
    
    //@ invariant i + 2 * 3 - 4 / 5 + 6 % i + (i << 5) + (i >> 6) + (i >>> i) == -10;
    //@ invariant i > 0 && i < 0 && i == 0 && (i <= +10 ? i >= 0 : i != 0);
    //@ invariant b || !b && (b ==> b) && ( b <==> b ) && ( b <=!=> b ) && (b <== b);
    //@ invariant (i & 1) + (i ^ 1) + (i | 1) + (~i);
    
    //@ invariant \type(int) <: \typeof(o);
    //@ invariant \type(int) <#= \typeof(o);
    //@ invariant \type(int) <# \typeof(o);
    //@ invariant o instanceof java.lang.String;
    
    //@ invariant true && false && (i == 10.0) && (i < -10e4) && (i > +.4e+5);
    //@ invariant "asd" != (Object)null && 'c' != 'd' && 'a' != '\045' && "45" != "\n\"'\034";
    //@ invariant (int)9 == 9 && (char)3 == 'd' && (float)4 == (double)5 && (short)1 == (byte)(-1) && (long)-13 == -12;
    
    //@ invariant (new int[]{1,2,3}).length == 3 && (new int[]{1,2,3})[0] == 1 && a[3] = 6;
    //@ invariant (new PP()).i == 0;
    //@ invariant (new PP() { int m() { return 5; } }) != null;
    
    //@ invariant (\forall int i; i != 0) && (\forall int k; k > 0; k >-1);
    //@ invariant (\exists int i; i != 0) && (\exists int k; k > 0; k >-1);
    //@ invariant (\num_of int i; i == 0) && (\num_of int k; k > 0; k >-1);
    //@ invariant (\max int i; i>0 && i<10; i ) && (\min int i; i>0 && i<10; i );
    //@ invariant (\sum int i; i>0 && i<10; i ) && (\product int i; i>0 && i<10; i );
    //@ invariant (* informal predicate *) && false && m() == 0 && mq(1,false,new Object());
    
    //@ constraint i >= \old(i);
    
    //@ ensures \result > 0 && ! \nonnullelements(a) && \elemtype(\typeof(a)) == \type(int);
    //@ ensures \duration(m()) > 0 && \space(PP) > 0 && \working_space(PP) > 0;
    //@ ensures \fresh(a);
    //@ ensures \max(\lockset) == a;
    int mm() { return 3; }
    
    // TODO:  .this .class this .super .new-expr
    // TODO: not-assigned not-modified only-accessed only-assigned only-called only-captured
    // TODO:  reach  is-initialized invariant-for lblpos lblneg
    // CANNOT DO: += -= *= /= %= ^= |= &= <<= >>= >>>= = ++ --
    
    // TODO: all kinds of clauses
    // TODO: visibility attributes on clauses, long lines
}