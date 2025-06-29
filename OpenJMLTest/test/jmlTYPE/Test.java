import java.util.*;
public class Test {
    
    public static void main(String ... args) {
        // NOTE: subtype relationships among type literals are constant-folded
        //-ESC@ show \type(int), \type(Integer), \type(List<Integer>), \type(int[]), \type(Integer[]), \type(List<Integer>[]), \arraytype(\type(List<Integer>));
        //-ESC@ show \type(int).toString(), \type(Integer).toString(), \type(List<Integer>).toString();
        //@ check \type(Integer) != \type(Boolean);
        //@ check \type(Integer) <: \type(Object);
        //@ check !(\type(Integer) <:= \type(Boolean));
        //@ check \type(Integer) <:= \type(Integer);
        //@ check !(\type(Integer) <: \type(Integer));
        //@ check \type(Integer) == \TYPE.of(Integer.class);
        //-RAC@ check \type(List<Integer>) == \TYPEof(java.util.List.class, \type(Integer));
        //@ check \erasure(\type(Integer)) == Integer.class;
        //@ check \isarray(\type(Integer[]));
        //@ check \isarray(\type(List<Integer>[]));
        //@ check !\isarray(\type(int));
        //@ check \elemtype(\type(Integer[])) == \type(Integer);
        //@ check \elemtype(\type(List<Integer>[])) == \type(List<Integer>);
        //-ESC@ show \arraytype(\type(Integer)) , \type(Integer[]);
        //@ check \arraytype(\type(Integer)) == \type(Integer[]);
        //@ check \type(List<Integer>) != \type(List<Boolean>);
        //@ check \typearg0(\type(List<Boolean>)) == \type(Boolean);
        //@ check \typearg(\type(List<Boolean>), 0) == \type(Boolean);
        //@ check \typearg0(\type(Map<Integer,Boolean>)) == \type(Integer);
        //@ check \typearg(\type(Map<Integer,Boolean>), 1) == \type(Boolean);
        //@ set m(\type(Integer));
        //@ set m(\type(Integer[]));
        //@ set m(\type(int));
        //@ set mc(int.class);
        //@ set mc(Integer.class);
        //@ set mc(Integer[].class);
        Object o = Integer.valueOf(0);
        //@ check \typeof(o) == \type(Integer);
        o = new Integer[0];
        //@ check \typeof(o) == \type(Integer[]);
        o = new java.util.LinkedList<Boolean>();
        //@ check \typeof(o) == \type(java.util.LinkedList<Boolean>);
//        int i; 
//        //@ check \typeof(i) == \type(int);
    }
    
    public void test() {
        // @ check \type(List<Integer>) == \TYPEof(java.util.List.class, \type(Integer));
        //-RAC-ESC@ check \type(List<Integer>[]) == \TYPEof(java.util.List.class, \type(Integer));
    }
        
    /*@
    model public static void m(\TYPE t) {
        check \isarray(\arraytype(t));
        check \elemtype(\arraytype(t)) == t;
        check t.erasure() == \erasure(t);
        check t.isArray() == \isarray(t);
        check \isarray(t) ==> (t.getComponentType() == \elemtype(t));
    }
    
    model public static void mc(Class<?> c) {
        //show c;
        check \erasure(\TYPE.of(c)) == c;
    }
    */
}

// FIXME
// NOTE: Cannot apply .class to a parameterized type name, as in List<Integer>.class
// Loss of type arguments when writing \type(List<Boolean>[])
// typeargs is no yet implemented
// need tests of typearg0, \typearg(t,n)
// ESC - show statements and toString()
// RAC - two argument \TYPEof
// settle wheteher one can apply \erasure to Class values
// \TYPE.of is not working for ESC or RAC; \TYPEof does
// When using \TYPE.of there are duplicate statements in the translated program
// Fix <:= in escgeneric.testGenericType2

