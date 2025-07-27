import java.util.*;
public class Test {
    
    public static void main(String ... args) {
        // NOTE: subtype relationships among type literals are constant-folded
        //@ check \type(Integer) == \type(Integer);
        //@ check \type(Integer) != \type(Boolean);
        //@ set eqTests(\type(Integer), \type(Boolean));
        subtypeTests();
        //-RAC@ check \type(List<Integer>) == \TYPEof(java.util.List.class, \type(Integer));
        //@ check \erasure(\type(Integer)) == Integer.class;
        //@ check \type(List<Integer>) != \type(List<Boolean>);
        elemtypeTests();
        typeargTests();
        //@ set m(\type(Integer));
        //@ set m(\type(Integer[]));
        //@ set m(\type(int));
        //@ set mc(int.class);
        //@ set mc(Integer.class);
        //@ set mc(Integer[].class);
        //@ check \erasure(\type(List<Integer>)) == List.class;
        Object o = Integer.valueOf(0);
        //@ check \typeof(o) == \type(Integer);
        o = new Integer[0];
        //@ check \typeof(o) == \type(Integer[]);
        o = new java.util.LinkedList<Boolean>();
        //@ check \typeof(o) == \type(java.util.LinkedList<Boolean>);
        int i = 0; 
        //@ check \typeof(i) == \type(int);
        showTest();
        errors1();
        errors2();
        errors3();
        errors4();
        errors5();
        errors6();
        numargTests();
        misc();
    }
    
    public static void errors1() {
        try {
            //@ ghost var c = \typearg1(\type(Integer)); // ERROR in RAC, undefined in ESC
        } catch (Exception e) {
            //-ESC@ set System.out.println(e);
        }
    }
    
    public static void errors2() {
        try {
            //@ ghost var c = \typearg(\type(Integer), 2); // ERROR in RAC, undefined in ESC
        } catch (Exception e) {
            //-ESC@ set System.out.println(e);
        }
    }
    
    public static void errors3() {
        try {
            //@ ghost var c = \typearg(\type(List<Integer>), 2); // ERROR in RAC, undefined in ESC
        } catch (Exception e) {
            //-ESC@ set System.out.println(e);
        }
    }
    
    public static void errors4() {
        try {
            //@ ghost var c = \elemtype(\type(Integer)); // ERROR
        } catch (Exception e) {
            //-ESC@ set System.out.println(e);
        }
    }
    
    public static void errors5() {
        try {
            //@ check \type(Integer).equals(null); // ERROR
        } catch (Exception e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors6() {
        try {
            var o = new Object();
            //@ check \type(Integer).equals(o); // ERROR
        } catch (Exception e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors7() {
        /*@ nullable */ Class<?> c = null;
        //@ ghost \TYPE t = \TYPE.of(c);
    }
    
    /*@
    model public static void eqTests(\TYPE t, \TYPE tt) {
        check t.eq(tt) <==> (t == tt);
        check t.ne(tt) <==> (t != tt);
        check t.isSubtypeOf(tt) <==> (t <:= tt);
        check t.isProperSubtypeOf(tt) <==> (t <: tt);
        check \isarray(\arraytype(t));
        check \elemtype(\arraytype(t)) == t;
    }
    
    model public static void m(\TYPE t) {
        check \isarray(\arraytype(t));
        check \elemtype(\arraytype(t)) == t;
        check t.erasure() == \erasure(t);
        check t.isArray() == \isarray(t);
        check \isarray(t) ==> (t.getComponentType() == \elemtype(t));
    }
    
    */
    
    public static void subtypeTests() {
        //@ check \type(Integer) <: \type(Object);
        //@ check !(\type(Integer) <:= \type(Boolean));
        //@ check \type(Integer) <:= \type(Integer);
        //@ check !(\type(Integer) <: \type(Integer));
        //@ check \type(Integer) == \TYPE.of(Integer.class);
        //@ check \type(LinkedList<Integer>) <: \type(List<Integer>) ;
        //@ check !(\type(ArrayList<Integer>) <: \type(List<Boolean>) );
    }
    
    public static void elemtypeTests() {
        //@ check \isarray(\type(Integer[]));
        //@ check \isarray(\type(List<Integer>[]));
        //@ check !\isarray(\type(int));
        //@ check \elemtype(\type(Integer[])) == \type(Integer);
        //@ check \elemtype(\type(List<Integer>[])) == \type(List<Integer>);
        //@ check \arraytype(\type(Integer)) == \type(Integer[]);
    }
    
    public static void showTest() {
        //-ESC@ show \type(int), \type(Integer), \type(List<Integer>), \type(int[]), \type(Integer[]), \type(List<Integer>[]), \arraytype(\type(List<Integer>));
        //-ESC@ show \type(int).toString(), \type(Integer).toString(), \type(List<Integer>).toString();
        //-ESC@ show \arraytype(\type(Integer)) , \type(Integer[]), \type(int), \type(List<Integer>), \type(List<Integer>[][]);
    }
    
    public static void mc(Class<?> c) {
        //@ check \erasure(\TYPE.of(c)) == c;
    }
    
    public static void typeargTests() {
        //@ check \typearg1(\type(List<Boolean>)) == \type(Boolean);
        //@ check \typearg(\type(List<Boolean>), 1) == \type(Boolean);
        //@ check \typearg1(\type(Map<Integer,Boolean>)) == \type(Integer);
        //@ check \typearg2(\type(Map<Integer,Boolean>)) == \type(Boolean);
        //@ check \typearg(\type(Map<Integer,Boolean>), 2) == \type(Boolean);        
    }
    
    public static void numargTests() {
        //@ check \type(Boolean).numargs() == 0;
        //@ check \type(List<Integer>).numargs() == 1;
        //@ check \type(Map<Integer,Boolean>).numargs() == 2;
        //@ check \TYPE.of(Boolean.class).numargs() == 0;
        //@ check \TYPE.of(List.class, \type(Boolean)).numargs() == 1;
        //@ check \TYPE.of(Map.class, \type(Boolean), \type(Boolean)).numargs() == 2;
        //-RAC@ check \TYPE.of(List.class, \type(Boolean)).numargs == 1;
        //-RAC@ check \TYPE.of(Map.class, \type(Boolean), \type(Boolean)).numargs == 2;
    }
    
    public static void misc() {
        //@ check \type(Boolean).hashCode() == \TYPE.of(Boolean.class).hashCode();
        //@ check \type(List<Integer>).hashCode() == \TYPE.of(List.class, \TYPE.of(Integer.class)).hashCode();
        //@ ghost \TYPE t = \TYPE.empty();
        try {
        //-ESC@ set t = \TYPE.of(Boolean.class, null); // Treats as a null array  // FIXME - crashes in ESC
        } catch (NullPointerException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    
//    public static void test() {
//        // @ check \type(List<Integer>) == \TYPEof(java.util.List.class, \type(Integer));
//        //-RAC-ESC@ check \type(List<Integer>[]) == \TYPEof(java.util.List.class, \type(Integer));
//    }
        

}

// FIXME
// NOTE: Cannot apply .class to a parameterized type name, as in List<Integer>.class
// Loss of type arguments when writing \type(List<Boolean>[])
// typeargs is no yet implemented
// RAC - two argument \TYPEof
// settle wheteher one can apply \erasure to Class values
// \TYPE.of is not working for ESC or RAC; \TYPEof does
// When using \TYPE.of there are duplicate statements in the translated program

