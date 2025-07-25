public class Trange {
    
    public static void main(String... args) {
        //@ check \range.empty().isEmpty();
        //@ ghost var r = \range.of(5,8);
        //@ check r.lo <= r.hi+1;
        //@ check !r.hiIsExclusive;
        //@ check !r.isEmpty();
        //@ check r.lo == 5;
        //@ check r.hi == 8;
        //@ check \range.of(\bigint.of(5),\bigint.of(8)).lo == 5;
        //@ check r == \range.of(\bigint.of(5),\bigint.of(8));
        //@ check r != \range.of(5,9);
        //@ check \range.of(6,9,true).hiIsExclusive;
        equality(4,9);
        misc();
    }
    
    public static void misc() {
        //@ ghost \range r1 = \range.of(5,8);
        //@ ghost var r2 = \range.of(5,8);
        //@ ghost \range r3 = \range.of(5,9);
        //@ check r1 == r2;
        //@ check r1.hashCode() == r2.hashCode(); // OK
        //@ check \range.of(5,8,false).hashCode() == \range.of(5,9,true).hashCode(); // SHOULD BE OK
        //+RAC@ show r1, r3.toString();
        try {
            //@ check r1.equals(null); // ERROR
        } catch (Exception e) {
            //+RAC@ set System.out.println(e);
        }
    }
    
    //@ requires ii <= jj+1;
    public static void equality(int ii, int jj) {
        //@ ghost \bigint i = ii; ghost \bigint j = jj;
        //@ check i <= j + 1;
        //@ ghost \range r = \range.of(i,j);
        //@ check \range.of(i,j).eq(r);  //OK
        //@ check \range.of(i,j+1).ne(r); // OK
        //@ check \range.of(i,j,false) == \range.of(i,j+1,true); // OK
        //@ check \range.of(i,j+1,true) == \range.of(i,j+1,true);  // OK
        //@ check \range.of(i,j,false) == \range.of(i,j,false); // OK
        //@ check \range.of(i,j+1,true) == \range.of(i,j,false); // OK
    }
    
    //@ requires i <= j+1;
    public static void equality2(int i, int j) {
        //@ ghost \range r = \range.of(i,j);
        //@ check \range.of(i,j).eq(r);
        //@ check \range.of(i,j+1).ne(r);
    }
    
    public static void equality3() {
        // Checks difference between assignment and binary equality
        //@ ghost \range rrr = \range.of(5,8);
        //@ check !rrr.hiIsExclusive;
        //@ check rrr == rrr;
    }
    
    public static void dotdot() {
        //@ ghost var r = 2 ..3 ;
        //@ set var rr = r;
        //@ set var k = r.lo;
        //@ check k == 2;
        //@ check r.hi == 3;
        //@ check (2 .. 3) == (2 .. 3);
        //@ check !((2 .. 3) != (2 .. 3));
    }
}