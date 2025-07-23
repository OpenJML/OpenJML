public class TestRange {
    
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
        //@ ghost \range r2 = \range.of(5,8);
        //@ ghost \range r3 = \range.of(5,9);
        //@ check r1 == r2;
        //@ check r1.hashCode() == r2.hashCode();
        //@ check \range.of(5,8,false).hashCode() == \range.of(5,9,true).hashCode();
        //+RAC@ show r1, r3.toString();
        try {
            //@ check r1.equals(null);
        } catch (Exception e) {
            //+RAC@ set System.out.println(e);
        }
    }
    
    //@ requires ii <= jj+1;
    public static void equality(int ii, int jj) {
        //@ ghost \bigint i = ii; ghost \bigint j = jj;
        //@ check i <= j + 1;
        //@ ghost var r = \range.of(i,j);
        //@ check \range.of(i,j).eq(r);
        //@ check \range.of(i,j+1).ne(r);
        //@ check \range.of(i,j,false) == \range.of(i,j+1,true);
        //@ check \range.of(i,j+1,true) == \range.of(i,j+1,true);
        //@ check \range.of(i,j,false) == \range.of(i,j,false);
        //@ check \range.of(i,j+1,true) == \range.of(i,j,false);
    }
    
    //@ requires i <= j+1;
    public static void equality2(int i, int j) {
        //@ ghost var r = \range.of(i,j);
        //@ check \range.of(i,j).eq(r);
        //@ check \range.of(i,j+1).ne(r);
    }
    
    public static void test() {
        //@ ghost \range r = \range.of(5,8);
        //@ check !r.hiIsExclusive;
    }
}