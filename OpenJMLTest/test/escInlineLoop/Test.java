import java.util.stream.Stream;
import org.jmlspecs.annotation.NonNull;
public class Test {
    
    static public int ii;
    static public int /*@ non_null */ [] arr = new int[5];
    
    //@ public normal_behavior
    //@ requires 0 <= ii < arr.length;
    //@ old int oldI = ii;
    //@ assignable ii, arr[oldI];
    //@ ensures arr[oldI] == v;
    //@ ensures ii == oldI + 1;
    static public void putAtI(int v) {
        arr[ii] = v;
        ii++;
    }
    
    public void m() {
        
        Stream<Integer> st = Stream.<Integer>of(1,2,3,4,5);
        //@ assert st.count() == 5;
        //@ assume arr.length == 5;
        
        ii = 0;
        //@ loop_invariant Test.ii == \count;
        //@ loop_invariant (\forall int j; 0 <= j < \count; arr[j] == st.values[j]);
        //@ loop_modifies Test.ii, Test.arr[*];
        //@ inlined_loop;
        st.forEachOrdered(v -> putAtI(v));
        //@ assert Test.ii == st.count();
        
        //@ assert arr[0] == 1;
        //@ assert arr[4] == 5;
    }
    
    public void q(Stream<@NonNull Integer> st) {
        //@ ghost var c = st.count();
        //@ assume c > 5;
        
        //@ assume \forall \bigint i; 0 <= i < c; st.values[i] != null && (int)st.values[i] == i+1;
        //@ assume Test.arr.length >= c >= 0;
        

        ii = 0;
        //@ loop_invariant Test.ii == \count;
        //@ loop_invariant (\forall int j; 0 <= j < \count; arr[j] == j+1);
        //@ loop_modifies Test.ii, Test.arr[*];
        //@ inlined_loop;
        st.forEachOrdered(v -> putAtI(v));
        //@ assert Test.ii == c;
        
        //@ assert (\forall int j; 0 <= j < c; arr[j] == j+1);
        //@ assert arr[0] == 1;
        //@ assert arr[4] == 5;
    }
}

class TestB {
    
    static public int ii;
    static public int[] arr = new int[5];
    
    //@ public normal_behavior
    //@ requires 0 <= ii < arr.length;
    //@ old int oldI = ii;
    //@ assignable ii, arr[ii];
    //@ ensures arr[oldI] == v;
    //@ ensures ii == oldI + 1;
    static public void putAtI(int v) {
        arr[ii] = v;
        ii++;
    }
    
    public void mq() {
        
        Stream<Integer> st = Stream.<Integer>of(1,2,3,4,5);
        //@ assert st.count() == 5;
        //@ assume arr.length == 5;
        
        ii = 0;
        //@ loop_invariant ii == \count;
        //@ loop_invariant (\forall int j; 0 <= j < \count; arr[j] == j+1);
        //@ loop_modifies ii, arr[*];
        //@ inlined_loop;
        st.forEachOrdered(v -> putAtI(v));
        //@ assert TestB.ii == st.count();
        
        //@ assert arr[0] == 1;
        //@ assert arr[4] == 5;
        //@ assert (\forall int j; j>=0 && j<arr.length; arr[j] == j+1);
    }
}

class TestA {

    public Stream<Integer> st = Stream.</*@ non_null*/ Integer>of(1,2,3,4,5);
    public int[] arr = new int[5];

    public int ii;

    //@ requires arrx != null && 0 <= ii < arrx.length;
    //@ old int oldI = ii;
    //@ assignable ii, arrx[oldI];
    //@ ensures arrx[oldI] == (int)v;
    //@ ensures ii == oldI + 1;
    public void putAtI(int[] arrx, /*@ non_null*/ Integer v) {
        arrx[ii] = (int)v;
        ii++;
    }

    //@ requires st.count() == 5;
    //@ requires arr != null && arr.length == 5;
    public void m() {
        //@ ghost var c = st.count();
        //@ assert c == 5;
        //@ assume \forall \bigint i; 0 <= i < c; st.values[i] != null && (int)st.values[i] == i+1;

        ii = 0;
        var arrz = arr;
        var local = this;
        //@ loop_invariant ii == \count;
        //@ loop_invariant (\forall int j; 0 <= j < \count; arrz[j] == st.values[j]);
        //@ loop_modifies local.ii, arrz[*];
        //@ inlined_loop;
        st.forEachOrdered(v -> putAtI(arrz,v));

        //@ show ii, st.values.length, st.count(); 
        //@ assert ii == st.count();
//
//      //@ assert arr[0] == 1;
//      //@ assert arr[4] == 5;
//      //@ assert (\forall int j; j>=0 && j<arr.length; arr[j] == j+1);
}
}