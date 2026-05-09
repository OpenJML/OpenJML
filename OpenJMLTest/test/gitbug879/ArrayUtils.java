public class ArrayUtils {
    //@ ensures 1 == \old(a[5 - 1]);
    void f(int[] a) {
    }
    
    public static void main(String... args) {
        var a = new int[10];
        new ArrayUtils().f(a);
    }
}
