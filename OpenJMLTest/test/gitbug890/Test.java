import java.util.Arrays;
public class Test {
    //@ requires arr != null;
    //@ assigns arr[*];
    //@ ensures arr == \old(arr);
    //@ ensures \forall int i; 0 <= i < arr.length; arr[i] == 0;
    public static void setZero(int[] arr) {
        //@ maintaining 0 <= i <= arr.length;
        //@ maintaining \forall int j; 0 <= j < i; arr[j] == 0;
        //@ loop_writes i, arr[*];
        //@ decreases arr.length - i;
        for (int i = 0; i < arr.length; ++i) {
            arr[i] = 0;
        }
    }

    //@ requires arr != null;
    //@ assigns arr[*];
    //@ ensures arr == \old(arr);
    //@ ensures \forall int i; 0 <= i < arr.length; arr[i] == 1;
    public static void setOne(int[] arr) {
        //@ maintaining 0 <= i <= arr.length;
        //@ maintaining \forall int j; 0 <= j < i; arr[j] == 1;
        //@ loop_writes i, arr[*];
        //@ decreases arr.length - i;
        for (int i = 0; i < arr.length; ++i) {
            arr[i] = 1;
        }
    }

    //@ requires arr != null;
    //@ model public static void model_test(int[] arr) {
    //@     int[] c1 = arr.clone();
    //@     int[] c2 = arr.clone();
    //@     assert c1 != c2;
    //@     setZero(c1);
    //@     setOne(c2);
    //@     ghost boolean b = Arrays.equals(c1, c2);
    //@     assert b; // Arrays.equals(c1, c2);
    // @     assert arr.length == 0 <==> Arrays.equals(c1, c2);
    //@     reachable;
    //@ }
    
    //@ requires arr != null;
    //@ model public static void mm(int[] arr, int[] c2) {
    //@     assume arr instanceof Cloneable; assert arr instanceof int[];
    //@     int[] c1 = arr.clone();
    //@     c2 = arr.clone();
    //@     reachable;
    //@     assert c1 != c2;
    //@     assume c1.length  > 0;
    //@     assume c1.length == c2.length;
    // @     setZero(c1);
    // @     setOne(c2);
    // @     assert \forall int i; 0 <= i < c1.length; c1[i] == 0;
    // @     assert \forall int i; 0 <= i < c2.length; c2[i] == 1;
    //@     reachable;
    //@     assert Arrays.equals(c1,c2);
    //@     reachable;
    //@ }

    //@ requires arr != null; //requires arr.length == 1;
    //@ ensures \result == (arr.length == 0);
    public static boolean test(int[] arr) {
        //@     assume arr instanceof Cloneable;
        int[] c1 = arr.clone();
        int[] c2 = arr.clone();
        setZero(c1);
        setOne(c2);
        return Arrays.equals(c1, c2);
    }
}
