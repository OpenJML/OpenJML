import java.util.Arrays;
public class Test
{
    //@ assigns \everything;
    public static void test(int arr[], int e) {
        if (arr != null && arr.length > 0) arr[0] = e;
    }

    public static void test2(int[] a) {
        if (a == null) return;
        //@ assert a != null;
        int[] a1 = a.clone();
        int[] a2 = a.clone();
        //@ assert Arrays.equals(a1, a2); // OK
        test(a1, 10);
        test(a2, 20);
        //@ assert Arrays.equals(a1, a2); // ERROR
    }
    
    //@ requires a1 != a2;
    public static void test3(int[] a1, int[] a2) {
        //@ assume Arrays.equals(a1, a2);
        test(a1, 10);
        test(a2, 20);
        //@ assert Arrays.equals(a1, a2); // ERROR
    }
}

class TestB
{
    // @ ensures Arrays.equals(arr, \old(arr));  // Incorrect spec - the old does not mean that array elements are evaluated in prestate
    //@ ensures \forall int i; 0 <= i < arr.length; arr[i] == \old(arr[i]);
    public static int test(int arr[]) {
        int dummy = 10;
        return dummy;
    }

    public static void test2(int[] a) {
        if (a == null) return;
        //@ assert a != null;
        int[] a1 = a.clone();
        int[] a2 = a.clone();
        //@ assert Arrays.equals(a1, a2);
        test(a1);
        test(a2);
        //@ assert Arrays.equals(a1, a2); //  ERROR because of no frame clause on test()
    }
}

class TestC
{
    //@ assigns \nothing;
    // @ ensures Arrays.equals(arr, \old(arr));  // Incorrect spec - the old does not mean that array elements are evaluated in prestate
    //@ ensures \forall int i; 0 <= i < arr.length; arr[i] == \old(arr[i]);
    public static int test(int arr[]) {
        int dummy = 10;
        return dummy;
    }

    public static void test2(int[] a) {
        if (a == null) return;
        //@ assert a != null;
        int[] a1 = a.clone();
        int[] a2 = a.clone();
        //@ assert Arrays.equals(a1, a2);
        test(a1);
        test(a2);
        //@ assert Arrays.equals(a1, a2); // OK
    }
}
