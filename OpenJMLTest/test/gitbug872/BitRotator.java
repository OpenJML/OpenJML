public class BitRotator {
    /*@ ensures \result == 50 >>> (32-4); @*/
    public static int rotateLeftBits() {
        return 50 >>> (32 - 4);
    }
    
    public static void usr(int x) {
        //@ ghost var z = ((\bigint)x) >>> 3;
    }

    //@ requires x >= 0;
    public static void usr2(int x) {
        //@ ghost var z = ((\bigint)x) >>> 3;
    }

    public static void main(String... args) {
        int n = rotateLeftBits();
        //@ show n;
        //@ check n == 0;
        usr(-100);
        usr(100);
    }
}
