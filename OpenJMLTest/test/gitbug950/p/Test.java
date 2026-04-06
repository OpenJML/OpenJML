package p;
public class Test {
    //@ requires x != Integer.MIN_VALUE;
    //@ ensures \result >= 0;
    public int abs(int x) { return x >= 0 ? x : -x; }

    public static void main(String... args) {
        Test t = new Test();
        //+RAC@ set System.out.println(t.abs(-3));
    }
}
