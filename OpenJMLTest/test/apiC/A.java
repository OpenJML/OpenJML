public class A {
    
    //@ ensures \result == 43;
    public static int n() {
        return 42;
    }

    public static void main(String... args) {
      n();
    }
}
