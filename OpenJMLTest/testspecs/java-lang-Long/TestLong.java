public class TestLong {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        compare();
        System.out.println("DONE");
    }

    public static void compare() {
        //@ assert Long.compare(3L, 5L) == -1 && Long.compare(5L, 5L) == 0 && Long.compare(5L, 3L) == 1;
        //@ assert Long.compare(Long.MIN_VALUE, Long.MAX_VALUE) == -1 && Long.compare(-1L, Long.MIN_VALUE) == 1;
    }
}
