import java.util.FormattableFlags;

public class TestFormattableFlags {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        values();
        System.out.println("DONE");
    }

    public static void values() {
        //@ assert FormattableFlags.LEFT_JUSTIFY == 1;
        //@ assert FormattableFlags.UPPERCASE == 2;
        //@ assert FormattableFlags.ALTERNATE == 4;
        int all = FormattableFlags.LEFT_JUSTIFY | FormattableFlags.UPPERCASE | FormattableFlags.ALTERNATE;
        //@ assert all == 7;
    }
}
