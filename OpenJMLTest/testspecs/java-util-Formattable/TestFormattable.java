import java.util.Formattable;
import java.util.Formatter;
import java.util.IllegalFormatException;

public class TestFormattable {

    static class F implements Formattable {
        //@ also public normal_behavior
        //@   requires formatter != null;
        //@   assignable \nothing;
        public void formatTo(Formatter formatter, int flags, int width, int precision) {}
    }

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        formatTo(new F(), new Formatter());
        System.out.println("DONE");
    }

    //@ requires f != null && fm != null;
    public static void formatTo(Formattable f, Formatter fm) {
        try {
            f.formatTo(fm, 0, -1, -1);
        } catch (IllegalFormatException e) {
            // allowed by Formattable.formatTo's spec
        }
    }
}
