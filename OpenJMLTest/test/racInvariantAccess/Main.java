// RAC must not inline an invariant of a library class that names members the caller can't
// access in Java (here GregorianCalendar's invariants on Calendar's protected 'fields'); javac's
// Lower crashed compiling such code. Covers a constructor's exit (#1105), a method's entry and exit
// for a field and a parameter (#1104), and a call site. Values are null so that the run does not
// reach the GregorianCalendar constructor, whose postcondition names a private field.
import java.util.GregorianCalendar;

public class Main {
    public /*@ nullable */ GregorianCalendar f;

    public Main() { f = null; }

    public void m(/*@ nullable */ GregorianCalendar p) { }

    public static void main(String... args) {
        Main g = new Main();
        g.m(g.f);
        System.out.println("END");
    }
}
