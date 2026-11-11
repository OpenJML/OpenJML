// RAC must not inline an invariant that names a member the calling class can't access in Java;
// javac's Lower crashed compiling such code for a protected member. RAC skips the invariant with a
// warning. Here A's invariant on its protected x reaches Main through B, a subclass in another
// package. Covers a constructor's exit (#1105), a method's entry and exit for a field and a
// parameter (#1104), and a call site. GregorianCalendar is a regression test for its specs, whose
// invariants on Calendar's protected 'fields' first exposed this.
import java.util.GregorianCalendar;
import p.B;

public class Main {
    public B f;
    public GregorianCalendar c;

    public Main() { f = new B(); c = new GregorianCalendar(); }

    public void m(B p, GregorianCalendar q) { }

    public static void main(String... args) {
        Main g = new Main();
        g.m(g.f, g.c);
        System.out.println("END");
    }
}
