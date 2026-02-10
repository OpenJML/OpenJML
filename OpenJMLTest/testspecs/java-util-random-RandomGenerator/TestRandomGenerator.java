import java.util.random.RandomGenerator;

@org.jmlspecs.annotation.NullableByDefault
public class TestRandomGenerator {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        esc();
        //@ print "DONE";
    }

    public static void esc() {
        var a = RandomGenerator.getDefault();
        //@ check a != null;
    }
}
