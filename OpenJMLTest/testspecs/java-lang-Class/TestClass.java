@org.jmlspecs.annotation.NullableByDefault
public class TestClass {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        test();
        //@ print "END";
    }

    public static void test() {
        //@ check int.class.isPrimitive();
        //@ check void.class.isPrimitive(); // Checking that void is also considered primitive, despite the ambiguous language in javadocs
    }
}

// FIXME - lots more testing needed
