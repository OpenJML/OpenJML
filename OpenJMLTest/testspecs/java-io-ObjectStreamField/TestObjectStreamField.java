import java.io.ObjectStreamField;

public class TestObjectStreamField {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        exceptions();
        System.out.println("DONE");
    }

    public static void construct() {
        ObjectStreamField f = new ObjectStreamField("count", int.class);
        //@ assert f.getName() == "count";
        //@ assert !f.isUnshared();
        ObjectStreamField g = new ObjectStreamField("next", Object.class, true);
        //@ assert g.getName() == "next";
        //@ assert g.isUnshared();
    }

    public static void exceptions() {
        try {
            new ObjectStreamField(null, int.class);
            //@ unreachable;
        } catch (NullPointerException e) {
        }
    }
}
