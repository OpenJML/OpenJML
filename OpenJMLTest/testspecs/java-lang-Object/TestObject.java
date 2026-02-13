
@org.jmlspecs.annotation.NullableByDefault
public class TestObject {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        esc();
    }

    public static void esc() {
        Object a = new Object();
        Object b = new Object();
        //@ check a != null;
        //@ check b != null;
        //@ check a != b;
        int i1 = a.hashCode();
        int i2 = a.hashCode();
        //@ check i1 == i2;
        //@ check a.equals(a); 
        //@ check !a.equals(b); 
        //@ check !a.equals(null); 
        // @ check a.getClass() == \erasure(\typeof(a));  // FIXME - causes infeasibility?
        //@ check a.getClass() == b.getClass();
        //@ check \typeof(a) == \typeof(b);
        // FIXME - no tests of toString
    }
}
