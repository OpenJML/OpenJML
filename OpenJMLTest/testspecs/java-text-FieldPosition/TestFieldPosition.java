import java.text.DateFormat;
import java.text.FieldPosition;

public class TestFieldPosition {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        setters();
        equality();
        System.out.println("DONE");
    }

    public static void construct() {
        FieldPosition p = new FieldPosition(3);
        //@ assert p.getField() == 3 && p.getFieldAttribute() == null;
        //@ assert p.getBeginIndex() == 0 && p.getEndIndex() == 0;
        FieldPosition q = new FieldPosition(null, 5);
        //@ assert q.getField() == 5 && q.getFieldAttribute() == null;
    }

    public static void setters() {
        FieldPosition p = new FieldPosition(1);
        p.setBeginIndex(4);
        p.setEndIndex(9);
        //@ assert p.getBeginIndex() == 4 && p.getEndIndex() == 9 && p.getField() == 1;
    }

    public static void equality() {
        FieldPosition p = new FieldPosition(2);
        FieldPosition q = new FieldPosition(2);
        //@ assert p.equals(q);
        //@ assert p.hashCode() == (2 << 24);
        q.setEndIndex(1);
        //@ assert !p.equals(q);
        //@ assert !p.equals("x");
    }
}
