import java.text.ParsePosition;

public class TestParsePosition {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        setters();
        equality();
        System.out.println("DONE");
    }

    public static void construct() {
        ParsePosition p = new ParsePosition(5);
        //@ assert p.getIndex() == 5;
        //@ assert p.getErrorIndex() == -1;
    }

    public static void setters() {
        ParsePosition p = new ParsePosition(0);
        p.setIndex(7);
        //@ assert p.getIndex() == 7 && p.getErrorIndex() == -1;
        p.setErrorIndex(3);
        //@ assert p.getIndex() == 7 && p.getErrorIndex() == 3;
        p.setIndex(-2);
        //@ assert p.getIndex() == -2 && p.getErrorIndex() == 3;
    }

    public static void equality() {
        ParsePosition p = new ParsePosition(4);
        ParsePosition q = new ParsePosition(4);
        //@ assert p.equals(q) && p.hashCode() == q.hashCode();
        //@ assert p.hashCode() == ((-1 << 16) | 4);
        q.setErrorIndex(1);
        //@ assert !p.equals(q);
        //@ assert !p.equals(null);
        //@ assert !p.equals("x");
    }
}
