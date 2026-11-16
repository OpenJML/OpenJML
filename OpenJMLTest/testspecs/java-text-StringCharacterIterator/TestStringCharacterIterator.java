import java.text.CharacterIterator;
import java.text.StringCharacterIterator;

public class TestStringCharacterIterator {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        construct();
        walkForward();
        walkBack();
        empty();
        setText();
        equality();
        exceptions();
        System.out.println("DONE");
    }

    public static void construct() {
        StringCharacterIterator it = new StringCharacterIterator("abcd");
        //@ assert it.getBeginIndex() == 0 && it.getEndIndex() == 4 && it.getIndex() == 0;
        StringCharacterIterator it2 = new StringCharacterIterator("abcd", 1, 3, 2);
        //@ assert it2.getBeginIndex() == 1 && it2.getEndIndex() == 3 && it2.getIndex() == 2;
        StringCharacterIterator it3 = new StringCharacterIterator("abcd", 4);
        //@ assert it3.getIndex() == 4 && it3.current() == CharacterIterator.DONE;
    }

    public static void walkForward() {
        StringCharacterIterator it = new StringCharacterIterator("xyz");
        char c = it.first();
        //@ assert c == 'x' && it.getIndex() == 0;
        c = it.next();
        //@ assert c == 'y' && it.getIndex() == 1;
        c = it.next();
        //@ assert c == 'z' && it.getIndex() == 2;
        c = it.next();
        //@ assert c == CharacterIterator.DONE && it.getIndex() == 3;
        c = it.next();
        //@ assert c == CharacterIterator.DONE && it.getIndex() == 3;
    }

    public static void walkBack() {
        StringCharacterIterator it = new StringCharacterIterator("xyz", 3);
        char c = it.previous();
        //@ assert c == 'z' && it.getIndex() == 2;
        c = it.last();
        //@ assert c == 'z' && it.getIndex() == 2;
        c = it.setIndex(0);
        //@ assert c == 'x';
        c = it.previous();
        //@ assert c == CharacterIterator.DONE && it.getIndex() == 0;
    }

    public static void empty() {
        StringCharacterIterator it = new StringCharacterIterator("");
        char c = it.first();
        //@ assert c == CharacterIterator.DONE;
        c = it.last();
        //@ assert c == CharacterIterator.DONE && it.getIndex() == 0;
    }

    public static void setText() {
        StringCharacterIterator it = new StringCharacterIterator("abc", 2);
        it.setText("hello");
        //@ assert it.getBeginIndex() == 0 && it.getEndIndex() == 5 && it.getIndex() == 0;
        //@ assert it.current() == 'h';
    }

    public static void equality() {
        StringCharacterIterator it = new StringCharacterIterator("abc");
        //@ assert it.equals(it);
        //@ assert !it.equals("abc");
    }

    public static void exceptions() {
        try {
            new StringCharacterIterator("abc", 5);
            //@ unreachable;
        } catch (IllegalArgumentException e) {
        }
        try {
            new StringCharacterIterator("abc", 2, 1, 1);
            //@ unreachable;
        } catch (IllegalArgumentException e) {
        }
        try {
            new StringCharacterIterator(null, 0, 0, 0);
            //@ unreachable;
        } catch (NullPointerException e) {
        }
        StringCharacterIterator it = new StringCharacterIterator("abc");
        try {
            it.setIndex(4);
            //@ unreachable;
        } catch (IllegalArgumentException e) {
        }
        //@ assert it.getIndex() == 0;
    }
}
