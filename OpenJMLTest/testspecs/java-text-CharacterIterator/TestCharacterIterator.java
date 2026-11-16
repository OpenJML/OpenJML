import java.text.CharacterIterator;
import java.text.StringCharacterIterator;

// Calls go through the interface type, so only CharacterIterator's specifications are used.
public class TestCharacterIterator {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        ends(new StringCharacterIterator("abc"));
        ends(new StringCharacterIterator(""));
        stepping(new StringCharacterIterator("abc"));
        positions(new StringCharacterIterator("abcdef", 1, 4, 2));
        System.out.println("DONE");
    }

    public static void ends(CharacterIterator it) {
        char c = it.first();
        //@ assert it.getIndex() == it.getBeginIndex() && c == it.current();
        char d = it.last();
        //@ assert it.getBeginIndex() == it.getEndIndex() ==> (it.getIndex() == it.getEndIndex() && d == CharacterIterator.DONE);
        //@ assert it.getBeginIndex() != it.getEndIndex() ==> it.getIndex() == it.getEndIndex() - 1;
    }

    public static void stepping(CharacterIterator it) {
        it.first();
        int b = it.getBeginIndex();
        int e = it.getEndIndex();
        char c = it.next();
        //@ assert b < e - 1 ==> it.getIndex() == b + 1;
        //@ assert b >= e - 1 ==> (it.getIndex() == e && c == CharacterIterator.DONE);
        it.setIndex(b);
        c = it.previous();
        //@ assert c == CharacterIterator.DONE && it.getIndex() == b;
    }

    public static void positions(CharacterIterator it) {
        int b = it.getBeginIndex();
        int e = it.getEndIndex();
        //@ assert b <= it.getIndex() && it.getIndex() <= e;
        it.setIndex(e);
        //@ assert it.current() == CharacterIterator.DONE;
        if (e < Integer.MAX_VALUE) {
            try {
                it.setIndex(e + 1);
                //@ unreachable;
            } catch (IllegalArgumentException ex) {
            }
        }
        //@ assert it.getIndex() == e;
    }
}
