import java.util.LinkedList;
import java.util.List;


public class bigint {

    // FIXME - also test casts back to int types, assignment from long, mixed operations with long or other types
    // initialization from string, output to string
    public static void main(String... args) {
        //@ ghost \bigint b = 20;
        //@ ghost \bigint bb = -b;
        //@ ghost \bigint zero = 0;
        //@ ghost \bigint prod = -400;
        //@ assert b + bb == zero;
        //@ assert b * bb == prod;
        //@ assert (\lbl BVALUE b) + bb == 0;
        //@ assert b + 0 == b;
        //@ assert b > 0;
        //@ assert zero == 0L;
        //@ set zero = 0L;
        //@ assert zero >= 0;
        //@ assert 0L + b == b;
        //@ assert b * (short)0 == zero;
        //@ ghost int i = (int)b;
        //@ ghost long l = (long)b;
        //@ assert b == zero;
    }
}
