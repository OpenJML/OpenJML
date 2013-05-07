import java.util.LinkedList;
import java.util.List;


public class Bug1 {

    public static void main(String... args) {
        LinkedList<?>[] a = new LinkedList<?>[1];
        a[0] = new LinkedList<Boolean>();
        //@ ghost \TYPE t = \elemtype(\typeof(a));
        //@ assume (\lbl TY t) != null;
        System.out.println("END");
    }
}
