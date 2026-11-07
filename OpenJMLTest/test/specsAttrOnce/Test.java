import java.util.*;

// The specs of a binary class's method are type-checked once, although the .jml declaration and the
// class file each have a symbol for it: the warning about size() (not declared in HashMap.jml) appears once
public class Test {
    public static void m(Map<Integer,String> mm) {
        HashMap<Integer,String> map = new HashMap<Integer,String>(mm);
    }
}
