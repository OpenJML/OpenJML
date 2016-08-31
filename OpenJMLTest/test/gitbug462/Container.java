public class Container {
    public static /*@ non_null @*/ Object c = new Object();

    /*@ public normal_behavior
      @   assignable c;
      @*/
    public static void allocate() {
        c = new Object();
    }

    public static void test() {
        allocate();
        //@ assert c instanceof Object;
    }
}