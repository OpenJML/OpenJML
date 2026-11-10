// #1105 (RAC): the invariants of the object a field refers to are checked on leaving a method,
// on normal and exceptional exit; restore() breaks and restores, so it reports nothing.
class C {
    public int x;
    //@ public invariant x > 0;
    public C(int x) { this.x = x; }
}
public class R {
    public C f = new C(1);
    public void breakNormal() { f.x = 0; }
    public void breakExc() { f.x = 0; throw new RuntimeException(); }
    public void restore() { f.x = 0; f.x = 2; }
    public static void main(String... a) {
        R r = new R();
        r.restore();
        System.out.println("restore done");
        r.breakNormal();
        System.out.println("breakNormal done");
        r.f.x = 1;
        try { r.breakExc(); } catch (RuntimeException e) { System.out.println("breakExc threw"); }
    }
}
