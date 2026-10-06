// Issue #980: 'maps a[*] \into g' in an implementing class, where the model field g is declared
// in the interface, is not honored by the frame check: writing a[n] is reported as violating
// 'assignable g'. The same shape verifies when g is declared in the class itself.
public interface I {
    //@ public model instance \seq<Integer> g;

    //@ requires 0 <= n < 10;
    //@ assignable g;
    public void set(int n);
}
