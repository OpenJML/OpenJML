// Issue #980: an element of a model field used as a frame location (reads s[n], assignable s[n],
// assignable mp[0]). These were treated as Java array elements, giving an ill-sorted SMT script.
// Semantics pinned here: 'in s' puts the field a itself in s, not its elements; 'maps a[*] \into s'
// makes s[k] stand for a[k]. So reads s[n] allows reading a[n] but not the field a (get fails,
// get2 verifies); assignable s[n] allows writing a[n] (set) but not a[n+1] (setOther fails).
// m and m2 are callers of methods with such frames: no SMT error.
public abstract class S {
    //@ public model \seq<Integer> s;
    //@ public model \map<Integer,Integer> mp;
    private final int[] a = new int[10]; //@ in s; //@ maps a[*] \into s;
    //@ private invariant a.length == 10;
    public int x;

    //@ requires 0 <= n < 10;
    //@ reads s[n];
    //@ spec_pure
    public int get(int n) { return a[n]; }

    //@ requires 0 <= n < 10;
    //@ reads s, s[n];
    //@ spec_pure
    public int get2(int n) { return a[n]; }

    //@ requires 0 <= n < 10;
    //@ assignable s[n];
    public void set(int n) { a[n] = 1; }

    //@ requires 0 <= n < 9;
    //@ assignable s[n];
    public void setOther(int n) { a[n+1] = 1; }

    //@ requires 0 <= n;
    //@ assignable s[n];
    public abstract void set2(int n);

    //@ assignable mp[0];
    public abstract void set3();

    public void m() { int y = x; set2(0); //@ assert x == y;
    }

    public void m2() { int y = x; set3(); //@ assert x == y;
    }
}
