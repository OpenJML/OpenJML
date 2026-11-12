// RAC for the 'invariants' clause (#651): the invariants of the listed objects are checked on
// entry, at normal and exceptional exit, and by the caller before and after a call, as the
// default (receiver and parameter) invariants are. Checks of assumed invariants (callee entry,
// caller after a call) are made only with --rac-check-assumptions, as for default invariants.
// racfiles runs this with and without that option (invariantsClauseRacNoAssume).

class C {
    public int x;
    //@ public invariant x > 0;
    public C(int x) { this.x = x; }
}

class D {
    public C c;
    public D(C c) { this.c = c; }
}

public class T {

    //@ invariants p.c;
    public static void ok(D p) {
        p.c.x = 2;
    }

    // Reports on leaving
    //@ invariants p.c;
    public static void breakNormal(D p) {
        p.c.x = 0;
    }

    // Reports on leaving with an exception
    //@ invariants p.c;
    public static void breakExceptional(D p) {
        p.c.x = 0;
        throw new RuntimeException();
    }

    // For comparison: the default invariants of a parameter, called with an invalid c
    public static void defaultEntry(C c) {
    }

    // Called with an invalid p.c: reports at the call (caller) and on entering (callee)
    //@ invariants p.c;
    public static void entry(D p) {
    }

    // Reports on leaving: the original p.c is broken; p is then reassigned to a valid object
    //@ invariants p.c;
    public static void reassign(D p) {
        p.c.x = 0;
        p = new D(new C(1));
    }

    public static void main(String... args) {
        D d = new D(new C(1));
        ok(d);
        System.out.println("ok done");
        breakNormal(d);
        System.out.println("breakNormal done");
        d.c.x = 1;
        try {
            breakExceptional(d);
        } catch (RuntimeException e) {
            System.out.println("breakExceptional threw");
        }
        d.c.x = 1;
        D bad = new D(new C(1));
        bad.c.x = -1;
        defaultEntry(bad.c);
        System.out.println("defaultEntry done");
        entry(bad);
        System.out.println("entry done");
        reassign(d);
        System.out.println("reassign done");
    }
}
