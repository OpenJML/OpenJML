package p;
// Each method's comment says whether it should verify; the results must not depend on whether the nullness
// annotations of A are in A.java, or in A.jml with A's source or with only its class file (#1067)
public class C {
    public void f0(A x) { //@ check x.f0 != null; // fails
    }
    public void f1(A x) { //@ check x.f1 != null; // verifies
    }
    public void f1e(A x) { //@ assume x.f1.length > 0;
        //@ check x.f1[0] != null; // fails
    }
    public void f2(A x) { //@ check x.f2 != null; // fails
    }
    public void f2e(A x) { //@ assume x.f2 != null && x.f2.length > 0;
        //@ check x.f2[0] != null; // verifies
    }
    public void f3e(A x) { //@ assume x.f3 != null && x.f3.length > 0;
        //@ check x.f3[0] != null; // fails
    }
    public void r0(A x) { //@ check x.r0() != null; // fails
    }
    public void r1(A x) { //@ check x.r1() != null; // verifies
    }
    public void r1e(A x) { //@ assume x.r1().length > 0;
        //@ check x.r1()[0] != null; // fails
    }
    public void r2(A x) { //@ check x.r2() != null; // fails
    }
    public void r2e(A x) { //@ assume x.r2() != null && x.r2().length > 0;
        //@ check x.r2()[0] != null; // verifies
    }
    public void r3(A x) { //@ check x.r3() != null; // verifies
    }
    public void r3e(A x) { //@ assume x.r3().length > 0;
        //@ check x.r3()[0] != null; // fails
    }
}
