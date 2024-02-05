 class TestAA extends TestB {
    
    //@ also
    //@   requires pq >= 0;
    //@   requires pq >= 10;
    //@   requires pq >= 20;
    //@ also
    //@   requires pq >= 5;
    //@   requires pq >= 15;
    //@   requires pq >= 25;
    public void m( /*@ non_null */Integer pq, int q,  /*@ non_null */Integer r) {
    }
    
}

public class TestA {
    
    
    // Fails because p must be non_null for all spec cases
    public static void m1(TestAA a, /*@ nullable */ Integer kk) {
        /*@ nullable */Integer k = null;
        a.m(k,100,100);
    }
    
    // Fails because r must be non_null for all spec cases
    public static void m2(TestAA a, /*@ nullable */ Integer kk) {
        a.m(100,100,kk);
    }
    
    // OK because C and B's preconditions are ok
    public static void m3(TestAA a, /*@ non_null */Integer k) {
        a.m(k,100,100);
    }
    
    // OK because A and B's preconditions are ok
    public static void m4(TestAA a, /*@ non_null */Integer kk) {
        a.m(100,100,kk);
    }

}