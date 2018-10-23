 class TestAA extends TestB {
    
    //@ also
    //@   requires p >= 0;
    //@   requires p >= 10;
    //@   requires p >= 20;
    //@ also
    //@   requires p >= 5;
    //@   requires p >= 15;
    //@   requires p >= 25;
    public void m(Integer p, int q, Integer r) {
    }
    
}

public class TestA {
    
    
    public static void mm(TestAA a, int i, /*@ nullable */ Integer kk) {
        /*@ nullable */Integer k = null;
        switch (i) {
        case 1: a.m(k,100,100); break;
        case 2: a.m(100,100,kk); break;
        }
    }
}