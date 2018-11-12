public class W {

    public void m() {
        int x = X.qqq();
        //@ assert x == 701;
    }

    //@ public normal_behavior
    //@   ensures true;
    public int mm() {
        int x = X.qqq();
        return x;
    }
}

class X {
    
    //@ private normal_behavior
    //@   ensures \result == 701;
    static public int qqq() {
        return 701;
    }
}