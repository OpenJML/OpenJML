enum EEE {
    
    AA(4), BB(8), CC(7);
    
    //@ spec_public
    private int code;
    
    //@ public invariant BB.code == 8;
    //@ public invariant CC.code == 7;
    
    //@ private normal_behavior
    //@   ensures code == c;
    //@ pure
    private EEE(int c) { code = c; }
}

public Test {
    
    public void m0() {
        //@ assert AA.code == 4;
        //@ assert BB.code == 8;
        //@ assert CC.code == 7;
    }
    
    public void m1() {
        AA.code = 9;
    }
    
}