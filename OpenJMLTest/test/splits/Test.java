public class Test {
    
    //@ ensures \result;
    public boolean mnosplit(int i) {
        if (i > 0) {
            return i > 0;
        } else {
            return i > 0; // ERROR
        }
    }
    
    //@ ensures \result;
    public boolean m1(int i) {
        //@ split
        if (i > 0) {
            return i > 0;
        } else {
            return i > 0; // ERROR
        }
    }
    
    //@ ensures \result;
    public boolean m2(int i) {
        //@ split;
        if (i>0) {
            return i < 0; // ERROR
        } else {
            return i <= 0;
        }
    }
    
    //@ requires i <= 2;
    //@ ensures \result;
    public boolean m3(int i) {
        //@ split
        switch (i + 1) {
        case 1: return i == 0;
        case 2: return i == 10; // ERROR
        case 3: return i == 2;
        default: return i < 0;
        }
    }
    
    public void bad() {
        //@ split
        int i;
    }
    
    public void bad2() {
        int i;
        //@ split
    }
    
    //@ ensures \result;
    public boolean mbool(int i) {
        //@ split i > 0;
        return i > 0;
    }
    
    //@ ensures \result;
    public boolean mcombined(int i) {
        //@ split
        if (i > 0) {
            //@ split i >= 0;
            return i >= 0; // ERROR
        } else {
            //@ split
            switch (i) {
            case 0: return true;
            case 1: return i > 0; // Infeasible
            default: return i < 0;
            }
        }
    }
    
    //@ ensures i>0 ==> \result == 10 * 10101;
    //@ ensures i<=0 ==> \result == 20 * 10101;
    //@ @org.jmlspecs.annotation.Options("-split=A")
    public int splitx(int i) {
        //@ split
        if (i > 0) {
            return 101010;
        }
        return 202020;
    }
}