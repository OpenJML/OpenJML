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
        case 2: return i == 10; // ERROR - split B
        case 3: return i == 2;
        default: return i < 0;
        }
    }
    
    public void bad() {
        //@ split  // ERROR: Out of place
        int i;
    }
    
    public void bad2() {
        int i;
        //@ split  // ERROR: Out of place
    }
    
    //@ ensures \result;
    public boolean mbool(int i) {
        //@ split i > 0;
        return i > 0;  // Split A OK; Split B is ERROR
    }
    
    //@ ensures \result;
    public boolean mcombined(int i) { // ERROR - split AB, BB infeasible
        //@ split
        if (i > 0) {
            //@ split i >= 0;
            return i >= 0; // split AB infeasible
        } else {
            //@ split
            switch (i) {
            case 0: return true;
            case 1: return i > 0; // Infeasible - split BB
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
    
    public int j;
    //@ requires i < 1000;
    //@ ensures j == i + 1;
    public void msw(int i) {
        switch (i) {
        case 0: j = 1; return;
        case 1: j = 2; return;
        default: j = i +1; return;
        }
    }
    
    //@ requires i < 1000;
    //@ ensures j == i + 1;
    public void mswa(int i) {  // ERROR - case 1
        switch (i) {
        case 0: j = 1; return;
        case 1: j = 3; break;
        default: j = i + 1; return;
        }
    }
    
    //@ requires i < 1000;
    //@ ensures (\lbl J j) == i + 1;
    public void mswb(int i) {
        //@ show i;
        switch (i) {
        case 0: j = 1; return;
        case 1: j = 3; break;
        default: j = i + 1; return;
        }
        j = 2;
    }
    
    //@ requires i < 1000;
    //@ ensures j == i + 1; // ERROR on default
    public void mswc(int i) {
        switch (i) {
        case 0: j = 1; return;
        case 1: j = 2; return;
        }
    }
    
    public void halt1(int i) {
        
        if (i > 0) {
            j = 10;
            //@ halt ;
            //@ assert j == 11; // IGNORED
        }
        //@ assert i < 0; // FAILS
    }
    
    public void halt2(int i) {
        
        if (i > 0) {
            j = 10;
            //@ halt ;
            //@ assert j == 11; // IGNORED
        }
        //@ assert i <= 0; // SUCCEEDS
    }
    
    public void halt3(int i) {
        
        if (i > 0) {
            j = 10;
            //@ halt ;
            //@ assert j == 11; // IGNORED
        } else {
            //@ halt
        }
        //@ assert false; // IGNORED
    }
}