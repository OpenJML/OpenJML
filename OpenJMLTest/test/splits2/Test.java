public class Test {

    public void wh(int i) {
        //@ split
        if (i < 0) {
            //@ assert i < -1; // Split A
            return;
        }
        int j = i;
        //@ loop_invariant -1 <= j <= i;
        //@ split
        while (j >= 0) {
            --j;
            //@ loop_invariant 0 <= k <= 10;
            //@ split
            for (int k=0; k<10; k++) {
                //@ assert k < 0; // FAILS - BAA
            }
            
            int[] a = {1,2,3};
            //@ split
            for (int k: a) {
                //@ assert i < 1; // FAILS - BABA
            }
            
            //@ assert i < 2; // FAILS - BABB
        }
        
        //@ loop_invariant 0 <= j <= 10;
        //@ split
        while (j < 10) {
            j++;
            //@ assert i < 3; // FAILS - BBA
        }
        //@ assert j < 0; // FAILS - BBB
    }

}