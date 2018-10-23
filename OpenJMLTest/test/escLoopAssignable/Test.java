public class Test {
    
	// FIXME - more tests to be sure that assignable is disambiguated between
	// loop specs and statement specs
    
    //@ requires a != null && a.length > 10;
    public void mm(int[] a) {
        
        a[3] = 10;
        //@ loop_invariant 5<=i && i<=8;
        //@ assignable i,a[4..7];
        for (int i= 5; i<8; i++) {
            a[i] = -4;
        }
        //@ assert a[3] == 10;  // OK
    }
    
}