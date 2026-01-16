public class M {

    //@ ensures \result > 0;
    //@ pure
    public static double test() {
        //@ assert Double.isFinite(2.0);
        //@ assert 2.0 != 0.0;
        //@ assert Double.isFinite(3.0);
        //@ assert 2.0 > 0.0;
        double k = Math.pow(2.0,3.0);
        //@ assert !Double.isNaN(k);
        //@ assert k > 0;
        return k;
    }
}
