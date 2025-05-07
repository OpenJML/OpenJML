public class Misc
{

    // NaN case works here  but not for Floats?
    public void doubleValueTest(Double a) {
        double b = a.doubleValue();
        //@ assert !Double.isNaN(a) ==> a == b;
        //@ assert Double.isNaN(a) <==> Double.isNaN(b);
    }

    // Only needs to check if the exact bit representation is the same
    public void equalsTest(Double a,Double b) {
        boolean c = a.equals(b);
        boolean d = Double.doubleToLongBits(a) == Double.doubleToLongBits(b);
        //@ assert  d == c;
    }


    // Need a way to compare float and doubles in order for this to work
    public void floatFromDoubleValueTest(Double a) {
        Float b = a.floatValue();
        // @ assert !Double.isNaN(a) ==> a == b;
    }


    // Getting different values than from documentation
    public void hashCodeDoubleTest(Double a) {
        long v = Double.doubleToLongBits(a);
        int longBitRep = (int)(v^(v>>>32));
        int hash = a.hashCode();
        //@ assert hash == longBitRep;
    }

    // Same issue as before
    public void hashCodeStaticTest(double a) {
        long v = Double.doubleToLongBits(a);
        int longBitRep = (int)((v & 0x00000000ffffffffL)^(v>>>32));
        int hash = Double.hashCode(a);
        //@ assert hash == longBitRep;
    }

    // Casting the true value of a not the representitave value which could be negative infinity
    public void intValueDoubleTest(double a) {
        int b = (int)a;
        //@ assert (a == Double.POSITIVE_INFINITY) || (a >= Integer.MAX_VALUE) ==> b == Integer.MAX_VALUE;
        //@ assert (a == Double.NEGATIVE_INFINITY) || (a <= Integer.MIN_VALUE) ==> b == Integer.MIN_VALUE;
        //@ assert Double.isFinite(a) && a > 0.0f && !(b == Integer.MAX_VALUE)  ==> a-b > -1 && a-b <= 0;
        //@ assert Double.isFinite(a) && a < 0.0f && !(b == Integer.MIN_VALUE) ==> a-b < 1 && a-b >= 0;
    }




}
