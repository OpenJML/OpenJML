public class DiscreteOps
{


    // All sorts of wrongness, turned a -1.0/10.0 int 1.0/4.0 which then was interpreted as NaN, As well rounding 1.0/4.0 to 5.0/4.0 which looks like a 1 up
    public void ceilTest(double a) {
        double b = Math.ceil(a);
        //@ assert Double.isNaN(a) <==> Double.isNaN(b);
        //@ assert Double.POSITIVE_INFINITY == a <==> Double.POSITIVE_INFINITY == b;
        //@ assert Double.NEGATIVE_INFINITY == a <==> Double.NEGATIVE_INFINITY == b;
        //@ assert Double.isFinite(a) && (a < 0) <==> a-b >= 0.0d && a-b < 1.0d;
        //@ assert Double.isFinite(a) && (a > 0) <==> a-b <= 0.0d && a-b > -1.0d;
        //@ assert Double.isFinite(a) && (a > -1.0d && a < 0) <==> (new Double(b)).equals(-0.0d);

    }

    // Rounded a value down to negative infinity, that value being -1.0/4.0, presumed issue with definition of Infinities and issue with flooring
    public void floorTest(double a) {
        double b = Math.floor(a);
        //@ assert Double.isNaN(a) <==> Double.isNaN(b);
        //@ assert Double.POSITIVE_INFINITY == a <==> Double.POSITIVE_INFINITY == b;
        //@ assert Double.NEGATIVE_INFINITY == a <==> Double.NEGATIVE_INFINITY == b;
        //@ assert Double.isFinite(a) && (a < 0) <==> b-a >= 0.0d && b-a < 1.0d;
        //@ assert Double.isFinite(a) && (a > 0) <==> b-a <= 0.0d && b-a > -1.0d;
    }

    // Issues are found with the specification on rint Double.isNaN(a) thinks that result == a which is not true for NaN since NaN not comparable
    // Does not round to the nearest value correctly in SMT
    public void rintTest(double a) {
        double b = Math.rint(a);
        //@ assert Double.isNaN(a) <==> Double.isNaN(b);
        //@ assert Double.POSITIVE_INFINITY == a <==> Double.POSITIVE_INFINITY == b;
        //@ assert Double.NEGATIVE_INFINITY == a <==> Double.NEGATIVE_INFINITY == b;
        //@ assert Double.isFinite(a) && (a-b > 0) ==> a-b <= 0.5d;
        //@ assert Double.isFinite(a) && (a-b < 0) ==> b-a < 0.5d;
    }
    public void roundTest(float a) {
        int b = Math.round(a);
        //@ assert Float.isNaN(a) <==> b == 0;
        //@ assert (Float.POSITIVE_INFINITY == a) || (a >= Integer.MAX_VALUE) <==> Integer.MAX_VALUE == b;
        //@ assert (Float.NEGATIVE_INFINITY == a) || (a >= Integer.MIN_VALUE) <==> Integer.MIN_VALUE == b;
        //@ assert Float.isFinite(a) && (a-b > 0) ==> a-b <= 0.5d;
        //@ assert Float.isFinite(a) && (a-b < 0) ==> b-a < 0.5d;
    }

    // floorDiv on min Int and min int gives 2 instead of 1
    //@ requires y != 0;
    public void floorDivIntTest(int x, int y) {
        int c = Math.floorDiv(x,y);
        int d = x/y;
        //@ assert (x == Integer.MIN_VALUE && y == -1) ==> c == Integer.MIN_VALUE;
        //@ assert (x < 0 ^ y < 0) <==> c == (d-1);
        //@ assert !(x < 0 ^ y < 0) && !( x == Integer.MIN_VALUE && y == -1) <==> c == d;
    }

    public void floorDivLongTest( long x, long y) {
        long c = Math.floorDiv(x,y);
        long d = x/y;
        //@ assert (x == Long.MIN_VALUE && y == -1) ==> c == Long.MIN_VALUE;
        //@ assert (x < 0 ^ y < 0) <==> c == (d-1);
        //@ assert !(x < 0 ^ y < 0) && !( x == Long.MIN_VALUE && y == -1) <==> c == d;
    }

    //@ requires y != 0;
    public void floorModIntTest(int x, int y) {
        int c = Math.floorMod(x,y);
        int d = c % y;
        //@ assert !(x < 0 ^ y < 0) <==> c == d;
        //@ assert (x < 0 && y > 0) <==> c == (d-1) * -1;
        //@ assert (x > 0 && y < 0) <==> c == (d+1) * -1;
    }

    public void floorModLongTest(long x, long y) {
        long c = Math.floorMod(x,y);
        long d = c % y;
        //@ assert !(x < 0 ^ y < 0) <==> c == d;
        //@ assert (x < 0 && y > 0) <==> c == (d-1) * -1;
        //@ assert (x > 0 && y < 0) <==> c == (d+1) * -1;
    }




}
