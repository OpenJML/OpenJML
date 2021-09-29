public class Misc
{


    // Does not properly recognize that a is for a fact negative infinity even when the bit representation is as such that it is negative infinity
    public void floatToIntBitsTest(Float a) {

        int b = Float.floatToIntBits(a);
        int sign = ((b >>> 31) == 0) ? 1 : -1;
        int exponent = ((b >>> 23) & 0xff);
        int mantissa = (b & 0x007fffff);

        //@ assert a == Float.POSITIVE_INFINITY <==> (sign == 1) && exponent == 0xff && mantissa == 0;
        //@ assert a == Float.NEGATIVE_INFINITY <==>  b == 0xff800000;
        //@ assert Float.isNaN(a) <==> b == 0x7fc00000;
        //@ assert (Float.isFinite(a) && !Float.isNaN(a)) ==> ((b < 0x7f800001) || ( b < 0xff800001 && b > 0x7fffffff ));
    }


    // Float.isNaN appears to believe that a is a float when its raw bits are 0xff800000 which is indicitive of negative infinity
    public void floatToRawIntBitsTest(Float a) {

        int b = Float.floatToRawIntBits(a);
        //@ assert a == Float.POSITIVE_INFINITY ==> b == 0x7f800000;
        //@ assert a == Float.NEGATIVE_INFINITY ==>  b == 0xff800000;
        //@ assert Float.isNaN(a) ==> ((b & 0x7f800000) == 0x7f800000) && ((b & 0x007fffff) != 0x0)  ;
        //@ assert (!Float.isFinite(a) && !Float.isNaN(a)) ==> ((b > 0xff800000) && ( b < 0x7f800000));
    }


    // weird errors seeming to pertain to the idea of NaN existing
    // Does not convert a wrapper NaN to a primitive NaN
    public void floatValueTest(Float a) {
        float b = a.floatValue();
        //@ assert !Float.isNaN(a) ==> a == b;
        //@ assert Float.isNaN(a) <==> Float.isNaN(b);
    }

    // Works directly off of floatToIntBits same issue
    public void hashCodeFloatTest(Float a,Float b) {
        int hashA = Float.hashCode(a);
        int hashB = Float.hashCode(b);
        //@ assert a == Float.POSITIVE_INFINITY ==> hashA == 0x7f800000;
        //@ assert a == Float.NEGATIVE_INFINITY ==>  hashA == 0xff800000;
        //@ assert Float.isNaN(a) ==> hashA == 0x7fc00000;
        //@ assert (!Float.isFinite(a) && !Float.isNaN(a)) ==> ((hashA < 0x7f800001) || ( hashA < 0xff800001 && hashA > 0x7fffffff ));
        //@ assert  (a == b) ==> hashA == hashB;
    }

    // Weird issue where function produces an infinite loop in SMT code

    // May require more testing due to signanling NaNs on different processor as referenced https://docs.oracle.com/javase/7/docs/api/java/lang/Float.html#intBitsToFloat(int)
    public void intBitsToFloatTest(int a) {

        Float b = Float.intBitsToFloat(a);
        int sign = ((a >> 31) == 0) ? 1 : -1;
        int exponent = ((a >> 23) & 0xff);
        int mantissa = (exponent == 0) ? (a & 0x7fffff) << 1 : (a & 0x7fffff) | 0x800000;
        //@ assert exponent == 0xff && sign == 1 && mantissa == 0 ==> b == Float.NEGATIVE_INFINITY;
        //@ assert exponent == 0xff && sign == -1 && mantissa == 0 ==> b == Float.POSITIVE_INFINITY;
        //@ assert exponent == 0xff && mantissa != 0  ==> Float.isNaN(b);
        //@ assert exponent != 0xff ==> Math.abs(b - (2 * (sign | 0x800000)*Math.pow(2,exponent-150))) < .1;
    }

    // Should throw a warning about possible lossy of accuracy with Infinites
    // Seems to be that a is being rounded when the expected result is to truncate to b
    public void intValueFloatTest(float a) {
        int b = (int)a;
        //@ assert a == Float.POSITIVE_INFINITY ==> b == Integer.MAX_VALUE;
        //@ assert a == Float.NEGATIVE_INFINITY ==> b == Integer.MIN_VALUE;
        //@ assert Float.isFinite(a) && a > 0.0f ==> a-b < 1 && a-b >= 0;
        //@ assert Float.isFinite(a) && a < 0.0f ==> a-b >-1 && a-b <= 0;
    }

    // In verboseness 3: Weird error wher eit believes Float.NaN and Float.Negative_Infinity are the same
    public void isInfiniteFloatTest(float a) {
        boolean b = Float.isInfinite(a);
        //@ assert a == Float.POSITIVE_INFINITY ==> b;
        //@ assert a == Float.NEGATIVE_INFINITY ==> b;
        //@ assert Float.isNaN(a) ==> !b;
        //@ assert !Float.isNaN(a) && a != Float.POSITIVE_INFINITY && a != Float.NEGATIVE_INFINITY ==> !b;
    }


}
