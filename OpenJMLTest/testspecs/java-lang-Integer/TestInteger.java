@org.jmlspecs.annotation.NullableByDefault
public class TestInteger {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        esc(10,42,-7);
    }

    @org.jmlspecs.annotation.CodeJavaMath
    public static void esc(int i, int j, /*@ non_null */ Integer z) {
        Integer a = Integer.valueOf(i);
        Integer c = Integer.valueOf(i+1);
        Integer b = i;
        //@ check a != null;
        //@ check b != null;
        // @ check a != b; // Does not necessarily hold
        //@ check a.intValue() == b.intValue();
        //@ check a.equals(b);
        //@ check a.intValue() != c.intValue();
        //@ check !a.equals(c);
        //@ check ((int)a) == i;
        int k = b;
        //@ check k == i;
        //@ check a.equals(b);
        //@ check !a.equals(c);
        //@ check !a.equals(null);
        //@ check Integer.MIN_VALUE == -2147483648;
        //@ check Integer.MAX_VALUE == 2147483647;
        //@ check Integer.BYTES == 4;
        //@ check Integer.SIZE == 32;
        //@ check Integer.TYPE == int.class;

        //@ check \typeof(a) == \type(Integer);
        //@ check \typeof(a) <: \type(Number);
        //@ check \typeof(a) != \type(Object);

        int s = i+j;
        //@ check Integer.sum(i,j) == s;
        //@ check Integer.max(i,j) == (i>j ? i : j);
        //@ check Integer.min(i,j) == (i<j ? i : j);
        //-RAC@ check z.intValue() == z.theInteger;
        byte by = (byte)z.intValue();
        //@ check z.byteValue() == by;
        long lg = (long)z.intValue();
        //@ check z.longValue() == lg;
        short sh = (short)z.intValue();
        //@ check z.shortValue() == sh;
        //@ check Integer.signum(i) == (i > 0 ? 1 : i == 0 ? 0 : -1);

        //@ check z.hashCode() == z.intValue();
        //@ check Integer.hashCode(j) == j;
        // TODO - divideUnsigned, doubleValue, floatValue, remainderUnsigned

        // FIXME - compare operations
        // compare, compareTo, compareUnsigned

        // FIXME _ bit operations
        // bitCount, highestOneBit, lowestOneBits, numberOfLeadingZeros, numberOfTrailiongZeros
        // reverse, reverseBytes, rotateLeft, rotateRight

        // TODO: describeConstable, getInteger, resolveConstantDesc
        // TODO: clone, getClass

        // FIXME - string operations
        // decode, parseInt, parseUnsignedInt, valueOf
        // toBionaryString, toHexString, toOctalString, toUnsigned...


        //		String s = a.toString();
        //		int k = Integer.parseInt(s);
        //		//@ check k == i;
        //		s = Integer.toString(a);
        //		k = Integer.parseInt(s);
        //		//@ check k == i;

        //		//@ check a.hashCode() == i;
    }
}
