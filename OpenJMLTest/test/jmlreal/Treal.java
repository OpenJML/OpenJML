// This file tests (both esc and rac) simple cases of all the functionality of \real
import java.math.BigInteger;

public class Treal {
    
    public static void main(String... args) {
        int i = 42;
        //@ ghost \real rint = i; check rint == 42; check rint.intValue() == 42; check (int)rint == 42;
        //@ set rint = (\real)i; check rint == 42; check rint == \real.of(21+21);
        long l = 4000;
        //@ ghost \real rlong = l; check rlong == 4000L; check rlong.longValue() == 4000L; check (long)rlong == 4000L;
        //@ set rlong = (\real)l; check rlong == 4000L; check rlong == \real.of(4000L);
        short s = 3;
        //@ ghost \real rshort = s; check rshort == 3; check rshort.shortValue() == 3; check (short)rshort == 3;
        //@ set rshort = (\real)s; check rshort == 3; check rshort == \real.of((short)3);
        byte b = -7;
        //@ ghost \real rbyte = b; check rbyte == -7; check rbyte.byteValue() == -7; check (byte)rbyte == -7;
        //@ set rbyte = (\real)b; check rbyte == -7; check rbyte == \real.of((byte)-7);
        char c = 'a';
        //@ ghost \real rchar = c; check rchar == 'a'; check rchar.charValue() == 'a'; check (char)rchar == 'a';
        //@ set rchar = (\real)c; check rchar == 'a'; check rchar == \real.of('a');
        float f = 45.0f; //@ assume Float.isFinite(f);
        //@ ghost \real rfloat = f; check rfloat == 45.0f; check rfloat.floatValue() == 45.0f; check (float)rfloat == 45.0f;
        double d = -56.0d; //@ assume Double.isFinite(d);
        //@ ghost \real rdouble = d; check rdouble == -56.0d; check rdouble.doubleValue() == -56.0d; check (double)rdouble == -56.0d;
        //@ ghost \bigint g = 100;
        //@ ghost \real rbig = g; check rbig == 100; check rbig.bigintValue() == 100; check (\bigint)rbig == g;
        //@ set rbig = (\real)g; check rbig == 100; check rbig == \real.of(100);        
        BigInteger bb = BigInteger.valueOf(123);
        //@ ghost \real rb = \real.of(bb); check rb.bigintValue() == \bigint.of(bb);
        
        ops(42,43);
        compare(42,43);
        misc();
        errors();
        Tcasts.main(args);
    }
    /*@ pure */ public static void ops(int a, int b) {
        //@ ghost \real rlong = 4000L;
        //@ ghost \real rint = 42;
        //@ check rlong + rint == 4042;
        //@ check rlong - rint == 3958;
        //@ check rint * rint == 1764;
        //@ check (11 + rlong) / rint == 95.5;
        //@ check (11 + rlong) / -rint == -95.5;
        //@ check rlong % rint == 10;
        //@ check rlong % -rint == 10;
        //@ check -rlong % rint == -10;
        //@ check -rlong % -rint == -10;
        //@ ghost \real ra = a;
        //@ ghost \real rb = b;
        //@ check (+ra) == ra;
        //@ check (-ra) == ra.negate();
        //@ check (ra + rb) == ra.add(rb);
        //@ check (ra - rb) == ra.subtract(rb);
        //@ check (ra * rb) == ra.multiply(rb);
        //@ check (rb != 0) ==> (ra / rb) == ra.divide(rb);
        //@ check (rb != 0) ==> (ra % rb) == ra.mod(rb);
    }
    
    /*@ pure */ public static void compare(int a, int b) {
        //@ ghost \real rlong = 4000L;
        //@ ghost \real rint = 42;
        //@ check !(rlong < rint);
        //@ check rlong != rint;
        //@ ghost \real ra = a;
        //@ ghost \real rb = b;
        //@ check (ra < rb) == ra.lt(rb);
        //@ check (ra > rb) == ra.gt(rb);
        //@ check (ra <= rb) == ra.le(rb);
        //@ check (ra >= rb) == ra.ge(rb);
        //@ check (ra != rb) == ra.ne(rb);
        //@ check (ra == rb) == ra.eq(rb);
        //@ check (ra == rb) == ra.equals(rb);
    }
    /*@ pure */ public static void misc() {
        //@ ghost \real rlong = 4000L;
        //@ ghost \real rint = 42;
        //@ check rlong.compareTo(rint) > 0;
        //@ check rlong.compareTo((\real)(4000)) == 0;
        //@ check rlong == \real.of(4000);
        //@ check rlong.compareTo(\real.of(4000)) == 0;
        //@ check rlong.hashCode() == ((\real)4000).hashCode();
        //@ check rlong.hashCode() == \real.of(4000).hashCode();
        //@ check rlong.eq(4000) == true;
        //@ check (rlong == 4000) == true;
        //@ check \real.empty() == 0;
        //@ show rlong.toString(), rint;
    }
    
    /*@ pure */ public static void errors() {
        //@ ghost \real rlong = 4000L;
        try {
        //@ check rlong.equals(null);  // Not allowed
        } catch (Exception e) {
            System.out.println(e);
        }
    }
}