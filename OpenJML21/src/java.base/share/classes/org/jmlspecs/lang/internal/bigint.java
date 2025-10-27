package org.jmlspecs.lang.internal;

import java.math.BigInteger;

import org.jmlspecs.lang.IJmlPrimitiveType;

public class bigint extends Number implements IJmlPrimitiveType {

    private static final long serialVersionUID = 1L;

    final private BigInteger value;
    
    private bigint(BigInteger v) {
        value = v;
    }
    
    public final static bigint zero = bigint.of(0);
    
    public final static bigint one = bigint.of(1);
    
    public static bigint empty() { return zero; }
    
    public static bigint of(BigInteger i) {
        return new bigint(i);
    }
    
    public static bigint of(bigint i) {
        return i;
    }
    
    public static bigint of(long i) {
        return new bigint(BigInteger.valueOf(i));
    }
    
    public static bigint of(int i) {
        return new bigint(BigInteger.valueOf(i));
    }
    
    public static bigint of(short i) {
        return new bigint(BigInteger.valueOf(i));
    }
    
    public static bigint of(char i) {
        return new bigint(BigInteger.valueOf(i));
    }
    
    public static bigint of(byte i) {
        return new bigint(BigInteger.valueOf(i));
    }
    
    // The OpenJDK code uses valueOf by default for conversions  // FIXME - change this
    public static bigint valueOf(long i) {
        return new bigint(BigInteger.valueOf(i));
    }
    
    public static bigint valueOf(int i) {
        return new bigint(BigInteger.valueOf(i));
    }
    
    public static bigint valueOf(bigint i) {
        return i;
    }
    
    public bigint negate() {
        return new bigint(value.negate());
    }
    
    public bigint add(bigint v) {
        return new bigint(value.add(v.value));
    }
    
    public bigint subtract(bigint v) {
        return new bigint(value.subtract(v.value));
    }
    
    public bigint multiply(bigint v) {
        return new bigint(value.multiply(v.value));
    }
    
    public bigint divide(bigint v) {
        if (v.value.equals(BigInteger.ZERO)) throw new ArithmeticException("/ by zero");
        return new bigint(value.divide(v.value));
    }
    
    public bigint mod(bigint v) {
        if (v.value.equals(BigInteger.ZERO)) throw new ArithmeticException("mod by zero");
        boolean neg = v.value.signum() < 0;
        return new bigint(value.remainder(v.value));
    }
    
    public boolean eq(bigint v) {
        return value.equals(v.value);
    }
    
    public boolean ne(bigint v) {
        return !value.equals(v.value);
    }
    
    public boolean lt(bigint v) {
        return value.compareTo(v.value) < 0;
    }
    
    public boolean le(bigint v) {
        return value.compareTo(v.value) <= 0;
    }
    
    public boolean gt(bigint v) {
        return value.compareTo(v.value) > 0;
    }
    
    public boolean ge(bigint v) {
        return value.compareTo(v.value) >= 0;
    }
    
    public bigint and(bigint v) {
        return new bigint(value.and(v.value));
    }
    
    public bigint or(bigint v) {
        return new bigint(value.or(v.value));
    }
    
    public bigint xor(bigint v) {
        return new bigint(value.xor(v.value));
    }
    
    public bigint comp() {
        return new bigint(value.not());
    }
    
    // A negative shift is a positive shift in the other direction, at least in RAC
    public bigint shiftLeft(bigint v) {
        return new bigint(value.shiftLeft(v.value.intValue()));
    }
    
    public bigint shiftRight(bigint v) {
        return new bigint(value.shiftRight(v.value.intValue()));
    }
    

    public String toString() {
        return value.toString();
    }
    
    public java.math.BigInteger bigValue() {
        return value;
    }

    public double doubleValue() {
        return value.doubleValue();
    }

    public float floatValue() {
        return value.floatValue();
    }

    public long longValue() {
        if (of(Long.MIN_VALUE).gt(this) || of(Long.MAX_VALUE).lt(this)) org.jmlspecs.runtime.Utils.assertionFailure("JML argument to numeric cast is out of range of the target type: " + this + " to long");
        return value.longValue();
    }

    public int intValue() {
        if (of(Integer.MIN_VALUE).gt(this) || of(Integer.MAX_VALUE).lt(this)) org.jmlspecs.runtime.Utils.assertionFailure("JML argument to numeric cast is out of range of the target type: " + this + " to int");
        return value.intValue();
    }

    public short shortValue() {
        if (of(Short.MIN_VALUE).gt(this) || of(Short.MAX_VALUE).lt(this)) org.jmlspecs.runtime.Utils.assertionFailure("JML argument to numeric cast is out of range of the target type: " + this + " to short");
        return value.shortValue();
    }

    public char charValue() {
        if (of(Character.MIN_VALUE).gt(this) || of(Character.MAX_VALUE).lt(this)) org.jmlspecs.runtime.Utils.assertionFailure("JML argument to numeric cast is out of range of the target type: " + this + " to char");
        return (char)value.intValue();
    }

    public byte byteValue() {
        if (of(Byte.MIN_VALUE).gt(this) || of(Byte.MAX_VALUE).lt(this)) org.jmlspecs.runtime.Utils.assertionFailure("JML argument to numeric cast is out of range of the target type: " + this + " to byte");
        return value.byteValue();
    }

    public real realValue() {
        return real.of(value);
    }
    
    public int compareTo(bigint b) {
        if (b == null) throw new NullPointerException("\\bigint.compareTo(null)");
        return value.compareTo(b.value);
    }
    
    @Override
    public boolean equals(Object o) {
        return o instanceof bigint b && this.eq(b);
    }
    
    public boolean equals(bigint o) {
        return this.eq(o);
    }
    
    @Override
    public int hashCode() {
        return value.hashCode();
    }
}
