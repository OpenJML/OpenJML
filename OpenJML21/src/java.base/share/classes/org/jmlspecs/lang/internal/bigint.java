package org.jmlspecs.lang.internal;

import java.math.BigInteger;

import org.jmlspecs.lang.IJmlPrimitiveType;

public class bigint implements IJmlPrimitiveType {
    
    final private BigInteger value;
    
    private bigint(BigInteger v) {
        value = v;
    }
    
    public final static bigint zero = bigint.of(0);
    
    public final static bigint one = bigint.of(1);
    
    public static bigint of(BigInteger i) {
        return new bigint(i);
    }
    
    public static bigint of(long i) {
        return new bigint(BigInteger.valueOf(i));
    }
    
    // The OpenJDK code uses valueOf by default for conversions
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
        return new bigint(value.divide(v.value));
    }
    
    public bigint mod(bigint v) {
        boolean neg = v.value.signum() < 0;
        return new bigint(value.remainder(v.value));
    }
    
    public boolean eq(bigint v) {
        return value.equals(v.value);
    }
    
    @Override
    public boolean equals(Object o) {
        return (o instanceof bigint b && eq(b));
    }
    
    @Override
    public int hashCode() {
        return value.hashCode();
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
        return new bigint(BigInteger.valueOf(-1).subtract(value));
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

    public long longValue() {
        return value.longValue();
    }

    public int intValue() {
        return value.intValue();
    }

    public short shortValue() {
        return value.shortValue();
    }

    public char charValue() {
        return (char)value.intValue();
    }

    public byte byteValue() {
        return value.byteValue();
    }

    public org.jmlspecs.lang.real realValue() {
        return org.jmlspecs.lang.real.of(value);
    }

}
