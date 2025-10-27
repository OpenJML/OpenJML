/** This class is the runtime representation of the JML built-in primitive \range type. */
package org.jmlspecs.lang.internal;
import org.jmlspecs.lang.IJmlPrimitiveType;

//@ immutable no_state 
public class range implements IJmlPrimitiveType {
	
    final public bigint lo;
    final public bigint hi;
    final public boolean hiIsExclusive;
    
    private range(bigint lo, bigint hi, boolean isExclusive) {
        this.lo = lo;
        this.hi = hi;
        this.hiIsExclusive = isExclusive;
    }
    
    /** Creates an empty range */
    public static range empty() {
        return new range(bigint.of(0),bigint.of(-1),false);
        // The above needs explicit conversions because this library class 
        // is compiled with normal Java, not with OpenJML
    }

    /** Creates a \\range value from its non-exclusive limits */
    public static range of(bigint lo, bigint hi) {
        return new range(lo, hi, false);
    }

    /** Creates a \\range value from its limits */
    public static range of(bigint lo, bigint hi, boolean isExclusive) {
        return new range(lo, hi, isExclusive);
    }

    /** Tests whether a \\range value is empty */
    public boolean isEmpty() {
        return hiIsExclusive ? hi.le(lo) : hi.lt(lo);
    }

    /** Tests whether two ranges are equal (same limits) */
    public boolean eq(range r) {
        return lo.eq(r.lo) && ((hiIsExclusive == r.hiIsExclusive && hi.eq(r.hi))
                || (hiIsExclusive  && !r.hiIsExclusive && hi.eq(r.hi.add(bigint.one)))
                || (!hiIsExclusive  && r.hiIsExclusive && hi.eq(r.hi.subtract(bigint.one))));
    }

    /** Negation of eq */
    public boolean ne(range r) {
        return !eq(r);
    }

    /** Converts to a String */
    @Override
    public String toString() { return "(" + lo + ".." + hi + ")"; }
    
    public boolean equals(range r) {
        return eq(r);
    }

    /** Object.equals is not supported on JML primitive types -- use == or eq() instead */
    @Override
    public boolean equals(Object o) {
        return o instanceof range r && eq(r);
    }
    
    private range toHiEx() {
        if (hiIsExclusive) return this;
        return new range(lo, hi.add(bigint.one), true);
    }
    
    private range toNonEx() {
        if (!hiIsExclusive) return this;
        return new range(lo, hi.subtract(bigint.one), false);
    }
    
    /** Computes a hashCode for the range value */
    // Caution: must produce equal hashCodes for equal range values
    @Override
    public int hashCode() { return hiIsExclusive ? toNonEx().hashCode() : (lo.hashCode() + hi.hashCode()*3 + 42); }

}
