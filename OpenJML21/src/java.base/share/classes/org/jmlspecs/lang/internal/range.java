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

    /** Creates a \\range value from its limits */
    public static range of(bigint lo, bigint hi) {
        return new range(lo, hi, false);
    }

    /** Tests whether a \\range value is empty */
    public boolean isEmpty() {
        return hiIsExclusive ? (hi.le(lo)) : (hi.lt(lo));
    }

    /** Tests whether two ranges are equal (same limits) */
    public boolean eq(range r) {
        return lo.eq(r.lo) && hi.eq(r.hi) && hiIsExclusive == r.hiIsExclusive;
    }

    /** Negation of eq */
    public boolean ne(range r) {
        return !eq(r);
    }

    /** Converts to a String */
    @Override
    public String toString() { return "(" + lo + ".." + hi + ")"; }
    
    /** Object.equals is not supported on JML primitive types -- use == or eq() instead */
    @Override
    public boolean equals(Object o) {
        throw new UnsupportedOperationException();
    }
    
    /** Computes a hashCode for the range value */
    @Override
    public int hashCode() { return lo.hashCode() + hi.hashCode()*3 + (hiIsExclusive ? 19:29); }

}
