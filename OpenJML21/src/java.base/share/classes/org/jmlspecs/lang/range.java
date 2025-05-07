/** This class is the runtime representation of the JML built-in primitive \range type. */
package org.jmlspecs.lang;
import org.jmlspecs.lang.internal.bigint;

//@ immutable pure 
public class range implements IJmlPrimitiveType {
	
    final public bigint lo;
    final public bigint hi;
    final public boolean hiIsExclusive;
    
    public range(bigint lo, bigint hi, boolean isExclusive) {
        this.lo = lo;
        this.hi = hi;
        this.hiIsExclusive = isExclusive;
    }

    public boolean eq(range r) {
        return lo.eq(r.lo) && hi.eq(r.hi) && hiIsExclusive == r.hiIsExclusive;
    }

    public boolean ne(range r) {
        return !eq(r);
    }

    public static range of(bigint lo, bigint hi ) {
        return new range(lo, hi, false);
    }

    @Override
    public String toString() { return "(" + lo + ".." + hi + ")"; }
    
    @Override
    public boolean equals(Object o) {
        return o != null && o instanceof range r && this.eq(r);
    }
    
    @Override
    public int hashCode() { return lo.hashCode() + hi.hashCode()*3 + (hiIsExclusive ? 19:29); }

}
