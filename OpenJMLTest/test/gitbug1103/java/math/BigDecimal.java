// A stub of java.math.BigDecimal, compiled from source into java.base (#1103). The specs of the JML runtime class
// org.jmlspecs.lang.internal.real, which has BigDecimal parameters, are loaded before this class's supertypes are
// entered; the interfaces of the erased type must not be cached as empty, else BigDecimal is not a Comparable in the
// SMT type axioms and the path after 'new BigDecimal()' is infeasible.
package java.math;

public class BigDecimal extends Number implements Comparable<BigDecimal> {
    public BigDecimal() {}

    public static BigDecimal make() {
        BigDecimal b = new BigDecimal();
        //@ reachable;
        return b;
    }

    public int compareTo(BigDecimal o) { return 0; }
    public int intValue() { return 0; }
    public long longValue() { return 0; }
    public float floatValue() { return 0; }
    public double doubleValue() { return 0; }
}
