// False claims: each method must fail to verify (checks the proofs in JMLFloatingApprox are not vacuous)
public class JMLFloatingApproxBad {
    //@ public normal_behavior
    //@   requires Double.isNaN(d) || Double.isNaN(d2);
    //@   ensures \result;
    public static boolean withinEpsilonOf(double d, double d2, double epsilon) {
        return StrictMath.abs(d - d2) <= epsilon;
    }

    //@ public normal_behavior
    //@   ensures \result <==> StrictMath.abs(f - f2) < epsilon;
    public static boolean withinEpsilonOf(float f, float f2, float epsilon) {
        return StrictMath.abs(f - f2) <= epsilon;
    }

    //@ public normal_behavior
    //@   requires epsilon > 0.0;
    //@   ensures \result <==> StrictMath.abs(d - d2) <= epsilon;
    public static boolean relativelyEqualTo(double d, double d2, double epsilon) {
        double tolerance = StrictMath.max(StrictMath.abs(d), StrictMath.abs(d2)) * epsilon;
        return StrictMath.abs(d - d2) <= tolerance;
    }
}
