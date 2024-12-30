// package org.jmlspecs.lang;

/** A class that defines approximation methods for float and double.
 *
 * @author Gary T. Leavens
 */
public /*@ pure @*/ class JMLFloatingApprox {

    /** Tell whether absolute value of difference of d and d2
     *  is within the given epsilon.  If the difference of d and d2 is NaN,
     *  then the result is false.
     */
    /*@  public normal_behavior
      @    ensures \result <==> StrictMath.abs(d - d2) <= epsilon;
      @ also
      @  implies_that
      @   public normal_behavior
      @     requires Double.isNaN(d) || Double.isNaN(d2);
      @     ensures !\result;
      @*/
    public static boolean withinEpsilonOf(double d, double d2,
                                          double epsilon) {
        return StrictMath.abs(d - d2) <= epsilon;
    }

    /** Tell whether relative difference of d and d2 is 
     *   within the computed tolerance.
     *  @see #approximatelyEqualTo(double, double, double)
     */
    /*@ public normal_behavior
      @    requires epsilon > 0.0;
      @    old double tolerance 
      @      = StrictMath.max(StrictMath.abs(d), StrictMath.abs(d2)) * epsilon;
      @    ensures \result
      @       <==> JMLFloatingApprox
      @             .approximatelyEqualTo(d, d2, tolerance);
      @*/
    public static boolean relativelyEqualTo(double d, double d2,
                                            double epsilon) {
        double tolerance = StrictMath.max(StrictMath.abs(d), StrictMath.abs(d2))
                           * epsilon;
        return JMLFloatingApprox.approximatelyEqualTo(d, d2, tolerance);
    }
    
    /** Tell whether difference of d and d2 is within the given epsilon.
     *  @see #withinEpsilonOf(double, double, double)
     */
    /*@ public normal_behavior
      @    ensures \result 
      @       <==> JMLFloatingApprox.withinEpsilonOf(d, d2, epsilon);
      @*/
    public static boolean approximatelyEqualTo(double d, double d2,
                                        double epsilon) {
        return JMLFloatingApprox.withinEpsilonOf(d, d2, epsilon);
    }

    /** Tell whether absolute value of difference of f and f2
     *  is within the given epsilon.  If the difference of f and f2 is NaN,
     *  then the result is false.
     */
    /*@  public normal_behavior
      @    ensures \result <==> StrictMath.abs(f - f2) <= epsilon;
      @ also
      @  implies_that
      @   public normal_behavior
      @     requires Float.isNaN(f) || Float.isNaN(f2);
      @     ensures !\result;
      @*/
    public static boolean withinEpsilonOf(float f, float f2,
                                          float epsilon) {
        return StrictMath.abs(f - f2) <= epsilon;
    }

    /** Tell whether relative difference of this JMLFloat and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(float, float, float)
     */
    /*@ public normal_behavior
      @    requires epsilon > 0.0;
      @    old float tolerance 
      @      = StrictMath.max(StrictMath.abs(f), StrictMath.abs(f2)) * epsilon;
      @    ensures \result
      @       <==> JMLFloatingApprox
      @             .approximatelyEqualTo(f, f2, tolerance);
      @*/
    public static boolean relativelyEqualTo(float f, float f2,
                                            float epsilon) {
        float tolerance = StrictMath.max(StrictMath.abs(f), StrictMath.abs(f2))
                           * epsilon;
        return JMLFloatingApprox.approximatelyEqualTo(f, f2, tolerance);
    }
    
    /** Tell whether difference of this JMLFloat and the arg is 
     *   within the given epsilon.
     *  @see #withinEpsilonOf(float, float, float)
     */
    /*@ public normal_behavior
      @    ensures \result 
      @       <==> JMLFloatingApprox.withinEpsilonOf(f, f2, epsilon);
      @*/
    public static boolean approximatelyEqualTo(float f, float f2,
                                        float epsilon) {
        return JMLFloatingApprox.withinEpsilonOf(f, f2, epsilon);
    }
}

