public class LongBitsToDouble{
  //@ requires Double.isFinite(a);
  public static void longBitsToDoubleTest(long a)
  {
    double staticResult = Double.longBitsToDouble(a);
    Double instance = 0.0;
    double instanceResult = instance.longBitsToDouble(a);
    //@ assert (a == 0x7ff8000000000000L) ==> Double.isNaN(staticResult);
    //@ assert (a == 0x7ff8000000000000L) ==> Double.isNaN(instanceResult);
    //@ assert (a == 0x7ff0000000000000L) ==> (Double.compare(staticResult, Double.POSITIVE_INFINITY) == 0);
    //@ assert (a == 0x7ff0000000000000L) ==> (Double.compare(instanceResult, Double.POSITIVE_INFINITY) == 0);
    //@ assert (a == 0xfff0000000000000L) ==> (Double.compare(staticResult, Double.NEGATIVE_INFINITY) == 0);
    //@ assert (a == 0xfff0000000000000L) ==> (Double.compare(instanceResult, Double.NEGATIVE_INFINITY) == 0);
  }

  //@ requires Double.isFinite(a);
  public static void longValueTest(double a)
  {
    Double instance = a;
    long instanceResult = instance.longValue();
    //@ assert instanceResult == Double.doubleToLongBits(a);
  }

  //@ requires !Double.isFinite(a);
  public static void longValueTestAnomalies(double a)
  {
    Double instance = a;
    long instanceResult = instance.longValue();
    //@ assert Double.isNaN(a) ==> (instanceResult == 0x7FF8000000000000L);
    //@ assert (Double.compare(a, Double.POSITIVE_INFINITY) == 0) ==> (instanceResult == 0x7ff0000000000000L);
    //@ assert (Double.compare(a, Double.NEGATIVE_INFINITY) == 0) ==> (instanceResult == 0xfff0000000000000L);
  }
}
