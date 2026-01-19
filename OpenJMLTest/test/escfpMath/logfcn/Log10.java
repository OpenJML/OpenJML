public class Log10{
  public void log10Test1(double a) {
      double b = Math.log10(a);
      //@ assert (Double.isNaN(a) || a < 0) <==> Double.isNaN(b);
      //@ assert (a == Double.POSITIVE_INFINITY) ==> (b == Double.POSITIVE_INFINITY);
      //@ assert (a == 0) ==> b == Double.NEGATIVE_INFINITY;
      //@ assert (Double.isFinite(a) && a > 0) ==> Double.isFinite(b);

      //determine precision
      //Math.pow(10,a)-b < .01d || Math.pow(10,a)-b > .01d;
  }

}
