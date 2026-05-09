public class Log1p{

  public void log1pTest1(double a) {
      //@ show a;
      double b = Math.log1p(a);
      double c = Math.log(1.0d + a);
      //@ assert (Double.isNaN(a) || a < -1.0) ==> Double.isNaN(b);
      //@ assert (a == Double.POSITIVE_INFINITY) ==> b == Double.POSITIVE_INFINITY;
      //@ assert (a == -1.0) ==> (b == Double.NEGATIVE_INFINITY);
      //@ assert (Double.isFinite(a) && (a > -1.0)) ==> Double.isFinite(b);

      //==> b-c < .01d && b-c > .01d;
  }

  public void log1pTest2(double d){
    double b = Math.log1p(d);
    //@ assert Double.isNaN(b);
  }

}
