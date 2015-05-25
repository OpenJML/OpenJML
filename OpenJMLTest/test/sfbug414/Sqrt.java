public class Sqrt {

double precision = 0.0001;

//@ ghost public static double eps = 0.00001;

/*@
@ requires x >= 0.0;
@ ensures org.jmlspecs.models.JMLDouble.approximatelyEqualTo(x, \result * \result, eps);
@*/
public double sqrt(double x) {
double a = 0, b = x, m = 0;
while (b - a > precision) {
m = (b + a) / 2;
if (m * m > x) {
b = m;
}
else {
a = m;
}
}
return m;
}
}