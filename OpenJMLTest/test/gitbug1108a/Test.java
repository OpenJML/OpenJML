// #1108: a final static field of another class (here java.math.MathContext.DECIMAL32) existed before
// a pure constructor call, so pure-method values on it are kept. The field's allocation bound was dropped.
import java.math.MathContext;
import java.math.RoundingMode;

public class Test {
    public static void staticOfOtherClass() {
        //@ assert MathContext.DECIMAL32.getPrecision() == 7;
        MathContext a = new MathContext(5);
        //@ assert MathContext.DECIMAL32.getPrecision() == 7;
    }
}
