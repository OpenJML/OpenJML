import java.math.BigInteger;

public class AA {

  public void m1() {
    BigInteger b = BigInteger.ZERO;
    //@ assert b == \bigint.zero;
  }
  public void m2() {
    BigInteger b = BigInteger.ZERO;
    //@ assert (\bigint)b == \bigint.zero;
  }
}
