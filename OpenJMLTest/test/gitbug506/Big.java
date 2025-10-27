import java.math.BigInteger;
public class Big {
  public final BigInteger z = BigInteger.valueOf(0);
  //@ public invariant z.value == 0;
  public Big() {
    //@ assert z.intValue() == 0;
  }
}

class B {
  public final static BigInteger z = BigInteger.valueOf(0);

  //@ static public invariant z != null && z.value == 0;

  //@ static_initializer
}
