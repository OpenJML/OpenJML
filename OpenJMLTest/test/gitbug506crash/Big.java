// This variant of gitbug506/Big.java causes a crash

import java.math.BigInteger;
public class Big {
  public final BigInteger z = BigInteger.valueOf(0);
  public Big() {
    //@ assert z.intValue() == 0;
  }
}

class B {
  public final static BigInteger z = BigInteger.valueOf(0);

  //@ static invariant z != null && z.intValue() == 0;

  //@ static_initializer
}
