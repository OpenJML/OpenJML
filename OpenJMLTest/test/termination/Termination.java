public class Termination implements I {

  //@ requires 20 > i >= 0;
  //@ measured_by i;
  //@ spec_pure
  static public int f(int i) {
    //@ assume i > 0 ==> Integer.MIN_VALUE < i * f(i-1) < Integer.MAX_VALUE;
    return i == 0 ? 1 : i * f(i-1);
  }

  //-RAC@ requires i >= 0;
  //-RAC@ measured_by i;
  //-RAC@ model public \bigint sf(\bigint i) { return i == 0? 1 : i * sf(i-1); }

  //@ requires 20 > i >= 0;
  //@ ensures 2*\result == i*(i+1);
  //@ measured_by i;
  //@ assignable \nothing;
  static public int add(int i) {
    // @ assert 0 <= i < 20 ==> 0 <= i <= i*i;
    // @ assert 0 < i < 20 ==> (i-1)*(i-1)+i <= i*i;
    // @ assert 0 < i < 20 ==> \forall \bigint k;; 0 <= k <= (i-1)*(i-1) ==> 0 <= k+i <= i*i;
    return i == 0 ? 0 : i + add(i-1);
  }

  //@ requires i >= 0;
  //@assignable \nothing;
  //@ ensures \result == i;
  //@  measured_by i;
  static public int count(int i) {
    return i == 0 ? 0 : 1+count(i-1);
  }
  
  public void z(int i) {
      if (i > 1) z(i-2);
  }

  public static void main(String... args) {
    int i = f(10);
    i = add(10);
    i = count(10);
  }
}

interface I {
    
    //@ measured_by i;
    public void z(int i);
}
