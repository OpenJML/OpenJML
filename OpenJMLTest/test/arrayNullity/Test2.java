//@ non_null_by_default
public abstract class Test2 {

  abstract int[] m();

  void p() {
    int[] z = m();
  }
}

//@ nullable_by_default
abstract class Test3 {

  abstract int[] m();

  void p() {
    int[] z = m();
  }
}

abstract class Test4 {

  abstract int[] m();

  void p() {
    int[] z = m();
  }
}
