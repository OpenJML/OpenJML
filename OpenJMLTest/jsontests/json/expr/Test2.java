class Test2 {
    int i;
  //@ requires true ==> false;
  //@ requires true <==> false;
  //@ requires true <=!=> false;
  //@ requires !false;
  //@ ensures i == \old(i);
  void m() {
      this.m();
      //@ assert \lbl(A, true);
      //@ assume \forall int i; i >= 0; i > 0;
      //@ assume \exists int i; ; i > 0;
      //@ assert 0 == \let var i = 0; i;
      x: m();
  }
}
