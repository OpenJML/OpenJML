class Foo {
  //@ invariant foo > 0;
  int foo;
  Integer dummy = new Integer(12);

  public static void main(String... args) {
    new Foo();
  }
}
