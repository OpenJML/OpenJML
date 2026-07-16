public class A {
  private final java.util.List names = new java.util.ArrayList<>();
  //@ public invariant getNames() != null; // invariant calls a non-pure accessor
  public java.util.List getNames() { return names; }
}
