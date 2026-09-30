public class B {
  private final java.util.List names = new java.util.ArrayList<>();
  //@ public invariant getNames() != null; // invariant calls a non-pure accessor
  //@ spec_pure helper
  public java.util.List getNames() { return names; }
}
