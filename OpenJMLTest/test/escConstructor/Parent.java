public class Parent {

  public /*@ non_null */ Object o;

  //@ ensures o.equals(oo);
  //@ pure
  public Parent(/*@ non_null*/ Object oo) {
     o = oo;
  }
}

