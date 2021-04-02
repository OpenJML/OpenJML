public class Parent {

  public /*@ nullable */ Object o;

  //@ ensures o.equals(oo);
  //@ pure
  public Parent(/*@ non_null*/ Object oo) {
     o = oo;
  }
}

