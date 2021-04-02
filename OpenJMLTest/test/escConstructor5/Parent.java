public class Parent {

  public /*@ non_null */ String o;

  //@ ensures o.equals(oo);
  //@ pure
  public Parent(/*@ non_null*/ String oo) {
     o = oo;
  }
}

