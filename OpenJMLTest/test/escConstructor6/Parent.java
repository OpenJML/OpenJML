public class Parent {

  public /*@ non_null */ Integer o;

  //@ ensures o.equals(oo);
  //@ pure
  public Parent(/*@ non_null*/ Integer oo) {
     o = oo;
  }
}

