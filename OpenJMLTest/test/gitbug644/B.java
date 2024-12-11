//@ non_null_by_default
public class B {
    public B() { }

    /*@ immutable pure public static model class Content {

       no_state helper
       public Object mapsObject(nullable Object key);

       no_state helper
       public Object mapss(nullable Object key);

       no_state helper
       public boolean hasMapObject(nullable Object key);

       no_state helper
       public boolean hasMap(nullable Object key);
     }
    @*/

  //@ axiom (\forall Content c; (\forall Object o; c.hasMapObject(o) ==> c.mapsObject(o) == c.mapss(o)) && c.hasMapObject(null) ==> c.mapsObject(null) == c.mapss(null));
  //@ axiom (\forall Content c; (\forall Object o; o != null; c.hasMapObject(o) ==> c.mapsObject(o) == c.mapss(o)));
  //@ axiom (\forall Content c; c.hasMapObject(null) ==> c.mapsObject(null) == c.mapss(null));
}
