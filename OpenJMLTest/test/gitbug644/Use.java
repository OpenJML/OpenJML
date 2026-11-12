// #644: the two axioms together once hung z3; check they are usable and consistent
//@ non_null_by_default
public class Use {
    /*@ immutable pure public static model class Content {
       no_state public Object mapsObject(nullable Object key);
       no_state public Object mapss(nullable Object key);
       no_state public boolean hasMapObject(nullable Object key);
     }
    @*/
    //@ axiom (\forall Content c; (\forall Object o; c.hasMapObject(o) ==> c.mapsObject(o) == c.mapss(o)));
    //@ axiom (\forall Content c; c.hasMapObject(null) ==> c.mapsObject(null) == c.mapss(null));

    //@ requires c.hasMapObject(o);
    //@ ensures c.mapsObject(o) == c.mapss(o);
    //@ model public static void ok(Content c, nullable Object o) {}

    //@ requires c.hasMapObject(null);
    //@ ensures c.mapsObject(null) == c.mapss(null);
    //@ model public static void okNull(Content c) {}

    //@ model public static void bad(Content c, Object o) { assert c.mapsObject(o) == c.mapss(o); } // fails
}
