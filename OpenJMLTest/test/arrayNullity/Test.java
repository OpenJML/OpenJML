import org.jmlspecs.annotation.*;

//@ nullable_by_default
public class Test {

    public void m1() {
        @NonNull Object[] o; // OK - onlyelements are null
        o = null; // OK
      }

      public void m2() {
        @NonNull Object[] o2 = new @NonNull Object[]{1}; // ERROR - null elements
        o2[0] = null; // ERROR
      }

      public void m2a() {
        var o2 = new @NonNull Object[]{1}; // ERROR - null elements
        o2[0] = null; // ERROR
      }

      public void m2b() {
        java.lang.@NonNull Object[] o2 = new @NonNull Object[]{1}; // ERROR - null elements
        o2[0] = null; // ERROR
      }

      public void m3() {
          Object @NonNull[] oooo;
          oooo = null; // ERROR
      }

      public void m4() {
          Object @NonNull[] oo = new Object[10];
          oo[0] = null; // OK
      }

      public void q1() {
          /*@ non_null*/ Object[] oq; // OK - onlyelements are null
          oq = null; // OK
      }

      public void q2() {
          /*@ non_null*/ Object[] o2 = new /*@ non_null*/ Object[]{1}; // ERROR - null elements
          o2[0] = null; // ERROR
      }

      public void q2a() {
          var o2 = new /*@ non_null*/ Object[]{1}; // ERROR - null elements
          o2[0] = null; // ERROR
      }

      public void q2b() {
          java.lang.@NonNull Object[] o2 = new /*@ non_null*/ Object[]{1}; // ERROR - null elements
          o2[0] = null; // ERROR
      }

      public void q3() {
          Object /*@ non_null*/[] oo;
          oo = null; // ERROR
      }

      public void q4() {
          Object /*@ non_null*/[] oo = new Object[10];
          oo[0] = null; // OK
      }

}

