import org.jmlspecs.annotation.*;

public class ReturnNullable {

    @NonNull Integer ff = 0;

	  public static void main(String... args) {
	    var n = new NZZ<@NonNull Integer>();
            //@ check n.id(4,1) != null; // ERROR - ESC
            //@ check n.id(4,0) != null; // ERROR
            /*@ non_null */ Integer kk = n.id(4,0); // ERROR
            //@ check kk != null; // ERROR - RAC
            //@ print "END";
          }

    public void q() {
      /*@ non_null*/ Integer kk = null; // ERROR
    }

    public void r() {
      ff = null; // ERROR
    }

    public void t() {
      /*@ non_null */ NZZ<Integer> nn = new NZZ<>();
      nn = null; // ERROR
    } 
}

class NZZ<T> {
   //@ ensures \result == o || \result == null;
   //@ spec_pure
   public /*@ nullable */ T id(T o, int k) { return k == 0 ? null : o; }

   /*@ non_null */ public static NZZ<Integer> ff = new NZZ<>();

   public void r() {
     ff = null; // ERROR
   }
}
