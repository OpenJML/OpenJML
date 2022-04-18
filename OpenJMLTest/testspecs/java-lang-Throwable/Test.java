public class Test {

    // FIXME - needs more
    
  public static void esc(/*@ nullable*/ String s) {
    var a = new Throwable();
    //@ assert a.getMessage() == null;
    //@ assert a.getCause() == null;
    a = new Throwable((String)null);
    //@ assert a.getMessage() == null;
    //@ assert a.getCause() == null;
    a = new Throwable(s);
    //@ assert a.getMessage() == s;
    //@ assert a.getCause() == null;

    try {
        a.initCause(a);
        //@ unreachable;
    } catch (IllegalArgumentException e) {
        // expected
    }

    var x = a.initCause(null);
    //@ assert a.getCause() == null;
    //@ assert x == a;
    //@ assert a.getMessage() == s;
    try {
        a.initCause(null); // May only call once
        //@ unreachable;
    } catch (IllegalStateException e) {
        //@ assert a.getCause() == null;
        // expected
    }

    var aa = new Throwable();
    x = aa.initCause(a);
    //@ assert x == aa;
    //@ assert aa.getCause() == a;
    //@ assert aa.getMessage() == null;
    try {
        aa.initCause(null); // May only call once
        //@ unreachable;
    } catch (IllegalStateException e) {
        //@ assert aa.getCause() == a;
        // expected
    }

}

  //@ skipesc
  public static void main(String... args) {
    esc("");
  }
}
