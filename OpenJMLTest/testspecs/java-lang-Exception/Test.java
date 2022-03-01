public class Test {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        esc("");
    }
    
    // FIXME - needs more

    //@ public normal_behavior
    public static void esc(/*@ nullable*/ String s) {
        var a = new Exception();
        //@ assert a.getMessage() == null;
        //@ assert a.getCause() == null;
        a = new Exception((String)null);
        //@ assert a.getMessage() == null;
        //@ assert a.getCause() == null;
        a = new Exception(s);
        //@ assert a.getMessage() == s;
        //@ assert a.getLocalizedMessage() == s;
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

        var aa = new Exception();
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
}
