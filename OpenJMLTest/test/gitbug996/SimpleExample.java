// gitbug996: a nullness modifier before a primitive array type (/*@ nullable */ int[] a)
// is misplaced -- it belongs on the array (int /*@ nullable */ [] a). OpenJML warns and
// uses it as if it were written there.
public class SimpleExample {

    //@ ensures \result <==> (a == null);
    //@ spec_pure
    public boolean isNull(/*@ nullable @*/ int[] a) { // warning; the array is nullable
        return a == null;
    }

    //@ ensures \result <==> (a == null);
    //@ spec_pure
    public boolean isNullRight(int /*@ nullable @*/ [] a) { // the correct position: no warning
        return a == null;
    }

    public void nonNull(/*@ non_null @*/ int[] a) { // warning; the array is non-null
        //@ assert a != null;
    }

    public int length(/*@ nullable @*/ int[] a) { // warning
        return a.length; // ERROR: a may be null
    }

    //@ requires a.length > 0;
    public void objects(/*@ nullable @*/ Object[] a) { // no warning: the elements are nullable
        //@ assert a != null;
        Object o = a[0]; // ERROR: an element may be null, but o is non_null
    }
}
