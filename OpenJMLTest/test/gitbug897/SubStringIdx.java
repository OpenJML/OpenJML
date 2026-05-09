//@ nullable_by_default
public class SubStringIdx {
    //@  requires pat != null && text != null;
    //@  requires \exists int i; 0 <= i <= text.chars.length - pat.chars.length; (\forall int j; 0 <= j < pat.chars.length; text.charAt(i+j) == pat.charAt(j));
    //@ also
    //@  requires pat != null && text != null;
    //@  requires !(\exists int i; 0 <= i <= text.chars.length - pat.chars.length; (\forall int j; 0 <= j < pat.chars.length; text.charAt(i+j) == pat.charAt(j)));
    // @ behaviors disjoint;
    public static int substringIdx(String pat, String text) {
        if (pat.length() > text.length())
            return -1;

        //@ maintaining 0 <= i <= text.chars.length - pat.chars.length + 1;
        //CANNOT PROVE@ maintaining \forall int k; 0 <= k < i; (\exists int l; 0 <= l < pat.chars.length; text.charAt(k+l) != pat.charAt(l));
        //@ loop_writes i;
        //@ decreases text.chars.length - pat.chars.length - i;
        for (int i = 0; i <= text.length() - pat.length(); i++) {
            int j = 0;
            //@ maintaining 0 <= j <= pat.chars.length;
            //@ maintaining !(j < pat.chars.length && text.charAt(i + j) == pat.charAt(j)) || \forall int k; 0 <= k < j; text.charAt(i + k) == pat.charAt(k);
            //@ loop_writes j;
            //@ decreases pat.chars.length - j;
            while (j < pat.length() && text.charAt(i + j) == pat.charAt(j)) {
                j++;
            }
            if (j == pat.length())
                return i;

            //@ assert j < pat.chars.length; // exit was due to mismatch
            //@ assert text.charAt(i + j) != pat.charAt(j); // witness for existential at k = i
        }
        return -1;
    }

    public void m(String pat, String text) {
        //@ ghost boolean b1 = pat != null && text != null && \exists int i; 0 <= i <= text.chars.length - pat.chars.length; (\forall int j; 0 <= j < pat.chars.length; text.charAt(i+j) == pat.charAt(j));
        //@ ghost boolean b2 = pat != null && text != null && !\exists int i; 0 <= i <= text.chars.length - pat.chars.length; (\forall int j; 0 <= j < pat.chars.length; text.charAt(i+j) == pat.charAt(j));
        //@ assert !(b1 && b2);
    }

    //@  requires pat != null && text != null;
    //@  old boolean b = \exists int i; 0 <= i <= text.chars.length - pat.chars.length; (\forall int j; 0 <= j < pat.chars.length; text.charAt(i+j) == pat.charAt(j));
    //@  {|
    //@     requires b;
    //@  also
    //@     requires !b;
    //@  |}
    //@ behaviors disjoint;
    public static int q(String pat, String text) {
        if (pat.length() > text.length())
            return -1;

        //@ maintaining 0 <= i <= text.chars.length - pat.chars.length + 1;
        //@ maintaining \forall int k; 0 <= k < i; (\exists int l; 0 <= l < pat.chars.length; text.charAt(k+l) != pat.charAt(l));
        //@ loop_writes i;
        //@ decreases text.chars.length - pat.chars.length - i;
        for (int i = 0; i <= text.length() - pat.length(); i++) {
            //@ assert \forall int k; 0 <= k < i; (\exists int l; 0 <= l < pat.chars.length; text.charAt(k+l) != pat.charAt(l));
            int j = 0;
            //@ maintaining 0 <= j <= pat.chars.length;
            //@ maintaining \forall int k; 0 <= k < j; text.charAt(i + k) == pat.charAt(k);
            //@ loop_writes j;
            //@ decreases pat.chars.length - j;
            while (j < pat.length() && text.charAt(i + j) == pat.charAt(j)) {
                j++;
            }
            //@ assert 0 <= j <= pat.chars.length;
            //@ assert !(j < pat.chars.length && text.charAt(i + j) == pat.charAt(j));
            if (j == pat.length())
                return i;
            //@ assert !(text.charAt(i + j) == pat.charAt(j));

            //@ assert j < pat.chars.length; // exit was due to mismatch
            //@ assert text.charAt(i + j) != pat.charAt(j); // witness for existential at k = i
            //@ assert (\exists int l; 0 <= l < pat.chars.length; text.charAt(i+l) != pat.charAt(l));
            //@ assert \forall int k; 0 <= k < i; (\exists int l; 0 <= l < pat.chars.length; text.charAt(k+l) != pat.charAt(l));
            //@ assert \forall int k; 0 <= k <= i; (\exists int l; 0 <= l < pat.chars.length; text.charAt(k+l) != pat.charAt(l));
        }
        //@ assert  \forall int k; 0 <= k <= text.chars.length - pat.chars.length; (\exists int l; 0 <= l < pat.chars.length; text.charAt(k+l) != pat.charAt(l));
        return -1;
    }

}


