public abstract class IVec {

    //@ requires (\exists int i; 0 <= i && i < ivec.length; ivec[i] == 0);
    //@ ensures 0 <= \result <= ivec.length;
    public static /*@ pure @*/ int ivec_len(int ivec[]) {
        int count = 0;
        //@ loop_invariant 0 <= count <= ivec.length;
        //@ loop_invariant \forall int i; 0 <= i < count; ivec[i] != 0;
        while (ivec[count] != 0) {
            count++;
        }
        return count;
    }

    /*@ requires \exists int i; 0 <= i && i < target.length; 
      @                           target[i] == 0
      @         && (\forall int j; 0 <= j && j < src.length;
      @                            j <= i ==> src[j] != 0); @*/
    //@ requires target.length <= src.length;
    void ivec_add(int target[], int src[]) {
        int len = ivec_len(target);
        //@ loop_invariant 0 <= i <= len;
        for (int i = 0; i < len; i++) {
            target[i] += src[i];
        }
    }

    //@ requires true;
    //@ ensures \result <= i && \result <= j && (\result == i || \result == j);
    public static int min(int i, int j) {
        return i <= j ? i : j;
    }

    /*@ requires (\exists int i; 0 <= i && i < left.length; 
      @                           left[i] == 0)
      @       && (\exists int i; 0 <= i && i < right.length; 
      @                           right[i] == 0); @*/
    public static int ivec_cmp(int left[], int right[]) {
        int left_len = ivec_len(left);
        int rh_len = ivec_len(right);
        //@ loop_invariant 0 <= i <= left_len <= left.length;
        //@ loop_invariant 0 <= i <= rh_len <= right.length;
        for (int i = 0; i < min(left_len, rh_len); i++) {
            if (left[i] != right[i]) {
                return (left[i] < right[i] ? -1 : +1);
            }
        }
        // at this point left and right are equal up to their minimum length
        return (left_len < rh_len ? -1 : (left_len == rh_len ? 0 : +1));
    }

}
