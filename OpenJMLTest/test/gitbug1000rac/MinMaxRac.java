// gitbug1000: RAC of \max and \min. When no value satisfies the range, the expression is not
// defined and RAC reports it (as for \choose); a use guarded by a non-empty test is not reported.
public class MinMaxRac {
    public static void main(String[] args) {
        int[] a = {1, 7, 4};
        int[] e = {};
        //@ assert (\max int i; 0 <= i < a.length; a[i]) == 7;
        //@ assert (\min int i; 0 <= i < a.length; a[i]) == 1;
        System.out.println("nonempty ok");
        //@ assert (\max int i; 0 <= i < e.length; e[i]) == 0;
        System.out.println("after empty max");
        //@ assert e.length == 0 || (\max int i; 0 <= i < e.length; e[i]) >= e[0];
        System.out.println("guarded ok");
        //@ assert (\min int i; 0 <= i < e.length; e[i]) == 0;
        System.out.println("end");
    }
}
