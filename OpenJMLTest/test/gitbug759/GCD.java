public class GCD{
    /*@ public normal_behaviour
      @ requires n2 != 0;
      @ // ensures \result == n1%n2; 
      @*/
    public /*@ pure no_state @*/static int mod(int n1, int n2){
        return n1 % n2;
    }
    
    /*@    requires 0 <= n <= Integer.MAX_VALUE;
	  @    ensures \result == n;
	  @ also
	  @    requires Integer.MIN_VALUE < n < 0;
	  @    ensures \result == -n; 
      @*/
    public /*@ pure no_state @*/ static int abs(int n){
        return (0 <= n) ? n : -n;
    }

      /*@ requires -Integer.MAX_VALUE < nn1 < Integer.MAX_VALUE && -Integer.MAX_VALUE < nn2 < Integer.MAX_VALUE;
        @ {|    
    @   requires nn1 != 0 && nn2 != 0;
    @   ensures 1 <= \result <= abs(nn1) & \result <= abs(nn2);
    @   ensures mod(nn1, \result) == 0 && mod(nn2, \result) == 0;
    @   ensures (\forall int k; \result < k <= abs(nn1) & k <= abs(nn2); mod(nn1, k) != 0 || mod(nn2, k) != 0);
    @ also
    @   requires nn1 == 0 && nn2 == 0;
    @   ensures \result == -1;
    @ also
    @   requires nn1 == 0 && nn2 != 0;
    @   ensures \result == abs(nn2);
    @ also
    @   requires nn1 != 0 && nn2 == 0;
    @   ensures \result == abs(nn1);
        @ |} @*/
    public /*@ pure no_state @*/ static int gcd(int nn1, int nn2) throws IllegalArgumentException{
          //@ reachable
        int result = 1;
        int n1 = abs(nn1);
        int n2 = abs(nn2);
        if( nn1 == 0 && nn2 == 0){
            return -1;
        }
        if (nn1 == 0 || nn2 == 0){
            return nn1 == 0 ? n2 : n1;
        }
        //@ assert n1 > 0 && n2 > 0;
        
        //@ reachable;
        //@ maintaining 0 < i && i <= n1+1 && i <= n2+1;
        //@ maintaining 1 <= result < i || (i==1 && result ==1);
        // @ maintaining mod(n1, result) == 0 && mod(n2, result) == 0;
        // @ maintaining (\forall int k; 0 < k < i; (mod(n1, k) == 0 && mod(n2, k)== 0) ==> k <= result);
        // @ maintaining (\forall int k; result < k < i; mod(n1, k) != 0 || mod(n2, k)!= 0);
        //@ decreases n1 - i;
        for(int i = 1; i <= n2 && i <= n1; i++){
        //@ reachable;
            if(mod(n1, i) == 0 && mod(n2, i) == 0){
                result = i;
            }
         //@ assert 0 < i && i < n1+1 && i < n2+1;
        //@ assert 0 < result <= i;
        // @ assert mod(nn1, result) == 0 && mod(nn2, result) == 0;
        // @ assert (\forall int k; 0 < k <= i; (mod(nn1, k) == 0 && mod(nn2, k)== 0) ==> k <= result);
        // @ assert (\forall int k; result < k <= i; mod(nn1, k) != 0 || mod(nn2, k)!= 0);
	//@ reachable;
        }
        //@ reachable;

//@ assert 1 <= result <= n1 && result <= n2;
// @ assert mod(n1, result) == 0 && mod(n2, result) == 0;
// @ assert mod(nn1, result) == 0 && mod(nn2, result) == 0;
// @ assert (\forall int k; 0 < k <= n1 & k <= n2; (mod(nn1, k) == 0 && mod(nn2, k)== 0) ==> k <= result);
// @ assert (\forall int k; result < k <= n1 & k <= n2; mod(nn1, k) != 0 || mod(nn2, k)!= 0);

    //@   assume 1 <= result <= n1 & result <= n2;
    //@   assume mod(nn1, result) == 0 && mod(nn2, result) == 0;
    //@   assume (\forall int k; result < k <= n1 & k <= n2; mod(nn1, k) != 0 || mod(nn2, k) != 0);

        return result;
    }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE && -Integer.MAX_VALUE < d < Integer.MAX_VALUE;
    //@ requires n != 0 || d != 0;
    //@ ensures \result == (GCD.gcd(n/GCD.gcd(n,d), d/GCD.gcd(n,d)) == 1);
    //@ pure helper no_state
    public static boolean lemma(int n, int d) { /*@ show n, d; */  return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE && -Integer.MAX_VALUE < d < Integer.MAX_VALUE;
    //@ requires n != 0 || d != 0;
    //@ ensures \result == ((\lbl A GCD.gcd(n, d)) == (\lbl B GCD.gcd(-n,d)));
    //@ pure helper no_state
    public static boolean lemma2(int n, int d) { /*@ show n, d; */  return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE && -Integer.MAX_VALUE < d < Integer.MAX_VALUE;
    //@ requires n != 0 || d != 0;
    //@ ensures \result == ((\lbl A GCD.gcd(n, d)) == (\lbl B GCD.gcd(n,-d)));
    //@ pure helper no_state
    public static boolean lemma3(int n, int d) { /*@ show n, d; */ return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE;
    //@ ensures \result == ((\lbl A GCD.gcd(n, 1)) == 1);
    //@ pure helper no_state
    public static boolean lemma4(int n) { /*@ show n; */ return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE;
    //@ requires n != 0;
    //@ ensures \result == ((\lbl A GCD.gcd(n, n)) == n);
    //@ pure helper no_state
    public static boolean lemma5(int n) { /*@ show n; */ return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE;
    //@ requires n != 0;
    //@ ensures \result == ((\lbl A GCD.gcd(0, n)) == abs(n));
    //@ pure helper no_state
    public static boolean lemma6(int n) { /*@ show n; */ return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE && -Integer.MAX_VALUE < d < Integer.MAX_VALUE;
    //@ requires n != 0 || d != 0;
    //@ ensures \result == ((\lbl A GCD.gcd(n, d)) == (\lbl B GCD.gcd(d,n)));
    //@ pure helper no_state
    public static boolean lemma7(int n, int d) { /*@ show n, d; */ return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE && -Integer.MAX_VALUE < d < Integer.MAX_VALUE;
    //@ requires n != 0 || d != 0;
    //@ ensures \result == ((\lbl A GCD.gcd(n, d)) == (\lbl B GCD.gcd(-n, -d)));
    //@ pure helper no_state
    public static boolean lemma8(int n, int d) { /*@ show n, d; */ return true; }

    // @ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE && k > 0 && g > 0;
    //@ requires -1000000 < n < 1000000 && k > 0 && g > 0;
    //@ ensures \result == (((\lbl A mod(n,g)) == 0 && (\lbl B mod(n/g,k)) == 0) ==> (\lbl C mod(n,k)) == 0);
    //@ pure helper no_state
    public static boolean lemma9(int n, int k, int g) { /*@ show n, k, g; */ return true; }

    //@ requires n != Integer.MIN_VALUE && d != 0;
    //@ ensures mod(n,d) == 0 ==> (n/d)*d == n;
    //@ pure helper no_state
    public static boolean divmod(int n, int d) { return true; }

}
