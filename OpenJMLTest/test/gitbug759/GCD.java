public class GCD{
    /*@ public normal_behaviour
      @ requires n2 != 0;
      @ // ensures \result == n1%n2; 
      @*/
    public /*@ no_state @*/static int mod(int n1, int n2){
        return n1 % n2;
    }
    
    //@ ensures mod(n, 1) == 0;
    //@ no_state
    public static boolean lemmamod(int n) { return true; }
    
    //@ axiom \forall int n; -Integer.MAX_VALUE < n < Integer.MAX_VALUE; \forall int d; d != 0; mod(-n, d) == mod(n, d);
    
    /*@    requires 0 <= n <= Integer.MAX_VALUE;
	  @    ensures \result == n;
	  @ also
	  @    requires -Integer.MAX_VALUE <= n < 0;
	  @    ensures \result == -n; 
      @*/
    public /*@ no_state @*/ static int abs(int n){
        return (0 <= n) ? n : -n;
    }

      /*@ requires 0 < n1 < Integer.MAX_VALUE && 0 < n2 < Integer.MAX_VALUE;
        @ {|    
    @   ensures 1 <= \result <= n1 & \result <= n2;
    @   ensures mod(n1, \result) == 0 && mod(n2, \result) == 0;
    @   ensures (\forall int k; \result < k & k <= n1 & k <= n2; mod(n1, k) != 0 || mod(n2, k) != 0);
    @ also
    @   requires n1 == 0 && n2 == 0;
    @   ensures \result == -1;
    @ also
    @   requires n1 == 0 && n2 != 0;
    @   ensures \result == abs(n2);
    @ also
    @   requires n1 != 0 && n2 == 0;
    @   ensures \result == abs(n1);
        @ |} @*/
    public /*@ no_state @*/ static int gcd(int n1, int n2) throws IllegalArgumentException{
          //@ reachable
        int result = 1;
        if( n1 == 0 && n2 == 0){
            return -1;
        }
        if (n1 == 0 || n2 == 0){
            return n1 == 0 ? n2 : n1;
        }
        //@ assert n1 > 0 && n2 > 0;
        
        //@ assume lemmamod(n1) && lemmamod(n2);
        
        //@ reachable;
        //@ maintaining 0 < i && i <= n1+1 && i <= n2+1;
        //@ maintaining 1 <= result < i || (i == 1 && result == 1);
        //@ maintaining mod(n1, result) == 0 && mod(n2, result) == 0;
        //@ maintaining (\forall int k; result < k < i; mod(n1, k) != 0 || mod(n2, k)!= 0);
        //@ decreases n1 - i;
        for(int i = 1; i <= n2 && i <= n1; i++){
            //@ reachable;
            if(mod(n1, i) == 0 && mod(n2, i) == 0){
                result = i;
            }
            //@ assert 0 < i && i < n1+1 && i < n2+1;
            //@ assert 0 < result <= i;
            //@ assert mod(n1, result) == 0 && mod(n2, result) == 0;
            //@ assert (\forall int k; result < k <= i; mod(n1, k) != 0 || mod(n2, k)!= 0);
        }
        //@ reachable;

        //@ assert 1 <= result <= n1 && result <= n2;
        //@ assert mod(n1, result) == 0 && mod(n2, result) == 0;
        //@ assert (\forall int k; result < k <= n1 & k <= n2; mod(n1, k) != 0 || mod(n2, k)!= 0);

    // @   assume 1 <= result <= n1 & result <= n2;
    // @   assume mod(n1, result) == 0 && mod(n2, result) == 0;
    // @   assume (\forall int k; result < k <= n1 & k <= n2; mod(n1, k) != 0 || mod(n2, k) != 0);

        return result;
    }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE && -Integer.MAX_VALUE < d < Integer.MAX_VALUE;
    //@ requires n != 0 || d != 0;
    //@ ensures \result == (GCD.gcd(n/GCD.gcd(n,d), d/GCD.gcd(n,d)) == 1);
    //@ helper no_state
    public static boolean lemma(int n, int d) { /*@ show n, d; */  return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE && -Integer.MAX_VALUE < d < Integer.MAX_VALUE;
    //@ requires n != 0 || d != 0;
    //@ ensures \result == ((\lbl A GCD.gcd(n, d)) == (\lbl B GCD.gcd(-n,d)));
    //@ helper no_state
    public static boolean lemma2a(int n, int d) { /*@ show n, d; */  return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE && -Integer.MAX_VALUE < d < Integer.MAX_VALUE;
    //@ requires n != 0 || d != 0;
    //@ ensures \result == ((\lbl A GCD.gcd(n, d)) == (\lbl B GCD.gcd(n,-d)));
    //@ helper no_state
    public static boolean lemma2b(int n, int d) { /*@ show n, d; */  return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE && -Integer.MAX_VALUE < d < Integer.MAX_VALUE;
    //@ requires n != 0 || d != 0;
    //@ ensures \result == ((\lbl A GCD.gcd(n, d)) == (\lbl B GCD.gcd(-n,-d)));
    //@ helper no_state
    public static boolean lemma2c(int n, int d) { /*@ show n, d; */ return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE;
    //@ ensures \result == ((\lbl A GCD.gcd(n, 1)) == 1);
    //@ helper no_state
    public static boolean lemma4(int n) { /*@ show n; */ return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE;
    //@ requires n != 0;
    //@ ensures \result == ((\lbl A GCD.gcd(n, n)) == n);
    //@ helper no_state
    public static boolean lemma5(int n) { /*@ show n; */ return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE;
    //@ requires n != 0;
    //@ ensures \result == ((\lbl A GCD.gcd(0, n)) == abs(n));
    //@ helper no_state
    public static boolean lemma6(int n) { /*@ show n; */ return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE && -Integer.MAX_VALUE < d < Integer.MAX_VALUE;
    //@ requires n != 0 || d != 0;
    //@ ensures \result == ((\lbl A GCD.gcd(n, d)) == (\lbl B GCD.gcd(d,n)));
    //@ helper no_state
    public static boolean lemma7(int n, int d) { /*@ show n, d; */ return true; }

    //@ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE && -Integer.MAX_VALUE < d < Integer.MAX_VALUE;
    //@ requires n != 0 || d != 0;
    //@ ensures \result == ((\lbl A GCD.gcd(n, d)) == (\lbl B GCD.gcd(-n, -d)));
    //@ helper no_state
    public static boolean lemma8(int n, int d) { /*@ show n, d; */ return true; }

    // @ requires -Integer.MAX_VALUE < n < Integer.MAX_VALUE && k > 0 && g > 0;
    //@ requires -1000000 < n < 1000000 && k > 0 && g > 0;
    //@ ensures \result == (((\lbl A mod(n,g)) == 0 && (\lbl B mod(n/g,k)) == 0) ==> (\lbl C mod(n,k)) == 0);
    //@ helper no_state
    public static boolean lemma9(int n, int k, int g) { /*@ show n, k, g; */ return true; }

    //@ requires n != Integer.MIN_VALUE && d != 0;
    //@ ensures mod(n,d) == 0 ==> (n/d)*d == n;
    //@ helper no_state
    public static boolean divmod(int n, int d) { return true; }

}
