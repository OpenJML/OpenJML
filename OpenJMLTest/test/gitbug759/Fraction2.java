public class Fraction2 {
    public final int numerator;
    public final int denominator;
    /*@ public invariant 0 < denominator < Integer.MAX_VALUE;
      @ public invariant Integer.MIN_VALUE + 1 < numerator < Integer.MAX_VALUE;
      @ public invariant numerator == 0 ==> denominator == 1;
      @ //public invariant \forall int k; 1 < k <= denominator & k <= GCD.abs(numerator); GCD.mod(numerator, k) != 0 || GCD.mod(denominator, k)!= 0;
    */
    //what I would want to write is
    // @ public invariant GCD.gcd(numerator, denominator) == 1;

    /*@ requires Integer.MIN_VALUE + 1 < numerator < Integer.MAX_VALUE;
      @ requires 0 <  denominator < Integer.MAX_VALUE;
      @ old int gcd = GCD.gcd(numerator, denominator);
      @ ensures this.numerator == numerator/gcd;
      @ ensures this.denominator == denominator/gcd;
      @ ensures equal(this, numerator, denominator);
      @ ensures GCD.gcd(this.numerator,this.denominator)==1;
      @ pure @*/
    public Fraction2(int numerator, int denominator){
//@ reachable;
        int gcd = GCD.gcd(numerator, denominator);
//@ reachable;
        this.numerator = numerator / gcd;
        this.denominator = denominator / gcd;
        //@ assume GCD.divmod(numerator,gcd);
        //@ assume GCD.divmod(denominator,gcd);
        //@ assume GCD.lemma(numerator,denominator);
//@ reachable;
        //@ assert GCD.gcd(this.numerator,this.denominator) == 1;
//@ reachable;
    }

/*@ 
     ensures \result == (a.numerator*b.denominator == a.denominator*b.numerator);
     pure model public static boolean equal(Fraction2 a, Fraction2 b);

     requires d != 0;
     ensures \result == (a.numerator*d == a.denominator*n);
     pure model public static boolean equal(Fraction2 a, \bigint n, \bigint d);
 */
    
    public static void main(String [] args){
      Fraction2 frac = new Fraction2(-10, 20);
      frac = frac.Inverse();
      System.out.println(String.valueOf(frac.numerator) + "/" + String.valueOf(frac.denominator));
    }
    /*@ requires f != null;
      @ old \bigint new_numerator = numerator * f.numerator;
      @ old \bigint new_denominator = denominator * f.denominator;
      @ requires Integer.MIN_VALUE + 1 < new_numerator < Integer.MAX_VALUE;
      @ requires 0 < new_denominator < Integer.MAX_VALUE;
      @ old int gcd = GCD.gcd((int)new_numerator, (int)new_denominator);
      @ ensures \result.numerator == new_numerator/gcd && \result.denominator == new_denominator/gcd;
      @ ensures equal(\result, new_numerator, new_denominator);
      @ pure @*/
    public Fraction2 Multiply(Fraction2 f){
        int new_numerator = this.numerator * f.numerator;
        int new_denominator = this.denominator * f.denominator;
        Fraction2 result = new Fraction2(new_numerator, new_denominator);
// @ assert GCD.gcd(result.numerator,result.denominator) == 1;
        return result;
    }

    /*@ requires f != null;
      @ requires -Integer.MAX_VALUE < this.numerator * f.denominator < Integer.MAX_VALUE;
      @ requires -Integer.MAX_VALUE < this.denominator * f.numerator < Integer.MAX_VALUE;
      @ old \bigint new_numerator = this.numerator * f.denominator + this.denominator * f.numerator;
      @ old \bigint new_denominator = this.denominator * f.denominator;
      @ requires -Integer.MAX_VALUE < new_numerator < Integer.MAX_VALUE;
      @ requires -Integer.MAX_VALUE < new_denominator < Integer.MAX_VALUE;
      @ old int gcd = GCD.gcd((int)new_numerator,(int)new_denominator);
      @ ensures \result.numerator == new_numerator/gcd && \result.denominator == new_denominator/gcd;
      @ ensures equal(\result, new_numerator, new_denominator);
     @ pure @*/
    public Fraction2 Add(Fraction2 f){
        int new_numerator = this.numerator * f.denominator + this.denominator * f.numerator;
        int new_denominator = this.denominator * f.denominator;
        //@ assume GCD.lemma(new_numerator,new_denominator);
        var result = new Fraction2(new_numerator, new_denominator);
         // @ assert GCD.gcd(result.numerator,result.denominator) == 1;
	return result;
   }

    /*@ requires Integer.MIN_VALUE+1< numerator < Integer.MAX_VALUE;
      @ requires 0 < denominator < Integer.MAX_VALUE;
      @ requires GCD.gcd(numerator,denominator)==1;
      @ ensures \result.numerator == -numerator;
      @ ensures \result.denominator == denominator;
      @ ensures equal(\result, -numerator, denominator);
      @ pure @*/
    public Fraction2 Inverse(){
        //@ assume GCD.lemma2(numerator,denominator);
        //@ assert GCD.gcd(-numerator,denominator) == 1;
        Fraction2 result =  new Fraction2(-numerator, denominator);
 // @ assert GCD.gcd(result.numerator,result.denominator) == 1;
       return result;
    }

    /*@ requires numerator != 0;
      @ requires Integer.MIN_VALUE + 1 < numerator < Integer.MAX_VALUE;
      @ requires 0 < denominator < Integer.MAX_VALUE;
      @ requires GCD.gcd(numerator,denominator)==1;
      @ ensures \result.denominator > 0;
      @ ensures \result.denominator == GCD.abs(numerator);
      @ ensures \result.numerator == ( numerator < 0 ? -denominator : denominator);
      @ ensures equal(\result, denominator, numerator);
      @ pure @*/
    public Fraction2 Reciprocal(){
        //@ show numerator, denominator;
        int d = numerator < 0 ? -denominator : denominator;
        int n = numerator < 0 ? -numerator : numerator;
        //@ assume GCD.lemma7(d,n);
        //@ assert GCD.gcd(d,n) == 1;
        Fraction2 result = new Fraction2(d, n);
 // @ assert GCD.gcd(result.numerator,result.denominator) == 1;
        return result;
    }
}
