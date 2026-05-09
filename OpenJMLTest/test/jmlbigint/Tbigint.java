@org.jmlspecs.annotation.Options("--escbv=false")
public class Tbigint {
    public static void main(String... args) {
        inits();
        //@ ghost \bigint a = 10;
        //@ ghost \bigint b = (\bigint)20;
        //@ set add(a,b);
        //@ set neg(a);
        //@ set mul(a,b);
        //@ set mod(a,b);
        //@ set mod(20, 10);
        //@ set mod(20, 15);
        //@ set mod(-20, 15);
        //@ set mod(20, -15);
        //@ set mod(-20, -15);
        //@ set shift(a);
        //@ set convert(a);
        //@ check a == a;
        //@ set divzero();
        //@ set compare(a,b);
        //@ set bit(a,b);
        //@ set assignop(a,b);
        //@ set constants(); set show();
        //@ check a + b == 40; // FALSE
        misc(100);
        Tcasts.main(args);
        //+RAC@ set System.out.println("END");
    }
    
    /*@ pure */ public static void inits() {
        //@ ghost \bigint bint = (int)5;  check bint == 5; check bint == \bigint.of(5); check bint.intValue() == 5;
        //@ ghost \bigint bshort = (short)5;  check bshort == 5; check bshort == \bigint.of((short)5); check bshort.shortValue() == 5;
        //@ ghost \bigint blong = (long)5;  check blong == 5; check blong == \bigint.of(5L); check blong.longValue() == 5;
        //@ ghost \bigint bbyte = (byte)5;  check bbyte == 5; check bbyte == \bigint.of((byte)5); check bbyte.byteValue() == 5;
        //@ ghost \bigint bchar = 'c'; check bchar == 'c'; check bchar == \bigint.of('c'); check bchar.charValue() == 'c';
    }
    
    /*@ pure */ public static void misc(int c) {
        //@ check \bigint.empty() == \bigint.zero;
        //@ check \bigint.zero + 1 == \bigint.one;
        //@ ghost \bigint a = 45;
        //@ ghost \bigint b = 45;
        //@ check a.compareTo(b) == 0;
        //@ check a.compareTo(45) == 0;
        //@ check a.hashCode() == b.hashCode();
        //@ check a.hashCode() != \bigint.of(c).hashCode() ==> a != \bigint.of(c);
        //-ESC@ check a.toString().equals("45");
        try {
            //@ check a.equals(null);
        } catch (Exception e) {
            //+RAC@ set System.out.println(e);
        }
    }
        
/*@
    pure model public static void add(\bigint a, \bigint b) {
      var c = a + b;
      var d = c - a;
      assert d == b;
      check a + b == a.add(b);
      check a - b == a.subtract(b);
    }
    pure model public static void neg(\bigint a) {
      var c = -a;
      var d = -c;
      check d == a;
      check a == +a;
      check -a == a.negate();
      check +a == a;
    }
    pure model public static void convert(\bigint a) {
      \bigint k = 42;
      check 42 == (int)k;
      check 42 == (long)k;
      check 42 == (short)k;
      check 42 == (byte)k;
    }
    requires a != 0;
    pure model public static void mul(\bigint a, \bigint b) {
      check \bigint.zero == (\bigint)0;
      assert a != \bigint.zero;
      check a * b == a.multiply(b);
      check b/a == b.divide(a);
      var c = a * b;
      var d = c / a;
      //+ESC@ show a, b, c, d;
      //-ESC@ check d == b;   // FIXME -- the counterexample is inaccurate -- cf Github Issue #870
    }
    pure model public static void divzero() {
      var a = (\bigint)10;
      try { var b = a/\bigint.zero; } catch (Exception e) { System.out.println(e); } // ERROR
      try { var c = a/0; } catch (Exception e) { System.out.println(e); } // ERROR
      try { var e = a % 0; } catch (Exception e) { System.out.println(e); } // ERROR
    }
    pure model public static void divzero1() {
      var a = (\bigint)10;
      var b = a/\bigint.zero; // ERROR
    }
    pure model public static void divzero2() {
      var a = (\bigint)10;
      var c = a/0; // ERROR
    }
    model public static void divzero3() {
      var a = (\bigint)10;
      var e = a % 0; // ERROR
    }
    
    requires b != 0;
    pure model public static void mod(int a, int b) { mod((\bigint)a, (\bigint)b); }
    requires b != 0;
    pure model public static void mod(\bigint a, \bigint b) {
      var c = a % b;
      var d = a / b;
      check a < 0 ==> c <= 0;
      check c < 0 ==> a < 0;
      check a == b * d + c;
      check c == a.mod(b);
    }
    pure model public static void shift(\bigint a) {
      var c = a << 2;
      var d = c >> 2;
      check d == a;
      //-ESC@ check c == a * 4;
      c = -a << 2;
      d = c >> 2;
      check d == -a;
      //-ESC@ check c == -a * 4;
      check (a << 0) == a;
      check (a >> 0) == a;
      d = c << -1;
      check d == c >> 1;
      d = c >> -1;
      check d == c << 1;
      check (c << 4) == c.shiftLeft(4);
 //     check (c >> 4) == c.shiftRight(4);
      //-ESC@ check c << 1 == c*2;
    }
    pure model public static void compare(\bigint a, \bigint b) {
      check a < b <==> b > a;
      check a <= b <==> b >= a;
      check a <= b <==> (a < b | a == b);
      check (a < b | a > b) <==> a != b;
      check a==b <==> !(a != b);
      check a < b == a.lt(b);
      check a > b == a.gt(b);
      check a >= b == a.ge(b);
      check a <= b == a.le(b);
      check a != b == a.ne(b);
      check a == b == a.eq(b);
    }
    pure model public static void bit(\bigint a, \bigint b) {
//-ESC@      check (a & b) == ~(~a | ~b);
       check ~a == -a-1;
       check ~a == a.comp();
//-ESC@       check (a | b) == a.or(b);
//-ESC@       check (a & b) == a.and(b);
    }
*/
    @org.jmlspecs.annotation.Options("--escbv=auto")
    /*@ pure */ public static void bitesc(int a, int b) {
      assert (a & b) == ~(~a | ~b);
    }

/*@
    model public static void assignop(\bigint a, \bigint b) {
      var c = a;
      set c += b;
      check c == a + b;
    }
    
    model public static void show() {
      \bigint b = -4242;
      show b;
      unreachable; // To force a show
    }
    
    model public static void constants() {
        //@ check \bigint.zero == 0;
        //@ check \bigint.one == 1;
    }
 */
    
//    public static void test() {
//        //@ ghost \bigint bchar = 'c'; // check bchar == 'c'; check bchar == \bigint.of('c'); check bchar.charValue() == 'c';
//    }
}