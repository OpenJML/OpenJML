@org.jmlspecs.annotation.Options("--escbv=false")
public class Test {
    
    public static void main(String... args) {
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
        //@ assert a == a;
        //@ set divzero();
        //@ set compare(a,b);
        //@ set bit(a,b);
        //@ set assignop(a,b);
        //@ assert a + b == 40; // FALSE
        System.out.println("END");
    }
    
/*@
    model public static void add(\bigint a, \bigint b) {
      var c = a + b;
      var d = c - a;
      assert d == b;
    }
    model public static void neg(\bigint a) {
      var c = -a;
      var d = -c;
      assert d == a;
      assert a == +a;
    }
    model public static void convert(\bigint a) {
      \bigint k = 42;
      assert 42 == (int)k;
      assert 42 == (long)k;
      assert 42 == (short)k;
      assert 42 == (byte)k;
    }
    requires a != 0;
    model public static void mul(\bigint a, \bigint b) {
      assert \bigint.zero == (\bigint)0;
      assert a != 0;
      var c = a * b;
      var d = c / a;
      assert d == b;
    }
    model public static void divzero() {
      var a = (\bigint)10;
      try { var b = a/\bigint.zero; } catch (Exception e) { System.out.println(e.getMessage()); }
      try { var c = a/0; } catch (Exception e) { System.out.println(e.getMessage()); }
      try { var e = a % 0; } catch (Exception e) { System.out.println(e.getMessage()); }
    }
    model public static void divzero1() {
      var a = (\bigint)10;
      var b = a/\bigint.zero;
    }
    model public static void divzero2() {
      var a = (\bigint)10;
      var c = a/0;
    }
    model public static void divzero3() {
      var a = (\bigint)10;
      var e = a % 0;
    }
    
    requires b != 0;
    model public static void mod(int a, int b) { mod((\bigint)a, (\bigint)b); }
    requires b != 0;
    model public static void mod(\bigint a, \bigint b) {
      var c = a % b;
      var d = a / b;
      assert a < 0 ==> c <= 0;
      assert c < 0 ==> a < 0;
      assert a == b * d + c;
    }
    model public static void shift(\bigint a) {
      var c = a << 2;
      var d = c >> 2;
      assert d == a;
      assert c == a * 4;
      c = -a << 2;
      d = c >> 2;
      assert d == -a;
      assert c == -a * 4;
      assert (a << 0) == a;
      assert (a >> 0) == a;
      d = c << -1;
      assert d == c >> 1;
      d = c >> -1;
      assert d == c << 1;
    }
    model public static void compare(\bigint a, \bigint b) {
      assert a < b <==> b > a;
      assert a <= b <==> b >= a;
      assert a <= b <==> (a < b | a == b);
      assert (a < b | a > b) <==> a != b;
      assert a==b <==> !(a != b);
    }
    model public static void bit(\bigint a, \bigint b) {
      assert (a & b) == ~(~a | ~b);
    }
*/
    @org.jmlspecs.annotation.Options("--escbv=auto")
    public static void bitesc(int a, int b) {
      assert (a & b) == ~(~a | ~b);
    }
/*@
    model public static void assignop(\bigint a, \bigint b) {
      var c = a;
      set c += b;
      assert c == a + b;
    }
 */
}