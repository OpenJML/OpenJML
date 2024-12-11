record R(int x, int y) {}
public class RR {
  public static int k;
  public static void m() {
    var rr = new R(4,5);
    //@ assert rr.x() == 4;
    k = 6;
    int y = rr.y();
    //@ assert k+y == 11; // check on y()'s frame condition
  }

  public static void main(String... args) {
    m();
  }
}

  
