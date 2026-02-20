// openjml --check T_Old.java
public class T_Old {

  //@ requires x > 0 && y > 0;
  //@ requires x < 10000 && y < 10000;
  //@ old \bigint g = Math.gcd(x,y); // spec from Math library
  //@ ensures \result == g+g+g;
  public int myGCD(int x, int y) {
     // some code
     int g = mygcd(x,y);
     return g+g+g;
  }

  //@ requires x > 0 && y > 0;
  //@ ensures \result == Math.gcd(x,y); // spec from Math library
  //@ pure
  public int mygcd(int x, int y) {
      return 0; // placeholder
  }
}
