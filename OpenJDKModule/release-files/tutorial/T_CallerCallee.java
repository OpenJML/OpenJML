// openjml -esc -progress T_CallerCallee.java
public class T_CallerCallee {

  public void caller1() {
     boolean b1 = lessThanDouble(5,4);
     //@ assert b1 == true;
     boolean b2 = lessThanDouble(9,4);
     //@ assert b2 == false;
  }

  public void caller2() {
     boolean b1 = lessThanDouble(-1, -2);
  }

  public void caller3() {
     boolean b2 = lessThanDouble(2, 2);
  }

  public void caller4() {
     boolean b = lessThanDouble(4,2);
     //@ assert b == true;
  }

  //@ requires x > y && y >= 0;
  //@ ensures \result == (x < y + y);
  public boolean lessThanDouble(int x, int y) {
    return x-y < y;
  }
} 
