public class Behaviors {

  //@ requires i >= 0;
  //@ also
  //@ requires i <= 0;
  //@ behaviors disjoint;
  public static void m1(int i) {}

  //@ requires i >= 0;
  //@ also
  //@ requires i <= 0;
  //@ behaviors complete;
  public static void m2(int i) {}

  //@ requires i > 0;
  //@ also
  //@ requires i < 0;
  //@ behaviors complete;
  public static void m3(int i) {}

  public static void main(String ... args) {
    m1(1);
    m1(0);
    m2(0);
    m3(1);
    m3(0);
    //@ print "DONE";
  }
}
