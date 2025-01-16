
public class NoModelTest {
    //@ model int zzz;
    //@ model int yyy;
    //@ represents yyy = 9;
  
  public static void main(String... args) {
      NoModelTest t = new NoModelTest();
      //@ set System.out.println("RESULT-ZZZ: " + t.zzz);
      //@ set System.out.println("RESULT-YYY: " + t.yyy);
  }
}
