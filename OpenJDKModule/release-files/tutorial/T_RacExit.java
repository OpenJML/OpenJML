// openjml -rac T_RacExit.java
public class T_RacExit {

  public static void main(String... args) {
    //@ assert args.length == 1;
    System.exit(10);
  }
}
