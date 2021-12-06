// openjml -rac T_RacOutput.java
public class T_RacOutput {

  public static void main(String... args) {
    checkArgs(args.length);
    System.out.println("END");
  }

  public static void checkArgs(int len) {
    //@ assert len == 1;
  }
}
