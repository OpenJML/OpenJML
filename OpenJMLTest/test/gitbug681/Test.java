
class TestJava {
  //@ ensures System.out.outputText.equals("foo");
  public static void main(String[] args) {
    System.out.println("foo");
  }
}
