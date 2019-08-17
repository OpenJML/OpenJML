
class TestJava {
  //@ requires System.out.outputText.isEmpty(); // TODO: Could be implied by a system startup property
  //@ ensures System.out.outputText == "foo";
  public static void main(String[] args) {
    System.out.print("foo");
  }
}
