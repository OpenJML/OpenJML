
class TestJava {
  //@ requires System.out.outputText.isEmpty(); // TODO: Could be implied by a system startup property
  //@ ensures System.out.outputText == "foo".chars;
  public static void main(String[] args) {
    System.out.print("foo");
  }
}

class Main {
    //@ requires System.out.outputText.isEmpty();
    //@ ensures System.out.outputText.startsWith("foo".chars);
    //@ ensures System.out.outputText.startsWith("foo\n".chars);
    //@ ensures System.out.outputText == \old(System.out.outputText) + "foo".chars + CharSequence.eol.chars;
  public static void m(String[] args) {
    System.out.println("foo");
  }
}
