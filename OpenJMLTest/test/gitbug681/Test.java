
class TestJava {
  //@ requires System.out.outputText.isEmpty(); // TODO: Could be implied by a system startup property
  //@ ensures System.out.outputText == "foo".chars;
  public static void main(String[] args) {
    System.out.print("foo");
  }
}

class Main {
    //@ requires java.io.PrintStream.eol == "\n";
    //@ requires System.out.outputText.isEmpty();
    //@ ensures System.out.outputText.startsWith("foo\n".chars);
    //@ ensures System.out.outputText == \old(System.out.outputText) + "foo".chars + java.io.PrintStream.eol.chars;
  public static void m(String[] args) {
      //@ assert System.out.outputText == \string.empty;
    System.out.println("foo");
    //@ assert System.out.outputText == \string.empty.append("foo".chars);
    //@ assert System.out.outputText.startsWith("foo".chars);
  }
}
