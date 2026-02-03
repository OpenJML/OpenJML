public class Alice {
  //@ ensures \result.equals("lice");
  public String alice() {
    String alice="Alice";
    //@ assert alice.chars == \string.of("Alice");
    return alice.substring(1);
  }
  
  //@ ensures \result.chars == "lice".chars;
  //@ ensures \result.equals("lice");
  public String alice2() {
    String alice="Alice";
    //@ assert alice.chars == \string.of("Alice");
    return alice.substring(1,5);
  }

}