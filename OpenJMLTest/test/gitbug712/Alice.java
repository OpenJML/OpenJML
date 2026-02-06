public class Alice {
    public String lice = "lice";
    
  //@ ensures \result.equals(lice);
  public String alice() {
    String alice="Alice";
    //@ assert \forall \bigint i; i < 0 || i >= 5; alice.chars[i] == \string.empty[i];
    // @ assert alice.chars == \string.of("Alice");
    String r =  alice.substring(1);
    //@ assert \forall \bigint i;; r.chars[i] == ((0 <= i < 4)? alice.chars[i+1] : \string.empty[i]);
    //@ assert \forall \bigint i;; lice.chars[i] == ((0 <= i < 4 )? alice.chars[i+1] : \string.empty[i]);
    //@ assert r.chars == lice.chars;
  //@ assert r.equals(lice);
    return r;
  }
  
  //@ ensures \result.chars == "lice".chars;
  //@ ensures \result.equals("lice");
  public String alice2() {
    String alice="Alice";
    return alice.substring(1,5);
  }

}