public class Test {

    public static void main(String... args) {
  //@     ghost String s = 
  //@     """
  //@     abc
  //@       def
  //@     ghi
  //@     """;
        //@ assume s.length() < 100;
        //@ set System.out.println("#"+s+"#");
        //@ show s.length();
        //@ assert s.length() == -1; // ERROR - is really 14
    }
}