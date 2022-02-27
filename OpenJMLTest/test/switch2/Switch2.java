// switch expression with patterns
public class Switch2 {

  static int m(Object o) {
    int j = switch (o) { case Integer k -> k+6; case String s->s.length()+6; default -> 0; };
    System.out.println("OUT " + j);
    return j;
  }

  public static void main(String... args) {
    m(9); m("asd"); m(5.6);
  }
}
    
