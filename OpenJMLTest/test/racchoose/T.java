public class T {

  public static void main(String ... args) {

     //@ assert (\choose int x; 5 <= x < 10) == 5;
     //@ assert (\choose int x; 5 < x <= 10; x >= 10) == 10;
     //@ assert (\choose long x; x > 10 && x < 100 && x > 15; x > 10) > 15;
     //@ assert (\choose char c; 'a' <= c <= 'z') >= 'A';
     //@ assert (\choose int x; 10 < x < 11) == 0; // ERROR
     System.out.println("END");
  }
}
