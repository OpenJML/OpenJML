public class Demo {

  //@ ensures false;
  public static void main(String ... args) {
    if (args.length == 1) {
        //@ assert false;
    }
    //@ halt;
    if (args.length == 2) {
      //@ assert false;
    }
  }
}
