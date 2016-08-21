public class Block {
    private /*@ spec_public @*/ int[] contents; 

    /*@ public normal_behavior
      @   ensures \fresh(contents);
      @*/
    public Block() { contents = new int[10]; }

    /*@ public normal_behavior
      @   requires cont != null;
      @   assignable contents;
      @   ensures contents == cont;
      @*/
    public Block(int[] cont) {
        contents = cont;
    }

    /*@ public normal_behavior
      @   requires size >= 0;
      @   ensures \fresh(\result);
      @   ensures \fresh(\result.contents);
      @*/
    public static Block allocate(int size) {
        int[] cont = new int[size];
        return new Block(cont);
    }
}