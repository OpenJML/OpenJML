public class Test {

    static public void dowhile() {
        int i = 2;
        //@ loop_invariant i >= 0 && (\count == 0 ==> i > 0);
        //@ split
        do { --i; } while (i > 0);
    }

    static public void boolsplit(int i) {
        //@ split i == 0;
        //@ assert i == 0;
    }

    //@ @org.jmlspecs.annotation.Options("--split=")
    static public void boolsplitB(int i) {
        //@ split i == 0;
        //@ assert i == 0;
    }
}
