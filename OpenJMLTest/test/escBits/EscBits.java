public class EscBits {
    
    public void m() {
        boolean b = true;
        boolean bb = false;
        //@ assert !(b & bb);
        //@ assert (b | bb);
        //@ assert (b ^ bb);
    }
    public void m1() {
        boolean b = true;
        boolean bb = false;
        //@ assert (b & bb); // FALSE
    }
    public void m2() {
        boolean b = true;
        boolean bb = false;
        //@ assert !(b & bb);
        //@ assert (b | bb);
        //@ assert (!b ^ bb); // FALSE
    }
}