//@ nullable_by_default
public class Test extends A {
    
    public int i;
    
    public void mbyte(byte /*@ non_null */ [] b) {
        byte[] bb = b.clone();
        //@ assert i == \old(i);
        //@ assert bb != null;
        //@ assert \fresh(bb);
        //@ assert java.util.Arrays.equalArrays(bb,b);
    }
    
    public void mint(int /*@ non_null */ [] b) {
        int[] bb = b.clone();
        //@ assert i == \old(i);
        //@ assert bb != null;
        //@ assert \fresh(bb);
        //@ assert java.util.Arrays.equalArrays(bb,b);
    }
    
    public void mchar(char /*@ non_null */ [] b) {
        char[] bb = b.clone();
        //@ assert i == \old(i);
        //@ assert bb != null;
        //@ assert \fresh(bb);
        //@ assert java.util.Arrays.equalArrays(bb,b);
    }
    
    public void mshort(short /*@ non_null */ [] b) {
        short[] bb = b.clone();
        //@ assert i == \old(i);
        //@ assert bb != null;
        //@ assert \fresh(bb);
        //@ assert java.util.Arrays.equalArrays(bb,b);
    }
    
    public void mlong(long /*@ non_null */ [] b) {
        long[] bb = b.clone();
        //@ assert i == \old(i);
        //@ assert bb != null;
        //@ assert \fresh(bb);
        //@ assert java.util.Arrays.equalArrays(bb,b);
    }
    
    public void mboolean(boolean /*@ non_null */ [] b) {
        boolean[] bb = b.clone();
        //@ assert i == \old(i);
        //@ assert bb != null;
        //@ assert \fresh(bb);
        //@ assert java.util.Arrays.equalArrays(bb,b);
    }

    // FIXME - add these eventually
//    public void mfloat(/*@ non_null */ float[] b) {
//        float[] bb = b.clone();
//        //@ assert i == \old(i);
//        //@ assert bb != null;
//        //@ assert \fresh(bb);
//        //@ assert java.util.Arrays.equalArrays(bb,b);
//    }
//    
//    public void mdouble(/*@ non_null */ double[] b) {
//        double[] bb = b.clone();
//        //@ assert i == \old(i);
//        //@ assert bb != null;
//        //@ assert \fresh(bb);
//        //@ assert java.util.Arrays.equalArrays(bb,b);
//    }
    
    public void minherited() {
    }
    
    public void mtest() {
        minherited();
        //@ assert i == \old(i);
    }

}

class A {
    
    //@ public normal_behavior
    //@   assignable \nothing;
    public void minherited() {
        
    }
}