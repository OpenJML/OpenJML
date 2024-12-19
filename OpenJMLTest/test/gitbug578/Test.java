public class Test {
    
    //@ public normal_behavior
    //-RAC@   requires java.math.BigInteger.parseable(s, 10);
    //@   old \bigint b = 10;
    public int m(String s) {
        return 0;
    }
    
    //@ public normal_behavior
    //@   old \bigint b = 10;
    //@   ensures \result == b;
    public int mb() {
        return 10;
    }
    
    //@ public normal_behavior
    //@   old \real b = 10;
    //@   ensures \result == b;
    public double mr(String s) {
        return 10;
    }
    

    //@ public normal_behavior
    //@   old \TYPE bbb = \type(Object);
    //@ also public normal_behavior
    //@   old int bbb = 20;
    public void mm(Integer t) {

    }
    
    public static void main(String... args) {
        var t = new Test();
        t.m("10");
        t.mb();
        t.mr("");
        t.mm(8);
    }

}