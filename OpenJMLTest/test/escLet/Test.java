
//@ non_null_by_default
    public class Test {
        
        //@ normal_behavior
        //@   requires (\let int c = cc; c != 0);
        //@ pure
        Test(int cc) {
        }
        
        //@ normal_behavior
        //@   requires (\let int c = cc; c != 0);
        //@ pure
        void m(int cc) {
        }
    }