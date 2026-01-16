public class Test {
    
    public void m(int i) {
        int j;
      //@ choose { i<0 -> j=-1; or i > 0 -> j=1; or i == 0 -> { j = 0; }}
      //@ check j == (i>0 ? 1: i == 0? 0: -1);
    }
}