public class Point2dU {
    /*@ spec_public */ private final int x; /*@ spec_public */ private final int y;
    //@ requires x > Integer.MIN_VALUE;
    //@ requires y > Integer.MIN_VALUE;
    //@ ensures \old(x) >= 0 ==> this.x == \old(x);
    //@ ensures \old(x) <  0 ==> this.x == -\old(x);
    public Point2dU(int x, int y) {
        if(x<0) x *= -1;
        if(y<0) y *= -1;
        this.x = x; this.y = y;
    }
}

