public record Point2dU(int x, int y) {
    //@ requires x > Integer.MIN_VALUE;
    //@ requires y > Integer.MIN_VALUE;
    //@ ensures \old(x) >= 0 ==> this.x == x;
    //@ ensures \old(x) <  0 ==> this.x == -x;
    public Point2dU {
        if(x<0) x *= -1;
        if(y<0) y *= -1;
    }
}
