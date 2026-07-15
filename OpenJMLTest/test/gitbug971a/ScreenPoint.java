public class ScreenPoint {
    public static final int MAX_SIZE = 2048;
    //@ public static invariant 0 < MAX_SIZE;

    private /*@ spec_public @*/ int x, y;
    //@ public invariant 0 <= x < MAX_SIZE;
    //@ public invariant 0 <= y < MAX_SIZE;

    //@ requires 0 <= xv < MAX_SIZE;
    //@ requires 0 <= yv < MAX_SIZE;
    //@ ensures x == xv && y == yv;
    public ScreenPoint(int xv, int yv) {
        x = xv;
        y = yv;
    }

    public void test() {
        //@ assert 0 <= 5;
        //@ assert 0 <= 7 < MAX_SIZE;
        int oldMaxSize = MAX_SIZE;
        ScreenPoint p = new ScreenPoint(5, 7);
        //@ assert oldMaxSize == MAX_SIZE;
        //@ check p.x == 5 && p.y == 7;
        //@ assert 0 <= p.x;
        //@ assert 0 <= p.y < MAX_SIZE;
    }
}

