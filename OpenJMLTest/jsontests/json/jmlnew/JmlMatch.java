// Exercises JmlMatchExpressionAdapter.
// Case expressions must start with a simple identifier (type patterns not yet implemented).
public class JmlMatch {
    Object obj;
    int x;

    //@ ensures \match (obj) { case o -> true; };
    public boolean single() { return true; }

    //@ ensures \match (x) { case zero -> true; case other -> false; };
    public boolean multi() { return x == 0; }
}
