// gitbug979: _a and _b are in g, _c is not -- only _c is reported
public class NotInGroup {
    //@ public model int g;
    private int _a, _b; //@ in g;
    private int _c;
    //@ private represents g = _a + _b + _c;
}
