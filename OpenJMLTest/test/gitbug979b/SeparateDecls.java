// gitbug979: with separate declarations, an 'in' clause applies only to the field just before it
// -- _b is in g, _a is not, so only _a is reported
public class SeparateDecls {
    //@ public model int g;
    private int _a;
    private int _b; //@ in g;
    //@ private represents g = _a + _b;
}
