/** No companion .jml — all specs here are attributed normally.
 *  Uses all four symbols from scenarios 1–4 in JML specs and Java body. */
public class B {
    public A aObj = new A();
    public C cObj = new C();

    //@ requires cObj.cField >= 0;          // (1) cField in B.java JML spec
    //@ requires cObj.cGhostField >= 0;     // (2) cGhostField in B.java JML spec
    //@ requires aObj.aField >= 0;          // (3) aField in B.java JML spec
    //@ requires aObj.ghostInAJml >= 0;     // (4) ghostInAJml in B.java JML spec
    public int bMethod() {
        int y = aObj.aField;               // (3) aField in B.java Java body
        return y;
    }
}
