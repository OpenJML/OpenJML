/** Scenario 1: Java field cField.  Scenario 2: JML ghost field cGhostField.
 *  No companion .jml file — all JML specs are inline and are attributed. */
public class C {
    public int cField = 0;               // (1) Java declaration in C.java
    //@ ghost public int cGhostField = 0; // (2) JML ghost declaration in C.java

    //@ requires cField >= 0;             // (1) cField used in C.java JML spec clause
    //@ requires cGhostField >= 0;        // (2) cGhostField used in C.java JML spec clause
    public int cMethod() {
        int x = cField;                  // (1) cField used in C.java Java body
        return x;
    }
}
