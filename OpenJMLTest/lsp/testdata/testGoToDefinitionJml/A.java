/** Scenario 3: Java field aField — declared here, also stubbed in A.jml.
 *  Scenario 4: ghost field ghostInAJml — declared only in A.jml, used here in body assertions.
 *
 *  This file has a companion A.jml that REPLACES all method specs and class invariants
 *  written directly in this file.  Only in-body JML assertions (//@ assert) and plain
 *  Java code are attributed when the companion exists. */
public class A {
    public int aField = 0;               // (3) Java field declaration in A.java
    public C cObj = new C();

    // A.java method spec below is HIDDEN by A.jml companion — not attributed.
    //@ requires aField >= 0;            // (3) aField in A.java method spec (HIDDEN — not attributed)
    public int aMethod2() { return 0; } // spec stub in A.jml

    public void aBodyUses() {
        int x = aField;                  // (3) aField in A.java Java body
        //@ assert aField >= 0;          // (3) aField in A.java JML body assert
        //@ assert cObj.cField >= 0;     // (1) cField in A.java JML body assert
        //@ assert cObj.cGhostField >= 0; // (2) cGhostField in A.java JML body assert
        //@ assert ghostInAJml >= 0;     // (4) ghostInAJml in A.java JML body assert
    }
}
