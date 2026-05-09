package test;

/**
 * Java class with a trivially unsatisfiable JML postcondition.
 * Used by RunEscMarkerTest to confirm that ESC produces at least one error marker.
 */
public class Bad {
    //@ ensures false;
    public void alwaysFails() {
        // intentionally empty — ESC will report the postcondition is unprovable
    }
}
