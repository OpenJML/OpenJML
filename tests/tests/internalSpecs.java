package tests;

/** These tests use the internal specs so that they trigger any checking of
 * specs that are referenced by Object.
 * @author David Cok
 *
 */
public class internalSpecs extends TCBase {


    @Override
    public void setUp() throws Exception {
//      noCollectDiagnostics = true;
//      jmldebug = true;
        useSystemSpecs = true;
        super.setUp();
    }

    /** Test scanning something very simple */
    public void testPure() {
        helpTC(" class A { /*@ pure */ boolean m() { return true; }  \n //@ invariant m(); \n}"
        );
    }

}
