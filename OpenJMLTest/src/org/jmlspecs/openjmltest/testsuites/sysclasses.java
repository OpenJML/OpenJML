package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class sysclasses extends TCBase {

    /** Tests using datagroup*/
    @Test public void testDataGroup() {
        helpTCText("A.java"," class A { //@ public model \\datagroup streamState;\n}"
                ); // Gives a symbol not found error if the org.jmlspecs.lang package is not loaded
    }
    
    // TODO _ adds checks on other system supplied classes that ought to be present

}
