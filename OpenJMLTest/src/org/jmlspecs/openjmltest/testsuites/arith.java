package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

// FIXME - needs documentation and more tests
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class arith extends TCBase {

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        //jmldebug = true;
        super.setUp();
    }
    
    /** See the FIXME in BigInteger.jml */
    @Test
    public void testSimpleJava() {
        helpTCText("A.java","public class A { java.math.BigInteger list; }");
    }

}