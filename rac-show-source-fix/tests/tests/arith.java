package tests;

import org.jmlspecs.openjml.JmlOption;
import org.junit.Test;

// FIXME - needs documentation and more tests
public class arith extends TCBase {

    static String testspecpath = "$A"+z+"$B"+z+"$SY";

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        //jmldebug = true;
        super.setUp();
    }
    
    /** See the FIXME in BigInteger.spec */
    @Test
    public void testSomeJava() {
        options.put("-specspath",   testspecpath);
        JmlOption.setOption(context,JmlOption.PURITYCHECK,false);
        helpTCF("A.java","public class A { java.math.BigInteger list; }");
    }

}