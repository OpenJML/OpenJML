package tests;

import org.jmlspecs.openjml.JmlOptionName;


public class arith extends TCBase {

    static String testspecpath = "$A"+z+"$B"+z+"$SY";

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        //jmldebug = true;
        super.setUp();
    }
    
    /** See the FIXME in BigInteger.spec */
    public void testSomeJava() {
        options.put("-specs",   testspecpath);
        JmlOptionName.putOption(context,JmlOptionName.NOPURITYCHECK);
        helpTCF("A.java","public class A { java.math.BigInteger list; }");
    }

}