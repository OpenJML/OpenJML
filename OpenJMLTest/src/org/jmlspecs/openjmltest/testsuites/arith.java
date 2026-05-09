package org.jmlspecs.openjmltest.testsuites;

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
    
    @Test
    public void modeChange() {
        helpTCText("Mode.java",
            """
            public class Mode {
            
              public static void main(String... args) {
                //@ ghost \\bigint b = \\bigint.one*2*Long.MAX_VALUE;;
                long ll = 0;
                //@ ghost var bbb = \\safe_math(\\bigint_math(b + Long.MAX_VALUE));
                //@ ghost var bb = \\safe_math((long)b + ll);
                //@ print bb;
              }
            }
            """
            ,"/Mode.java:6: error: the argument of \\safe_math must be cast to a Java integral type",35
            );
    }

    @Test
    public void modeChange2() {
        helpTCText("Mode.java",
            """
            public class Mode {
            
              public static void main(String... args) {
                //@ ghost \\bigint b = \\bigint.one*2*Long.MAX_VALUE;;
                long ll = 0;
                //@ ghost var bbb = \\java_math(\\bigint_math(b + Long.MAX_VALUE));
                //@ ghost var bb = \\java_math((long)b + ll);
                //@ print bb;
              }
            }
            """
            ,"/Mode.java:6: error: the argument of \\java_math must be cast to a Java integral type",35
            );
    }

}