package tests;

import org.junit.Ignore;
import org.junit.Test;

/** These tests exercise the RAC checking.  They compile a test class 
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
public class racArithmeticModes extends RacBase {

    /** Sets the classpath used for these tests.  The bin in the classpath
     * brings in the currently compiled runtime classes (so we don't have
     * to build jmlruntime.jar)
     */
    String[] ordrac = new String[]{jdk, "-ea", "-classpath","bin"+z+"bin-runtime"+z+"testdata",null};

    @Override
    public void setUp() throws Exception {
        testspecpath1 = "$A"+z+"$B"+z+"$SY";
        rac = ordrac;
        jdkrac = false;
        //noCollectDiagnostics = true; print = true;
        super.setUp();
        //main.addOptions("-verboseness=4");
        expectedNotes = 2;
        main.addOptions("-jmltesting");
    }
    
    @Override
    public void tearDown() throws Exception {
        testspecpath1 = "$A"+z+"$B";
    }


    @Test public void testNeg() {
        helpTCX("tt.TestJava","package tt; import static org.jmlspecs.lang.JML.*; public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = -i; System.out.println(\"END\");} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END"
                );
        
    }

    @Test public void testNegJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = -i; System.out.println(\"END\");} \n" +
                "}"
                ,"END"
                );
        
    }

    @Test public void testNegSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = -i; System.out.println(\"END\");} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END"
                );
        
    }

    @Ignore // FIXME - need to settle on how to handle int declarations in Math mode
    @Test public void testNegMath() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int j = Integer.MAX_VALUE; int k = -j; System.out.println(\"END\"); \n" +
                "int i = Integer.MIN_VALUE; int kk = -i; System.out.println(\"END\");} \n" +
                "}"
                ,"END"
                );
    }

    @Test public void testCompJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = ~i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 2147483647"
                );
    }
    @Test public void testCompSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = ~i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 2147483647"
                );
    }

    @Ignore // FIXME
    @Test public void testCompMath() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = ~i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 2147483647"
                );
    }


    @Test public void testSumJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; int k = i + i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END -2"
                );
    }

    @Test public void testSumSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; int k = i + i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END -2"
                );
    }

}
