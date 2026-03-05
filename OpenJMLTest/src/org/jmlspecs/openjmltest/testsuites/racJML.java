package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Test;

/** These tests exercise the RAC checking.  They compile a test class
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racJML extends RacBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("-jmltesting");
    }
        // FIXME - why are there no reports of failed assertions
    @Test
    public void testLBLObject() {
        helpRacText("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",\"Z\") != null; \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = Z"
                );
    }

    @Test
    public void testLBLString() {
        helpRacText("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ ghost nullable String x = JML.lbl(\"AL\",\"XYZ\"); assert x.equals(\"XYZ\"); \n" // using ghost decl to avoid duplicate evaluation
                +"  }\n"
                +"}"
                ,"LABEL AL = XYZ"
                );
    }

    @Test // Test to check that we have one evaluation
    public void testLBLStringDup() {
        helpRacText("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",\"XYZ\").equals(\"XYZ\"); \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = XYZ"
                );
    }

    @Test
    public void testLBLboolean() {
        helpRacText("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",args.length == 0); \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = true"
                );
    }

    @Test
    public void testLBLint() {
        helpRacText("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert \\lbl(AL,args.length) == 0; \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = 0"
                );
    }

    @Test
    public void testLBLlong() {
        helpRacText("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",(long)args.length) == 0; \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = 0"
                );
    }

    @Test
    public void testLBLshort() {
        helpRacText("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",(short)args.length) == 0; \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = 0"
                );
    }

    @Test
    public void testLBLbyte() {
        helpRacText("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",(byte)args.length) == 0; \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = 0"
                );
    }

    @Test
    public void testLBLchar() {
        helpRacText("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",'Z') == 'Z'; \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = Z"
                );
    }

    @Test
    public void testLBLdouble() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //  @ ensures (\\lbl INPUTX i) == \\result;
                  //@ ensures JML.lbl(\"INPUT\",i) == \\result;
                  public static double m(double i) { return i; }
                  public static void main(String... args) {
                     //@ assert JML.lbl("AL",5.0) != 0.0;
                  }
                }
                """
                ,"LABEL AL = 5.0"
                );
    }
}
