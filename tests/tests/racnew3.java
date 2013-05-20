package tests;

import org.junit.Test;

/** These tests exercise the RAC checking.  They compile a test class 
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
public class racnew3 extends RacBase {

    /** Sets the classpath used for these tests.  The bin in the classpath
     * brings in the currently compiled runtime classes (so we don't have
     * to build jmlruntime.jar)
     */
    String[] ordrac = new String[]{jdk, "-ea", "-classpath","bin"+z+"bin-runtime"+z+"testdata",null};

    @Override
    public void setUp() throws Exception {
        rac = ordrac;
        jdkrac = false;
        //noCollectDiagnostics = true; print = true;
        super.setUp();
        //main.addOptions("-verboseness",   "4");
        expectedNotes = 0;
    }
    
    /** Tests not_modified */
    @Test public void testNotModified1() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*;  \n" +
                "public class TestJava { \n" +
                "    public static void main(String... args) {\n" +
                "       m(3);\n" +
                "    }" +
                "    public static void m(int i) {\n" +
                "       i = 3;\n" +
                "       //@ assert \\not_modified(i);\n" +
                "       i = 4;\n" +
                "       //@ assert \\not_modified(i);\n" + // FAILS
                "    }" +
                "}"
                ,"/tt/TestJava.java:9: JML assertion is false"
        );        
    }

    /** Tests not_modified */
    @Test public void testNotModified2() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*;  \n" +
                "public class TestJava { \n" +
                "    int f = 5;\n" +
                "    public static void main(String... args) {\n" +
                "       (new TestJava()).m(3,2);\n" +
                "    }" +
                "    public void m(int i, int j) {\n" +
                "       i = 4;\n" +
                "       //@ assert \\not_modified(j,this.f,f);\n" +
                "       f=6;\n" +
                "       //@ assert \\not_modified(this.f);\n" + // FAILS
                "    }" +
                "}"
                ,"/tt/TestJava.java:10: JML assertion is false"

        );        
    }

    /** Tests not_modified */
    @Test public void testNotModified3() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*;  \n" +
                "public class TestJava { \n" +
                "    int f = 5;\n" +
                "    public static void main(String... args) {\n" +
                "       (new TestJava()).m(3,2);\n" +
                "    }" +
                "    public void m(int i, int j) {\n" +
                "       i = 4;\n" +
                "       //@ assert \\not_modified(j,this.f,f);\n" +
                "       f=6;\n" +
                "       //@ assert \\not_modified(f);\n" + // FAILS
                "    }" +
                "}"
                ,"/tt/TestJava.java:10: JML assertion is false"

        );        
    }

    /** Tests not_modified */
    @Test public void testNotModified4() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*;  \n" +
                "public class TestJava { \n" +
                "    int f = 5;\n" +
                "    public static void main(String... args) {\n" +
                "       (new TestJava()).m(new int[]{1,2},7);\n" +
                "    }" +
                "    public void m(int[] a, int j) {\n" +
                "       j = 4;\n" +
                "       //@ assert \\not_modified(a[0]);\n" +
                "       a[0]=10;\n" +
                "       //@ assert \\not_modified(a[0]);\n" + // FAILS
                "    }" +
                "}"
                ,"/tt/TestJava.java:10: JML assertion is false"
        );        
    }

 
    // FIXME - need tests for X.f X.* o.* a[*] a[1..3] a[1..]
}
