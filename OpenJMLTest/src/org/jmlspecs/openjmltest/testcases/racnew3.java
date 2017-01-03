package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.RacBase;
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
    String[] ordrac = new String[]{jdk, "-ea", "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata",null};

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
    
    @Test
    public void testCast() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public static double d;\n"
                +"  public static float f;\n"
                +"  public static long l;\n"
                +"  public static int i;\n"
                +"  public static short s;\n"
                +"  public static char c;\n"
                +"  public static byte b;\n"
                
                +"    public static void main(String... args) {\n" 
                +"       i = 6; m0(); \n" 
                +"       i = 100000; m0bad(); \n" 
                +"    }\n" 
                
                +"  //@ requires i == 6;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m0() {\n"
                +"    s = (short)i;\n"
                +"    //@ assert s == i;\n"  // OK
                +"    b = (byte)i;\n"
                +"    //@ assert b == i;\n"  // OK // Line 20
                +"    c = (char)i;\n"
                +"    //@ assert c == i;\n"  // OK
                +"    l = (long)i;\n"
                +"    //@ assert l == i;\n"  // OK
                +"    int ii = (int)i;\n"
                +"    //@ assert ii == i;\n"  // OK

                +"    //@ assert i == (short)i;\n"
                +"    //@ assert i == (long)i;\n"
                +"    //@ assert i == (char)i;\n"
                +"    //@ assert i == (byte)i;\n"
                +"    //@ assert i == (int)i;\n"
                +"  }\n"
                 
                +"  //@ requires i == 100000;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m0bad() {\n"
                +"    s = (short)i;\n"
                +"    //@ assert s == i;\n"  // BAD // Line 37
                +"    b = (byte)i;\n"
                +"    //@ assert b == i;\n"  // BAD
                +"    c = (char)i;\n"
                +"    //@ assert c == i;\n"  // BAD
                +"    l = (long)i;\n"
                +"    //@ assert l == i;\n"  // OK
                +"    int ii = (int)i;\n"
                +"    //@ assert ii == i;\n"  // OK

                +"    //@ assert i == (short)i;\n" // BAD // Line
                +"    //@ assert i == (long)i;\n"
                +"    //@ assert i == (char)i;\n"
                +"    //@ assert i == (byte)i;\n"
                +"    //@ assert i == (int)i;\n"
                +"  }\n"
                 
                +"}"
                ,"/tt/TestJava.java:36: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:37: JML assertion is false"
                ,"/tt/TestJava.java:38: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:39: JML assertion is false"
                ,"/tt/TestJava.java:40: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:41: JML assertion is false"
                ,"/tt/TestJava.java:46: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:46: JML assertion is false"
                ,"/tt/TestJava.java:48: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:48: JML assertion is false"
                ,"/tt/TestJava.java:49: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:49: JML assertion is false"
                );
    }
    

    @Test
    public void testCast1() {
    	//main.addOptions("-show","-method=m0");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"    public static void main(String... args) {\n" 
                +"       m0(); \n" 
                +"    }\n" 
                
                +"  public static void m0() {\n"
                +"    {/*@ nullable */ Short s = null;\n"
                +"    try { //@ assert 0 == (short)s; \n} catch (NullPointerException e) {}\n" 
                +"    try { short d = (Short)null; \n} catch (NullPointerException e) {}\n"  // Lines 10-11
                +"    }\n"
                +"    {/*@ nullable */ Long s = null;\n"
                +"    try { //@ assert 0 == (long)s;\n} catch (NullPointerException e) {}\n" 
                +"    try { long d = (Long)null;\n} catch (NullPointerException e) {}\n"
                +"    }\n"
                +"    {/*@ nullable */ Byte s = null;\n"
                +"    try { //@ assert 0 == (byte)s;\n} catch (NullPointerException e) {}\n" 
                +"    try { byte d = (Byte)null;\n} catch (NullPointerException e) {}\n"
                +"    }\n"
                +"    {/*@ nullable */ Integer s = null;\n"
                +"    try { //@ assert 0 == (int)s;\n} catch (NullPointerException e) {}\n" 
                +"    try { int d = (Integer)null;\n} catch (NullPointerException e) {}\n"
                +"    }\n"
                +"    {/*@ nullable */ Character s = null;\n"
                +"    try { //@ assert 0 == (char)s;\n} catch (NullPointerException e) {}\n" 
                +"    try { char d = (Character)null;\n} catch (NullPointerException e) {}\n"
                +"    }\n"
                +"    {/*@ nullable */ Float s = null;\n"
                +"    try { //@ assert 0 == (float)s;\n} catch (NullPointerException e) {}\n" 
                +"    try { float d = (Float)null;}\n catch (NullPointerException e) {}\n"
                +"    }\n"
                +"    {/*@ nullable */ Double s = null;\n"
                +"    try { //@ assert 0 == (double)s;\n} catch (NullPointerException e) {}\n"
                +"    try { double d = (Double)null;\n} catch (NullPointerException e) {}\n"
                +"    }\n"
                +"    {/*@ nullable */ Boolean s = null;\n"
                +"    try { //@ assert (boolean)s;\n} catch (NullPointerException e) {}\n"
                +"    try { boolean d = (Boolean)null;\n} catch (NullPointerException e) {}\n"
                +"    }\n"
                
                +"  }\n"
                 
                +"}"
                ,"/tt/TestJava.java:8: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:10: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:14: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:16: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:20: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:22: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:26: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:28: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:32: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:34: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:38: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:40: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:44: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:46: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:50: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:52: JML Attempt to unbox a null object"
                );
    }
    

    @Test
    public void testCast2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"    public static void main(String... args) {\n" 
                +"       m1(); \n" 
                +"    }\n" 
                
                +"  public static void m1() {\n"
                +"    short s = (short)9;\n"
                +"    //@ assert 9 == (Short)s;\n" 
                +"  }\n"
                 
                +"}"
                );
    }
    
    @Test
    public void testVarargs() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"    public static void main(String... args) {\n" 
                +"       m1(args); \n" 
                +"       m1(); \n" 
                +"       m1(\"a\"); \n" 
                +"       m1(\"a\",\"b\"); \n" 
                +"    }\n" 
                
                +"  //@ requires args.length >= 0; \n"
                +"  //@ ensures args.length == \\result; \n"
                +"  public static int m1(String ... args) {\n"
                +"    return args.length;\n" 
                +"  }\n"
                 
                +"}"
                );
    }
    

}
