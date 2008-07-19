package tests;


public class racsystem extends RacBase {

    String[] sysrac = new String[]{"C:/Apps/jdk1.6.0/bin/java", "-Xbootclasspath/p:jdkbin;bin", "-classpath","jdkbin;bin;testdata",null};

    protected void setUp() throws Exception {
        rac = sysrac;
        jdkrac = true;
        //noCollectDiagnostics = true;
        super.setUp();
        //options.put("-jmlverbose",   "");
        //options.put("-noInternalSpecs",   "");
        //options.put("-useExceptions",   "");
    }

    public void testFile2() {
        expectedRACExit = 1;
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.useExceptions = true; \n"
                +"try { m(); } catch (Exception e) { e.printStackTrace(System.out); } \n"
                +"System.out.println(\"END\"); }"
                +"static void m() {\n"
                +"  int i = (new java.io.File(\"A\")).compareTo((java.io.File)null);\n"
                +"}"
                +"}"
                ,"Exception in thread \"main\" org.jmlspecs.utils.Utils$JmlAssertionFailure: File.refines-spec:77: JML precondition is false"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailure(Utils.java:28)"
                ,"\tat java.io.File.compareTo(File.java:1)"
                ,"\tat tt.TestJava.m(TestJava.java from TestJavaFileObject:5)"
                ,"\tat tt.TestJava.main(TestJava.java from TestJavaFileObject:3)"
                );
    }
    
    public void testFile3() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"try { m(); } catch (Exception e) {  } \n"
                +"System.out.println(\"END\"); }"
                +"static void m() {\n"
                +"  int i = (new java.io.File(\"A\")).compareTo((java.io.File)null);\n"
                +"}"
                +"}"
                ,"File.refines-spec:77: JML precondition is false"
                ,"File.refines-spec:115: JML unexpected exception"
                ,"END"
                );
    }
    
    public void testFile() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.showStack = true; \n"
                +"try { m(); } catch (Exception e) {  } \n"
                +"System.out.println(\"END\"); }"
                +"static void m() throws Exception {\n"
                +"  int i = (new java.io.File(\"A\")).compareTo((java.io.File)null);\n"
                +"}"
                +"}"
                ,"File.refines-spec:77: JML precondition is false"
                ,"org.jmlspecs.utils.Utils$JmlAssertionFailure: File.refines-spec:77: JML precondition is false"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailure(Utils.java:30)"
                ,"\tat java.io.File.compareTo(File.java:1)"
                ,"\tat tt.TestJava.m(TestJava.java from TestJavaFileObject:5)"
                ,"\tat tt.TestJava.main(TestJava.java from TestJavaFileObject:3)"
                ,"File.refines-spec:115: JML unexpected exception"
                ,"org.jmlspecs.utils.Utils$JmlAssertionFailure: File.refines-spec:115: JML unexpected exception"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailure(Utils.java:30)"
                ,"\tat java.io.File.compareTo(File.java:1)"
                ,"\tat tt.TestJava.m(TestJava.java from TestJavaFileObject:5)"
                ,"\tat tt.TestJava.main(TestJava.java from TestJavaFileObject:3)"
                ,"END"
                );
    }

    public void _testHashCode() {  // FIXME
        print = true;
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.showStack = true; \n"
                +"int i = ( new Object().hashCode()); \n"
                +"int j = ( new Object().hashCode()); \n"
                +" System.out.println(i==j);"
                +"System.out.println(\"END\"); }"
                +"}"
                ,"END"
                );
    }
    

}
