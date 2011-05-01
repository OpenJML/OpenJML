package tests;

import org.jmlspecs.openjml.esc.JmlEsc;

import com.sun.tools.javac.util.Options;

public class escnew extends EscBase {

    protected void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        options.put("-newesc","");
        options.put("-noPurityCheck","");
        //options.put("-jmlverbose",   "");
        //options.put("-showbb",   "");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //options.put("-trace",   "");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
 
    // FIXME - causes a prover failure
//    public void testCollect() {
//        options.put("-showbb","");
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava extends java.io.InputStream implements Comparable<TestJava> { \n"
//                +"  //@ invariant \\type(Short) <: \\type(java.lang.Long);\n"
//                +"  public String m(java.lang.Integer i, Number b) {\n"
//                +"    java.util.Vector<Integer> v = new java.util.Vector<Integer>();\n"
//                +"    boolean bb = b instanceof Double;\n"
//                +"    Object o = (Class<?>)v.getClass();\n"
//                +"    v.add(0,new Integer(0));\n"  // FIXME add(0,0) fails because of a lack of autoboxing
//                +"    bb = v.elements().hasMoreElements();\n"
//                +"    return null; \n"
//                +"  }\n"
//                +"}\n"
//              );
//    }

    
    // Just testing a binary method
    // It gave trouble because the specs were missing
    public void testGen() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result ==4;\n"
                +"  public int m1bad() {\n"
                +"    return 1 + 2;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result == 3;\n"
                +"  public int m1ok() {\n"
                +"    return 1 + 2;\n"
                +"  }\n"
                
                +"  //@ requires x >= 0;\n"
                +"  //@ ensures \\result < 0;\n"
                +"  public int m2bad(int x) {\n"
                +"    return -x;\n"
                +"  }\n"
                
                +"  //@ requires x >= 0;\n"
                +"  //@ ensures \\result <= 0;\n"
                +"  public int m2ok(int x) {\n"
                +"    return -x;\n"
                +"  }\n"
                
                
                +"}"
                );
    }

}
