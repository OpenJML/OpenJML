package tests;

import org.jmlspecs.openjml.esc.JmlEsc;

import com.sun.tools.javac.util.Options;

public class esc extends EscBase {

    protected void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        options.put("-noPurityCheck","");
        options.put("-nullableByDefault",""); // Because the tests were written this way
        //options.put("-jmlverbose",   "");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //options.put("-trace",   "");
        //JmlEsc.escdebug = true;
        org.jmlspecs.openjml.provers.YicesProver.showCommunication = 1;
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
                
                +"  public void m1() {\n"
                +"    Integer a = Integer.valueOf(0);\n"
                +"  }\n"
                
                +"}"
                );
    }
    

    public void testForEach() {
//        options.put("-showbb","");
//        options.put("-counterexample","");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1() {\n"
                +"    long[] a = { 1,2,3,4};\n"
                +"    for (Long k: a) {\n"
                +"      //@ assert \\index >= 0;\n"  // OK
                +"      //@ assert \\index < a.length;\n"  // OK
                +"    }\n"
                +"  }\n"
                
                +"  public void m3() {\n"  // Line 10
                +"    long[] a = { 1,2,3,4};\n"
                +"    for (long k: a) {\n"
                +"      //@ assert \\index >= 1;\n"  // BAD
                +"    }\n"
                +"  }\n"
                
                +"  public void m4() {\n"
                +"    long[] a = { 1};\n"
                +"    long[] b = { 1,2};\n"
                +"    for (long k: a) {\n"
                +"      //@ ghost int i = \\index;\n"  // OK // Line 20
                +"      //@ assert \\index >= 0;\n"  // OK
                +"      for (long kk: b) {\n"
                +"         //@ assert \\index < 2;\n" // OK
                +"      }\n"
                +"      //@ assert \\index == i;\n"  // OK
                +"    }\n"
                +"  }\n"
                
                +"  public void m5() {\n"
                +"    long[] a = { 1,2,3,4};\n"
                +"    long[] b = { 1,2};\n" // Line 30
                +"    for (long k: a) {\n"
                +"      //@ ghost int i = \\index;\n"  
                +"      for (long kk: b) {\n"
                +"         //@ assert \\index == i;\n" // BAD
                +"      }\n"
                +"    }\n"
                +"  }\n"
                
                +"  public void m6() {\n"
                +"    long[] a = { 1,2,3,4};\n"
                +"    //@ loop_invariant \\index >= 0 && \\index <= a.length;\n" // OK
                +"    //@ decreases a.length - \\index;\n" // OK
                +"    for (long k: a) {\n"
                +"    }\n"
                +"  }\n"
                
                +"  public void m7() {\n"
                +"    long[] a = { 1,2,3,4};\n"
                +"    //@ decreases a.length - \\index -1;\n" // BAD // FIXME
                +"    for (long k: a) {\n"
                +"    }\n"
                +"  }\n"  // Line 50
                
                +"  public void m7a() {\n"
                +"    long[] a = { 1,2,3,4};\n"
                +"    //@ decreases \\index;\n" // BAD
                +"    for (long k: a) {\n"
                +"    }\n"
                +"  }\n"
                
                +"  public void m8() {\n"
                +"    long[] a = { 1,2,3,4};\n"
                +"    //@ loop_invariant \\index > 0 && \\index <= a.length;\n" // BAD - first time through loop
                +"    for (long k: a) {\n"
                +"    }\n"
                +"  }\n"
                
                +"  public void m9() {\n"
                +"    long[] a = { 1,2,3,4};\n"
                +"    //@ loop_invariant \\index >= 0 && \\index < a.length;\n" // BAD - last time through loop
                +"    for (long k: a) {\n"
                +"    }\n"
                +"  }\n"
                
                
                +"  public void m2() {\n"
                +"    long[] a = { };\n"
                +"    for (Long k: a) {\n"
                +"      //@ assert \\index >= 0;\n"  // OK
                +"      //@ assert \\index < a.length;\n"  // OK
                +"    }\n"
                +"  }\n"
                
                +"  public void m10() {\n"
                +"    long[] a = {  };\n"
                +"    long[] b = { 1,2};\n"
                +"    for (long k: a) {\n"
                +"      //@ ghost int i = \\index;\n"  // OK 
                +"      //@ assert \\index >= 0;\n"  // OK
                +"      for (long kk: b) {\n"
                +"         //@ assert \\index < 2;\n" // OK
                +"      }\n"
                +"      //@ assert \\index == i;\n"  // OK
                +"    }\n"
                +"  }\n"
                
                +"  public TestJava() {}\n"
                +"}"
                
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method m3",11
                ,"/tt/TestJava.java:34: warning: The prover cannot establish an assertion (Assert) in method m5",14
                ,"/tt/TestJava.java:55: warning: The prover cannot establish an assertion (LoopDecreases) in method m7a",5
                ,"/tt/TestJava.java:53: warning: Associated declaration",9
                ,"/tt/TestJava.java:60: warning: The prover cannot establish an assertion (LoopInvariantBeforeLoop) in method m8",5
                ,"/tt/TestJava.java:59: warning: Associated declaration",9
                ,"/tt/TestJava.java:67: warning: The prover cannot establish an assertion (LoopInvariant) in method m9",5
                ,"/tt/TestJava.java:65: warning: Associated declaration",9
                );
    }

    public void testForEach1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1() {\n"
                +"    Integer[] a = { 1,2,3,4};\n"
                +"    //@ loop_invariant \\values.size() == \\index;\n"
                +"    for (Integer k: a) {\n"
                +"    }\n"
                +"  }\n"
                
                +"  public void m2() {\n"
                +"    Integer[] a = { 1,2,3,4};\n"
                +"    //@ loop_invariant \\values.size() == \\index;\n"
                +"    for (Integer k: a) {\n"
                +"      //@ assert \\values.size() == \\index;\n" 
                +"    }\n"
                +"  }\n"
                
                +"  public void m3() {\n"
                +"    Integer[] a = { 1,2,3,4};\n"
                +"    for (Integer k: a) {\n"
                +"      //@ assert \\values.size() == \\index;\n" 
                +"    }\n"
                +"  }\n"
                
                +"  public TestJava() {}"
                
//                +"  public void m3() {\n"  // Line 10
//                +"    long[] a = { 1,2,3,4};\n"
//                +"    for (long k: a) {\n"
//                +"      //@ assert \\index >= 1;\n"  // BAD
//                +"    }\n"
//                +"  }\n"
//                
//                +"  public void m4() {\n"
//                +"    long[] a = { 1,2,3,4};\n"
//                +"    long[] b = { 1,2};\n"
//                +"    for (long k: a) {\n"
//                +"      //@ ghost int i = \\index;\n"  // OK
//                +"      //@ assert \\index >= 0;\n"  // OK
//                +"      for (long kk: b) {\n"
//                +"         //@ assert \\index < 2;\n" // OK
//                +"      }\n"
//                +"      //@ assert \\index == i;\n"  // OK
//                +"    }\n"
//                +"  }\n"
//                
//                +"  public void m5() {\n"
//                +"    long[] a = { 1,2,3,4};\n"
//                +"    long[] b = { 1,2};\n" // Line 30
//                +"    for (long k: a) {\n"
//                +"      //@ ghost int i = \\index;\n"  
//                +"      for (long kk: b) {\n"
//                +"         //@ assert \\index == i;\n" // BAD
//                +"      }\n"
//                +"    }\n"
//                +"  }\n"
//                
//                +"  public void m6() {\n"
//                +"    long[] a = { 1,2,3,4};\n"
//                +"    //@ loop_invariant \\index >= 0 && \\index <= a.length;\n" // OK
//                +"    //@ decreases a.length - \\index;\n" // OK
//                +"    for (long k: a) {\n"
//                +"    }\n"
//                +"  }\n"
//                
//                +"  public void m7() {\n"
//                +"    long[] a = { 1,2,3,4};\n"
//                +"    //@ decreases a.length - \\index -1;\n" // BAD // FIXME
//                +"    for (long k: a) {\n"
//                +"    }\n"
//                +"  }\n"  // Line 50
//                
//                +"  public void m7a() {\n"
//                +"    long[] a = { 1,2,3,4};\n"
//                +"    //@ decreases \\index;\n" // BAD
//                +"    for (long k: a) {\n"
//                +"    }\n"
//                +"  }\n"
//                
//                +"  public void m8() {\n"
//                +"    long[] a = { 1,2,3,4};\n"
//                +"    //@ loop_invariant \\index > 0 && \\index <= a.length;\n" // BAD - first time through loop
//                +"    for (long k: a) {\n"
//                +"    }\n"
//                +"  }\n"
//                
//                +"  public void m9() {\n"
//                +"    long[] a = { 1,2,3,4};\n"
//                +"    //@ loop_invariant \\index >= 0 && \\index < a.length;\n" // BAD - last time through loop
//                +"    for (long k: a) {\n"
//                +"    }\n"
//                +"  }\n"
                
                +"}"
                
//                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method m3",11
//                ,"/tt/TestJava.java:34: warning: The prover cannot establish an assertion (Assert) in method m5",14
//                ,"/tt/TestJava.java:54: warning: The prover cannot establish an assertion (LoopDecreases) in method m7a",21
//                ,"/tt/TestJava.java:53: warning: Associated declaration",9
//                ,"/tt/TestJava.java:60: warning: The prover cannot establish an assertion (LoopInvariant) in method m8",5
//                ,"/tt/TestJava.java:59: warning: Associated declaration",9
//                ,"/tt/TestJava.java:66: warning: The prover cannot establish an assertion (LoopInvariant) in method m9",21
//                ,"/tt/TestJava.java:65: warning: Associated declaration",9
                );
    }

    // FIXME - troubles with enhanced-for statements with complicated generics
    public void _testForEach2() {
        helpTCX("tt.TestJava","package tt; import java.util.*; \n"
                +"public class TestJava { \n"
                
//                +"  public void m1() {\n"
//                +"    Set<Map.Entry<String,String>> a = new HashSet<Map.Entry<String,String>>();\n"
//                +"    for (Map.Entry<String,String> k: a) {\n"
//                +"    }\n"
//                +"  }\n"
                                
                +"  public void m2() {\n"
                +"    int index = 0;\n"
                +"    List<Map.Entry<String,String>> values = new LinkedList<Map.Entry<String,String>>(); //@ assume values != null; set values.containsNull = true; \n"
                +"    Set<Map.Entry<String,String>> a = new HashSet<Map.Entry<String,String>>(); //@ assume a != null; \n"
                +"    Iterator<Map.Entry<String,String>> it = a.iterator(); //@ assume it != null; \n"
                +"    Map.Entry<String,String> k;\n"
                +"    for (; it.hasNext(); values.add(k) ) {\n"
                +"        k = it.next();  //@ assume \\typeof(k) <: \\type(Map.Entry); \n"
                +"    }\n"
                +"  }\n"
                                
                +"  public TestJava() {}"
                
                +"}"
                
//                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method m3",11
//                ,"/tt/TestJava.java:34: warning: The prover cannot establish an assertion (Assert) in method m5",14
//                ,"/tt/TestJava.java:54: warning: The prover cannot establish an assertion (LoopDecreases) in method m7a",21
//                ,"/tt/TestJava.java:53: warning: Associated declaration",9
//                ,"/tt/TestJava.java:60: warning: The prover cannot establish an assertion (LoopInvariant) in method m8",5
//                ,"/tt/TestJava.java:59: warning: Associated declaration",9
//                ,"/tt/TestJava.java:66: warning: The prover cannot establish an assertion (LoopInvariant) in method m9",21
//                ,"/tt/TestJava.java:65: warning: Associated declaration",9
                );
    }

    public void testForEachBad() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1a() {\n"
                +"    long[] a = { 1,2,3,4};\n"
                +"    for (long k: a) {\n"
                +"    }\n"
                +"    //@ ghost int i = \\index;\n"  // Out of scope
                +"  }\n"
                
                +"  public void m2() {\n"
                +"    long[] a = { 1,2,3,4};\n"
                +"    //@ ghost int i = \\index;\n"  // Out of scope
                +"  }\n"
                
                +"  public void m4() {\n"
                +"    long[] a = { 1,2,3,4};\n"
                +"    for (long k: a) {\n"
                +"      //@ set \\index = 6;\n"  // Syntax error
                +"    }\n"
                +"  }\n"
                
                +"  public void v1a() {\n"
                +"    Integer[] a = { 1,2,3,4};\n"
                +"    for (Integer k: a) {\n"
                +"    }\n"
                +"    //@ ghost org.jmlspecs.lang.JMLList i = \\values;\n"  // Out of scope
                +"  }\n"
                
                +"  public void v2() {\n"
                +"    long[] a = { 1,2,3,4};\n"
                +"    //@ ghost org.jmlspecs.lang.JMLList i = \\values;\n"  // Out of scope
                +"  }\n"
                
                +"  public void v4() {\n"
                +"    Integer[] a = { 1,2,3,4};\n"
                +"    for (Integer k: a) {\n"
                +"      //@ set \\values = null;\n"  // Syntax error
                +"    }\n"
                +"  }\n"
                
                +"  public void v10a() {\n"
                +"    long[] a = { 1,2,3,4};\n"
                +"    for (long k: a) {\n"
                +"      //@ ghost org.jmlspecs.lang.JMLList i = \\values;\n"  // OK
                +"    }\n"
                +"  }\n"
                
                +"}"
                
                ,"/tt/TestJava.java:7: A \\index token is used outside the scope of a foreach loop",23
                ,"/tt/TestJava.java:11: A \\index token is used outside the scope of a foreach loop",23
                ,"/tt/TestJava.java:16: unexpected type\n  required: variable\n  found:    value",15
                ,"/tt/TestJava.java:23: A \\values token is used outside the scope of a foreach loop",45
                ,"/tt/TestJava.java:27: A \\values token is used outside the scope of a foreach loop",45
                ,"/tt/TestJava.java:32: unexpected type\n  required: variable\n  found:    value",15
                );
    }

    // Test well-definedness within the implicit old
    public void testNonNullElements() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1(Object[] a) {\n"
                +"    //@ assume \\nonnullelements(a);\n"
                +"    //@ assume a.length > 1;\n"
                +"    //@ assert a[0] != null;\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m11(Object[] a) {\n"
                +"    //@ assume \\nonnullelements(a);\n"
                +"    //@ assert a != null;\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m11a(Object[] a) {\n"
                +"    //@ assume \\nonnullelements(a);\n"
                +"    //@ assert a == null;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1a(Object[] a) {\n"
                +"    //@ assume a != null && a.length > 1;\n"
                +"    //@ assert a[0] != null;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m2(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 0;\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m22(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 0;\n"
                +"    //@ assert (\\forall int i; 0<=i && i<a.length; a[i] != null);\n" // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m3(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 1;\n"
                +"    a[0] = new Object();\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m33(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 1;\n"
                +"    //@ assume a[0] != null;\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m4(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 2;\n"
                +"    a[0] = new Object();\n"
                +"    a[1] = new Object();\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m44(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 2;\n"
                +"    //@ assume a[0] != null;\n"
                +"    //@ assume a[1] != null;\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m4a(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 3;\n"
                +"    a[0] = new Object();\n"
                +"    a[1] = new Object();\n"
                +"    //@ assert \\nonnullelements(a);\n" // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m5(Object[] a) {\n"
                +"    //@ assume \\nonnullelements(a) && a.length == 3;\n"
                +"    a[0] = new Object();\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m5a(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 3;\n"
                +"    a[0] = null;\n"
                +"    //@ assert \\nonnullelements(a);\n" // BAD
                +"  }\n"
                
                 
                +"}"
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method m11a",9
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (Assert) in method m1a",9
                ,"/tt/TestJava.java:65: warning: The prover cannot establish an assertion (Assert) in method m4a",9
                ,"/tt/TestJava.java:77: warning: The prover cannot establish an assertion (Assert) in method m5a",9
                );
    }
    


    public void testNotModified() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires i == 5;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m1(int i) {\n"
                +"    i = 5;\n"
                +"    //@ assert \\not_modified(i);\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1a(int i) {\n"
                +"    i = 5;\n"
                +"    //@ assert \\not_modified(i);\n"  // BAD
                +"  }\n"
                
                +"  int i;\n"
                +"  static int si;\n"
                +"  //@ ghost int gi;\n"
                
                +"  //@ requires i == 5;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m2() {\n"
                +"    i = 5;\n"
                +"    //@ assert \\not_modified(i);\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m2a() {\n"
                +"    i = 5;\n"
                +"    //@ assert \\not_modified(i);\n"  // BAD
                +"  }\n"
                
                +"  //@ requires si == 5;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m3() {\n"
                +"    si = 5;\n"
                +"    //@ assert \\not_modified(si);\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m3a() {\n"
                +"    si = 5;\n"
                +"    //@ assert \\not_modified(si);\n"  // BAD
                +"  }\n"
                
                +"  //@ requires gi == 5;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m4() {\n"
                +"    //@ set gi = 5;\n"
                +"    //@ assert \\not_modified(gi);\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m4a() {\n"
                +"    //@ set gi = 5;\n"
                +"    //@ assert \\not_modified(gi);\n"  // BAD
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method m1a",9
                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Assert) in method m2a",9
                ,"/tt/TestJava.java:37: warning: The prover cannot establish an assertion (Assert) in method m3a",9
                ,"/tt/TestJava.java:48: warning: The prover cannot establish an assertion (Assert) in method m4a",9
                );
    }
    
    // Test well-definedness within the implicit old
    public void testNotModified2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  int i;\n"
                +"  static TestJava t;\n"
                
                +"  //@ requires t != null;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m1() {\n"
                +"    //@ assert \\not_modified(t.i);\n"  // OK
                +"  }\n"
                
                +"  //@ requires t != null;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m1a() {\n"
                +"    t = null;\n"
                +"    //@ assert \\not_modified(t.i) ? true: true;\n"  // BAD
                +"  }\n"
                
                +"  //@ requires t == null;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m1b() {\n"
                +"    t = new TestJava();\n"
                +"    //@ assert \\not_modified(t.i) ? true: true;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1c() {\n"
                +"    //@ assert \\not_modified(t.i) ? true: true;\n"  // BAD
                +"  }\n"
                
                 
                +"}"
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m1a",31
                ,"/tt/TestJava.java:20: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m1b",31
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m1c",31
                );
    }
    
    // TODO - test not_modified and old nested in each other; remember to test definedness            

    public void testFresh() {
//        print = true;
//        options.put("-showbb","");
//        options.put("-trace",   "");
//        options.put("-subexpressions",   "");
        helpTCX("tt.TestJava","package tt; \n"
                +"abstract public class TestJava { \n"
                
                +"  //@ requires p != null && p != this;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m1(Object p) {\n"
                +"    Object pp = c1(p);\n"
                +"    //@ assert pp != p;\n"  // OK
                +"    //@ assert pp != this;\n"  // OK
                +"  }\n"
                
                +"  //@ requires p != null && p != this;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m2(Object p) {\n"
                +"    Object pp = c2(p);\n"
                +"    //@ assert pp != p;\n"  // BAD
                +"  }\n"
                
                +"  //@ requires p != null && p != this;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m3(Object p) {\n"
                +"    Object pp = c2(p);\n"
                +"    //@ assert pp != this;\n"  // BAD
                +"  }\n"
                
                +"  //@ requires p != null && p != this;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m4(Object p) {\n"
                +"    Object pp = c1(p);\n"
                +"    Object q = new Object();\n"
                +"    //@ assert pp != q;\n"  // OK
                +"  }\n"
                
                +"  //@ requires p != null && p != this;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m5(Object p) {\n"
                +"    Object pp = c2(p);\n"
                +"    Object q = new Object();\n"
                +"    //@ assert pp != q;\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  //@ ensures \\result != null && \\fresh(\\result);\n"
                +"  //@ ensures \\result != p && \\result != this;\n"
                +"  public Object m6(Object p) {\n"
                +"    return new Object();\n"
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  //@ ensures \\result == null;\n"  // BAD
                +"  public Object m6a(Object p) {\n"
                +"    return new Object();\n"
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  //@ ensures \\result != null && \\fresh(\\result);\n"
                +"  //@ ensures \\result == p || \\result == this;\n" // BAD
                +"  public Object m6b(Object p) {\n"
                +"    return new Object();\n"
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  //@ ensures \\result != null && !\\fresh(\\result);\n" // BAD
                +"  public Object m6c(Object p) {\n"
                +"    return new Object();\n"
                +"  }\n"
                
                +"  Object o;\n"
                +"  //@ ghost Object oo;\n"
                +"  static Object so;\n"
                +"  //@ static ghost Object soo;\n"
                
                +"  //@ modifies \\nothing;\n"
                +"  public void m7(Object p) {\n"
                +"    Object pp = c1(p);\n"
                +"    //@ assert pp != o && pp != oo;\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\nothing;\n"
                +"  public void m7a(Object p) {\n"
                +"    Object pp = c2(p);\n"
                +"    //@ assert pp != o;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\nothing;\n"
                +"  public void m7b(Object p) {\n"
                +"    Object pp = c2(p);\n"
                +"    //@ assert pp != oo;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m7c(Object p) {\n"
                +"    Object pp = c1e(p);\n"
                +"    //@ assert pp != oo;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m7d(Object p) {\n"
                +"    Object pp = c1e(p);\n"
                +"    //@ assert pp != o;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\nothing;\n"
                +"  public void m8(Object p) {\n"
                +"    Object pp = c1(p);\n"
                +"    //@ assert pp != so && pp != soo;\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\nothing;\n"
                +"  public void m8a(Object p) {\n"
                +"    Object pp = c2(p);\n"
                +"    //@ assert pp != so;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\nothing;\n"
                +"  public void m8b(Object p) {\n"
                +"    Object pp = c2(p);\n"
                +"    //@ assert pp != soo;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m8c(Object p) {\n"
                +"    Object pp = c1e(p);\n"
                +"    //@ assert pp != soo;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m8d(Object p) {\n"
                +"    Object pp = c1e(p);\n"
                +"    //@ assert pp != so;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\nothing;\n"
                +"  public void m9a(Object p) {\n"
                +"    Object pp = c1n(p);\n"  // if pp is allowed to be null, then it might equal o or oo
                +"    //@ assert pp != o && pp != oo;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\nothing;\n"
                +"  public void m9b(Object p) {\n"
                +"    Object pp = c1n(p);\n"
                +"    //@ assert pp != so && pp != soo;\n"  // BAD
                +"  }\n"
                

                
                
                +"  //@ modifies \\nothing;\n"
                +"  //@ ensures \\fresh(\\result);\n"
                +"  abstract public Object c1(Object o); \n"
                
                +"  //@ modifies \\nothing;\n"
                +"  //@ ensures \\result == null || \\fresh(\\result);\n"
                +"  abstract public Object c1n(Object o); \n"
                
                +"  //@ modifies \\nothing;\n"
                +"  //@ ensures true;\n"
                +"  abstract public Object c2(Object o); \n"
                
                +"  //@ modifies \\everything;\n"
                +"  //@ ensures \\result != null && \\fresh(\\result);\n"
                +"  abstract public Object c1e(Object o); \n"
                
                +"  //@ modifies \\everything;\n"
                +"  //@ ensures true;\n"
                +"  abstract public Object c2e(Object o); \n"
                
                +"  public TestJava() {}\n"
                +"}"
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method m2",9
                ,"/tt/TestJava.java:20: warning: The prover cannot establish an assertion (Assert) in method m3",9
                ,"/tt/TestJava.java:45: warning: The prover cannot establish an assertion (Postcondition) in method m6a",5
                ,"/tt/TestJava.java:43: warning: Associated declaration",15
                ,"/tt/TestJava.java:51: warning: The prover cannot establish an assertion (Postcondition) in method m6b",5
                ,"/tt/TestJava.java:49: warning: Associated declaration",15
                ,"/tt/TestJava.java:56: warning: The prover cannot establish an assertion (Postcondition) in method m6c",5
                ,"/tt/TestJava.java:54: warning: Associated declaration",15
                ,"/tt/TestJava.java:70: warning: The prover cannot establish an assertion (Assert) in method m7a",9
                ,"/tt/TestJava.java:75: warning: The prover cannot establish an assertion (Assert) in method m7b",9
                ,"/tt/TestJava.java:80: warning: The prover cannot establish an assertion (Assert) in method m7c",9
                ,"/tt/TestJava.java:85: warning: The prover cannot establish an assertion (Assert) in method m7d",9
                ,"/tt/TestJava.java:95: warning: The prover cannot establish an assertion (Assert) in method m8a",9
                ,"/tt/TestJava.java:100: warning: The prover cannot establish an assertion (Assert) in method m8b",9
                ,"/tt/TestJava.java:105: warning: The prover cannot establish an assertion (Assert) in method m8c",9
                ,"/tt/TestJava.java:110: warning: The prover cannot establish an assertion (Assert) in method m8d",9
                ,"/tt/TestJava.java:115: warning: The prover cannot establish an assertion (Assert) in method m9a",9
                ,"/tt/TestJava.java:120: warning: The prover cannot establish an assertion (Assert) in method m9b",9
                );
    }
    
    public void testAssignables4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int k; static int sk;\n"
                +"  static TestJava p;\n"
                
                +"  //@ requires p != null && p != this;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m1() {\n"
                +"    //@ assume k == 0;\n"
                +"    c1(p);\n"
                +"    //@ assert k == 0;\n"
                +"  }\n"
                
                +"  //@ requires p != null && p != this;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m1a() {\n"
                +"    //@ assume sk == 0;\n"
                +"    c1(p);\n"
                +"    //@ assert sk == 0;\n"  // FAILS
                +"  }\n"
                
                +"  //@ requires p != null && p != this;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m2a() {\n"
                +"    //@ assume k == 0;\n"
                +"    c1(this);\n"
                +"    //@ assert k == 0;\n" // FAILS
                +"  }\n"
                
                +"  //@ requires p != null && p != this;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m2b() {\n"
                +"    //@ assume sk == 0;\n"
                +"    c1(this);\n"
                +"    //@ assert sk == 0;\n"  // FAILS
                +"  }\n"
                
                +"  //@ requires p != null && p != this;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m3() {\n"
                +"    //@ assume k == 0;\n"
                +"    c2(this);\n"
                +"    //@ assert k == 0;\n"
                +"  }\n"
                
                +"  //@ requires p != null && p != this;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m3a() {\n"
                +"    //@ assume sk == 0;\n"
                +"    c2(this);\n"
                +"    //@ assert sk == 0;\n"  // FAILS
                +"  }\n"
                

                
                +"  //@ requires o != null;\n"
                +"  //@ modifies o.*;\n"
                +"  public void c1(TestJava o) { } \n"
                
                +"  //@ requires o != null;\n"
                +"  //@ modifies TestJava.*;\n"
                +"  public void c2(TestJava o) { } \n"
                +"}"
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method m1a",9
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (Assert) in method m2a",9
                ,"/tt/TestJava.java:31: warning: The prover cannot establish an assertion (Assert) in method m2b",9
                ,"/tt/TestJava.java:45: warning: The prover cannot establish an assertion (Assert) in method m3a",9
                );
    }
    
    public void testAssignables1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int k; static int sk;\n"
                +"  int[] a; static int[] sa;\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1() {\n"
                +"    //@ assume k == 0;\n"
                +"    c1(1);\n"
                +"    //@ assert k == 0;\n"
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1a() {\n"
                +"    //@ assume k == 0;\n"
                +"    c1(0);\n"
                +"    //@ assert k == 0;\n" // FAILS
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m2() {\n"
                +"    //@ assume sk == 0;\n"
                +"    c1(1);\n"
                +"    //@ assert sk == 0;\n"
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m2a() {\n"
                +"    //@ assume sk == 0;\n"
                +"    c1(0);\n"
                +"    //@ assert sk == 0;\n" // FAILS
                +"  }\n"
                
                +"  //@ requires a != null && a.length > 10;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m3() {\n"
                +"    //@ assume a[0] == 0;\n"
                +"    c1(1);\n"
                +"    //@ assert a[0] == 0;\n"
                +"  }\n"
                
                +"  //@ requires a != null && a.length > 10;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m3a() {\n"
                +"    //@ assume a[0] == 0;\n"
                +"    c1(0);\n"
                +"    //@ assert a[0] == 0;\n" // FAILS
                +"  }\n"
                
                +"  //@ requires sa != null && sa.length > 10;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m4() {\n"
                +"    //@ assume sa[0] == 0;\n"
                +"    c1(1);\n"
                +"    //@ assert sa[0] == 0;\n"
                +"  }\n"
                
                +"  //@ requires sa != null && sa.length > 10;\n"  // Line 50
                +"  //@ modifies \\everything;\n"
                +"  public void m4a() {\n"
                +"    //@ assume sa[0] == 0;\n"
                +"    c1(0);\n"
                +"    //@ assert sa[0] == 0;\n" // FAILS
                +"  }\n"
                
                +"  //@ requires sa != null && sa.length > 10;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m5() {\n"
                +"    //@ assume a == \\old(a);\n"
                +"    c1(1);\n"
                +"    //@ assert a == \\old(a);\n"
                +"  }\n"
                
                +"  //@ requires sa != null && sa.length > 10;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m5a() {\n"
                +"    //@ assume a == \\old(a);\n"
                +"    c1(0);\n"
                +"    //@ assert a == \\old(a);\n" // FAILS
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m6(/*@ non_null*/TestJava t) {\n"
                +"    //@ assume t.k == 0;\n"
                +"    c1(1);\n"
                +"    //@ assert t.k == 0;\n"
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m6a(/*@ non_null*/TestJava t) {\n"
                +"    //@ assume t.k == 0;\n"
                +"    c1(0);\n"
                +"    //@ assert t.k == 0;\n" // FAILS
                +"  }\n"

                +"  //@ modifies \\everything;\n"
                +"  public void m7() {\n"
                +"    c1(1);\n"
                +"    //@ assert sk == \\old(sk);\n" // Should be OK - FIXME
                +"  }\n"

                +"  //@ modifies \\everything;\n"
                +"  public void m7a() {\n"
                +"    c1(0);\n"
                +"    //@ assert sk == \\old(sk);\n" // FAILS
                +"  }\n"

                
                +"  //@ requires i == 0;\n"
                +"  //@ modifies \\everything;\n"
                +"  //@ also requires i > 0;\n"
                +"  //@ modifies \\nothing;\n"
                +"  public void c1(int i) { } \n"
                +"}"
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method m1a",9
                ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (Assert) in method m2a",9
                ,"/tt/TestJava.java:41: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m3a",-17
                ,"/tt/TestJava.java:41: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m3a",-17
                ,"/tt/TestJava.java:55: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m4a",-18
                ,"/tt/TestJava.java:55: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m4a",-18
                ,"/tt/TestJava.java:55: warning: The prover cannot establish an assertion (Assert) in method m4a",-9
                ,"/tt/TestJava.java:69: warning: The prover cannot establish an assertion (Assert) in method m5a",9
                ,"/tt/TestJava.java:81: warning: The prover cannot establish an assertion (Assert) in method m6a",9
                ,"/tt/TestJava.java:86: warning: The prover cannot establish an assertion (Assert) in method m7",9
                ,"/tt/TestJava.java:91: warning: The prover cannot establish an assertion (Assert) in method m7a",9
                );
    }
    
    public void testAssignables2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int k;\n"
                +"  static int sk;\n"
                
                +"  //@ modifies k,sk;\n"
                +"  public void m1() {\n"
                +"    //@ assume k == 0 && sk == 0;\n"
                +"    c1(0);\n"
                +"    //@ assert sk == 0;\n"
                +"  }\n"
                
                +"  //@ modifies k,sk;\n"
                +"  public void m1a() {\n"
                +"    //@ assume k == 0 && sk == 0;\n"
                +"    c1(1);\n"
                +"    //@ assert sk == 0;\n" // FAILS
                +"  }\n"
                
                +"  //@ modifies k,sk;\n"
                +"  public void m2() {\n"
                +"    //@ assume k == 0 && sk == 0;\n"
                +"    c1(1);\n"
                +"    //@ assert k == 0;\n"
                +"  }\n"
                
                +"  //@ modifies k,sk;\n"
                +"  public void m2a() {\n"
                +"    //@ assume k == 0 && sk == 0;\n"
                +"    c1(0);\n"
                +"    //@ assert k == 0;\n" // FAILS
                +"  }\n"
                
                +"  //@ modifies k,sk;\n"
                +"  public void m3() {\n"
                +"    //@ assume k == 0 && sk == 0;\n"
                +"    c2(0,this);\n"
                +"    //@ assert k == 0;\n"
                +"  }\n"
                
                +"  //@ modifies k,sk;\n"
                +"  public void m3a() {\n"
                +"    //@ assume k == 0 && sk == 0;\n"
                +"    c2(10,this);\n"
                +"    //@ assert k == 0;\n" // FAILS
                +"  }\n"
                
                +"  static int[] a; int[] b;\n"
                +"  //@ requires a != null && a.length == 5;\n"
                +"  //@ modifies a[0];\n"
                +"  public void m4() {\n"
                +"    //@ assume a[0] == 0 && a[1] == 1;\n"
                +"    c3(0);\n"
                +"    //@ assert a[1] == 1;\n"
                +"  }\n"
                
                +"  //@ requires a != null && a.length == 5;\n"
                +"  //@ modifies a[0];\n"
                +"  public void m4a() {\n"
                +"    //@ assume a[0] == 0 && a[1] == 1;\n"
                +"    c3(0);\n"
                +"    //@ assert a[0] == 0;\n" // FAILS
                +"  }\n"
                
                +"  //@ requires b != null && b.length == 5;\n"
                +"  //@ modifies b[0];\n"
                +"  public void m5() {\n"
                +"    //@ assume b[0] == 0 && b[1] == 1;\n"
                +"    c4(0);\n"
                +"    //@ assert b[1] == 1;\n"
                +"  }\n"
                
                +"  //@ requires b != null && b.length == 5;\n"
                +"  //@ modifies b[0];\n"
                +"  public void m5a() {\n"
                +"    //@ assume b[0] == 0 && b[1] == 1;\n"
                +"    c4(0);\n"
                +"    //@ assert b[0] == 0;\n" // FAILS
                +"  }\n"
                
                +"  //@ requires b != null && b.length == 5;\n"
                +"  //@ modifies b[0];\n"
                +"  public void m6a() {\n"
                +"    //@ assume b[0] == 0 && b[1] == 1;\n"
                +"    c3(0);\n"  // changes a - get a null deference warning
                +"  }\n"
                
                +"  //@ requires a != null && b != null && b.length == 5  && a.length ==5;\n"
                +"  //@ modifies b[0];\n"
                +"  public void m6() {\n"
                +"    //@ assume b[0] == 0 && b[1] == 1;\n"
                +"    c3(0);\n"  // changes a - now ok
                +"    //@ assert b[1] == 1;\n"
                +"  }\n"
                
                +"  //@ requires i == 0;\n"
                +"  //@ modifies k;\n"
                +"  //@ also requires i > 0;\n"
                +"  //@ modifies sk;\n"
                +"  public void c1(int i) { } \n"
                
                +"  //@ requires i == 10;\n"
                +"  //@ modifies t.k;\n"
                +"  //@ also requires i == 0;\n"
                +"  //@ modifies \\nothing;\n"
                +"  public void c2(int i, TestJava t) {}\n"
                
                +"  //@ requires a!=null && 0<=i && i<a.length;\n"
                +"  //@ modifies a[i];\n"
                +"  public void c3(int i) {}\n"
                +"  //@ requires b!=null && 0<=i && i<b.length;\n"
                +"  //@ modifies b[i];\n"
                +"  public void c4(int i) {}\n"
                +"}"
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method m1a",9
                ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (Assert) in method m2a",9
                ,"/tt/TestJava.java:39: warning: The prover cannot establish an assertion (Assert) in method m3a",9
                ,"/tt/TestJava.java:54: warning: The prover cannot establish an assertion (Assert) in method m4a",9
                ,"/tt/TestJava.java:68: warning: The prover cannot establish an assertion (Assert) in method m5a",9
                ,"/tt/TestJava.java:74: warning: The prover cannot establish an assertion (Precondition) in method m6a",7
                ,"/tt/TestJava.java:93: warning: Associated declaration",16
                );
    }
    
    public void testAssignables3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static int[] a;  //@ invariant a != null && a.length == 10;\n"
                
                +"  public TestJava() {\n"
                +"     a = new int[10];\n"
                +"  }\n"
                
                +"  //@ modifies a[*];\n"
                +"  public void m1() {\n"
                +"    //@ assume a[0] == 0 && a[2] == 2;\n"
                +"    c1();\n"
                +"    //@ assert a[0] == 0;\n"
                +"  }\n"
                
                +"  //@ modifies a[*];\n"
                +"  public void m1a() {\n"
                +"    //@ assume a[0] == 0 && a[2] == 2;\n"
                +"    c1();\n"
                +"    //@ assert a[2] == 3;\n"  // FAILS
                +"  }\n"
                
                +"  //@ modifies a[*];\n"
                +"  public void m2a() {\n"
                +"    //@ assume a[0] == 0 && a[2] == 2;\n"
                +"    c2();\n"
                +"    //@ assert a[0] == 0;\n" // FAILS
                +"  }\n"
                
                +"  //@ modifies a[*];\n"
                +"  public void m2b() {\n"
                +"    //@ assume a[0] == 0 && a[2] == 2;\n"
                +"    c2();\n"
                +"    //@ assert a[2] == 2;\n"  // FAILS
                +"  }\n"
                
                +"  //@ modifies a[*];\n"
                +"  public void m3() {\n"
                +"    //@ assume a[0] == 0 && a[2] == 2;\n"
                +"    c3();\n"
                +"    //@ assert a[0] == 0;\n" 
                +"  }\n"
                
                +"  //@ modifies a[*];\n"
                +"  public void m3a() {\n"
                +"    //@ assume a[0] == 0 && a[9] == 2;\n"
                +"    c3();\n"
                +"    //@ assert a[9] == 2;\n"  // FAILS
                +"  }\n"
                
                
                +"  //@ modifies a[2 .. 4];\n"
                +"  public void c1() { } \n"
                
                +"  //@ modifies a[*];\n"
                +"  public void c2() {}\n"
                
                +"  //@ modifies a[2 .. ];\n"
                +"  public void c3() {}\n"
                +"}"
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method m1a",9
                ,"/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Assert) in method m2a",9
                ,"/tt/TestJava.java:29: warning: The prover cannot establish an assertion (Assert) in method m2b",9
                ,"/tt/TestJava.java:41: warning: The prover cannot establish an assertion (Assert) in method m3a",9
                );
    }
    
    public void testMethodCallsWithExceptions() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static int k;\n"
                +"  //@ requires i >= 0;\n"
                +"  //@ modifies k;\n"
                +"  //@ ensures k == 10;\n"
                +"  //@ signals (Exception e) k<0;\n"
                +"  public void m1(int i) {\n"
                +"    m(i);\n"
                +"    k = 10;\n"
                +"  }\n"
                +"  //@ requires i >= 0;\n"
                +"  //@ modifies k;\n"
                +"  //@ ensures k == 10;\n"
                +"  //@ signals (Exception e) k==-11;\n"
                +"  public void m2(int i) {\n"
                +"    m(1);\n"
                +"    m(2);\n"
                +"    k = 10;\n"
                +"  }\n"

                +"  //@ requires i >= 0;\n"
                +"  //@ modifies k;\n"
                +"  //@ ensures k == 10;\n"
                +"  //@ signals (Exception e) k==-12;\n"
                +"  public void m3(int i) {\n"
                +"    m(0);\n"
                +"    m(2);\n"
                +"    k = 10;\n"
                +"  }\n"
                
                +"  //@ requires i >= 0;\n"
                +"  //@ modifies k;\n"
                +"  //@ ensures k == 10;\n"
                +"  //@ signals (Exception e) k==-13;\n" // FAILS
                +"  public void m3a(int i) {\n"
                +"    m(0);\n"
                +"    m(2);\n"
                +"    k = 10;\n"
                +"  }\n"
                
                +"  //@ requires i >= 0;\n"
                +"  //@ modifies k;\n"
                +"  //@ ensures \\result == 12;\n"
                +"  //@ signals (Exception e) false;\n"
                +"  public int m4(int i) {\n"
                +"    return 10+m(0)+m(0);\n"
                +"  }\n"
                
                +"  //@ requires i >= 0;\n"
                +"  //@ modifies k;\n"
                +"  //@ ensures false;\n"
                +"  //@ signals (Exception e) k == -11;\n"
                +"  public int m5(int i) {\n"
                +"    return 10+m(1)+m(0);\n"
                +"  }\n"
                
                +"  //@ requires i >= 0;\n"
                +"  //@ modifies k;\n"
                +"  //@ ensures false;\n"
                +"  //@ signals (Exception e) k == -12;\n"
                +"  public int m6(int i) {\n"
                +"    return 10+m(0)+m(2);\n"
                +"  }\n"
                
                +"  //@ requires i == 0;\n"
                +"  //@ modifies k;\n"
                +"  //@ ensures k>0 && \\result == i+1;\n"
                +"  //@ signals (Exception e) false;\n"
                +"  //@ also \n"
                +"  //@ requires i > 0;\n"
                +"  //@ modifies k;\n"
                +"  //@ ensures false;\n"
                +"  //@ signals (Exception e) k == -10-i;\n"
                +"  //@ signals_only Exception;\n"
                +"  public int m(int i) {\n"
                +"    if (i > 0) {\n"
                +"      k = -10-i;\n"
                +"      throw new RuntimeException();\n"
                +"    }\n"
                +"    k = 1;\n"
                +"    return i+1;\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m3a",6
                ,"/tt/TestJava.java:33: warning: Associated declaration",7
                );
    }
    
    public void testStrings() { // FIXME - hangs up when we try to check assumptions
        String v = Options.instance(context).get("-noCheckAssumptions");
        Options.instance(context).put("-noCheckAssumptions","");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  String s;\n"
                +"  String ss = \"abcde\";\n"
                +"  public boolean m(String sss) {\n"
                +"    return sss == (\"abcde\");\n"
                +"  }\n"
                +"  public boolean m1(/*@ non_null*/ String sss) {\n"
                +"    return sss.equals(\"abcde\");\n"
                +"  }\n"
                +"}"
                );
        Options.instance(context).put("-noCheckAssumptions",v);
    }

    public void testRequires() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  TestJava() { b = true; }\n"
                +"  public TestJava(int i) {}\n"  // fails
                +"  //@ requires false;\n"
                +"  public static boolean bf(boolean bb) { return true; }\n"
                +"  //@ requires true;\n"
                +"  public static boolean bt(boolean bb) { return true; }\n"
                +"  static boolean b;\n"
                +"  //@ static invariant b;\n"
                +"  //@ requires !b;\n"
                +"  public static boolean bq(boolean bb) { return true; }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Invariant) in method <init>",10,
                "/tt/TestJava.java:10: warning: Associated declaration",24,
                "/tt/TestJava.java:6: warning: Invariants+Preconditions appear to be contradictory in method bf(boolean)",25,
                "/tt/TestJava.java:12: warning: Invariants+Preconditions appear to be contradictory in method bq(boolean)",25);
    }

    public void testJava() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static boolean bstatic;\n"
                +"  boolean binstance;\n"
                +"  boolean binstance2;\n"
                +"  /*@ non_null */ Object o;\n"
                +"  //@ ghost Object oo;\n"
                +"  //@static invariant bstatic;\n"
                +"  //@invariant binstance;\n"
                +"  //@initially binstance2;\n"
                +"  //@constraint binstance2 == \\old(binstance2);\n"
                +"  //@static constraint bstatic == \\old(bstatic);\n"
                
                +"  public static void main(/*@ non_null*/ String[] args) {  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result;\n"
                +"  public static boolean b(boolean bb) { return true; }\n"
                
                +"  //@ requires false;\n"
                +"  //@ ensures true;\n"
                +"  public static int i(int ii) { return 0; }\n"
                
                +"  //@ requires ii == 10;\n"
                +"  //@ ensures true;\n"
                +"  public Object inst(int ii) { binstance = ii == 0; o = null; /*@ set oo = null;*/ return null; }\n"
                
                +"  //@ requires ii == 10;\n"
                +"  //@ ensures true;\n"
                +"  public Object insx(int ii) { binstance = ii == 0;           /*@ set oo = null;*/ return null; }\n"
                +"}",
                "/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Invariant) in method <init>",8, // nothing sets bstatic true
                "/tt/TestJava.java:8: warning: Associated declaration",23,
                //"/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Invariant) in method <init>",8, // nothings sets binstance true
                //"/tt/TestJava.java:9: warning: Associated declaration",16,
                //"/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Initially) in method <init>",8, // nothing sets binstance2 true
                //"/tt/TestJava.java:10: warning: Associated declaration",16,
                "/tt/TestJava.java:19: warning: Invariants+Preconditions appear to be contradictory in method i(int)",21, // precondition is false
                "/tt/TestJava.java:22: warning: The prover cannot establish an assertion (PossiblyNullReference) in method inst",55,  // FIXME - incorrect error
                "/tt/TestJava.java:25: warning: The prover cannot establish an assertion (Invariant) in method insx",84, // binstance is false
                "/tt/TestJava.java:9: warning: Associated declaration",16
        );
    }

    public void testAssert() {
//        options.put("-showbb","");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert(boolean bb, boolean b) { /*@ assume b; */ /*@assert false;*/   }\n" // Should fail because of the explicit assert false
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert2(boolean bb, boolean b) { /*@ assume b; */ /*@assert !bb;*/   }\n" // Should fail because of the tautologically false assert
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert3(boolean bb, boolean b) { /*@ assume bb; */ /*@assert b;*/   }\n" // Should fail because of the unprovable assert
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method bassert",75,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method bassert2",76,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method bassert3",77
        );
    }

    public void testAssume() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassumeBADASSUMP(boolean bb) { /*@assume false;*/  /*@ assert false; */ }\n" // Should succeed despite the false assert
                +"  //@ requires bbb;\n"
                +"  public static void bifOK(boolean bb,boolean b, boolean bbb) { /*@assume true;*/ if (bb) { /*@assume !b;*/ /*@ assert !bb; */ }  }\n"
                +"  //@ requires b;\n"
                +"  public static void bifBAD(boolean bb,boolean b) { /*@assume true;*/ if (bb) { /*@assume !b;*/ /*@ assert !bb; */ }  }\n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassumeBADASSUMP2(boolean bb) { /*@assume false;*/  /*@ assert true; */ }\n" // Should succeed despite the false assert
                +"  public static void bassumeCHAIN1(boolean bb, boolean b) { if (bb) { /*@ assume !bb; assume bb;*/ b = true;  /* @ assert false; */ } }\n" 
                +"  public static void bassumeCHAIN2(boolean bb, boolean b) { if (bb) { /*@assume bb; assume !bb; */ b = true; /* @ assert false; */ } }\n" 
                +"  public static void bassumeMULT(boolean bb, boolean b) { if (bb) { /*@assume bb; assume !bb; */ b = true; /* @ assert false; */ } else { /*@assume bb; assume !bb; */ b = true; /* @ assert false; */} }\n" 
                +"  public TestJava() {}\n"
                +"}",
                "/tt/TestJava.java:5: warning: An assumption appears to be infeasible in method bassumeBADASSUMP(boolean)",56,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method bifOK",113,
                "/tt/TestJava.java:9: warning: An assumption appears to be infeasible in method bifBAD(boolean,boolean)",84,
                "/tt/TestJava.java:12: warning: An assumption appears to be infeasible in method bassumeBADASSUMP2(boolean)",57,
                        // The following error is required, but can occur before or after the error on the same line
                "/tt/TestJava.java:13: warning: An assumption appears to be infeasible in method bassumeCHAIN1(boolean,boolean)",-87,
                "/tt/TestJava.java:13: warning: An assumption appears to be infeasible in method bassumeCHAIN1(boolean,boolean)",75,
                "/tt/TestJava.java:13: warning: An assumption appears to be infeasible in method bassumeCHAIN1(boolean,boolean)",-87,
                "/tt/TestJava.java:14: warning: An assumption appears to be infeasible in method bassumeCHAIN2(boolean,boolean)",85,
                // The following error is required, but can occur before or after the error on the same line
                "/tt/TestJava.java:15: warning: An assumption appears to be infeasible in method bassumeMULT(boolean,boolean)",83,
                "/tt/TestJava.java:15: warning: An assumption appears to be infeasible in method bassumeMULT(boolean,boolean)",142,
                "/tt/TestJava.java:15: warning: An assumption appears to be infeasible in method bassumeMULT(boolean,boolean)",153
        );
    }

    public void testDeadBranch() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //static int ii;\n"
                +"  public static void bok(boolean b, int i) { if (b) i = 7; else i = 9; }\n" 
                +"  public static void bok2(boolean b, int i, int ii) { if (b) i = 7; else i = 9; if (b) ii = 7; else ii = 9; }\n" 
                +"  public static void bdead(boolean b, int i) { /*@ assume b; */ if (b) i = 7; else i = 9; }\n" 
                +"  public static void bdeadelse(boolean b, int i) { /*@ assume !b; */ if (b) i = 7; else i = 9; }\n" 
                +"}",
                "/tt/TestJava.java:6: warning: else branch apparently never taken in method bdead(boolean,int)", 69,
                "/tt/TestJava.java:7: warning: then branch apparently never taken in method bdeadelse(boolean,int)", 73
        );
    }

    public void testDecl() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void bok() { int k = 0; /*@ assert k == 0; */ }\n" 
                +"  public static void bfalse() { int k = 0; /*@ assert k != 0; */ }\n" 
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method bfalse",48
        );
    }

    public void testIncarnations() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void bnotok() { int k = 10; int i = 0; i = 1; i = k; k = 5; k = i+k; /*@ assert i == 10; assert k == 16; */}\n" // We want to be sure it fails
                +"  public static void bifok(boolean b) { int k = 10; if (b) { k = k+1; if (b) k = k-1; else k = k+1; } else { k=k-1; if (b) k=k-1; else k=k+1; } /*@ assert k == 10; */}\n"
                +"  public static void bifbad(boolean b) { int k = 10; if (b) { k = k+1; if (b) k = k-1; else k = k+1; } else { k=k-1; if (b) k=k-1; else k=k+1; } /*@ assert k == 11; */}\n" // We want to be sure it fails
                +"  public static void bifbad2(boolean b) { int k = 10; if (b) { k = k+1; if (!b) k = k+1; } else { k=k-1; if (b) {k=k-1; b = false; } } /*@ assert k == 11; */}\n" // We want to be sure it fails
                +"}",
                "/tt/TestJava.java:3: warning: The prover cannot establish an assertion (Assert) in method bnotok",106,
                    // The following error is required, but the order is arbitrary
                "/tt/TestJava.java:4: warning: else branch apparently never taken in method bifok(boolean)", -75,
                "/tt/TestJava.java:4: warning: then branch apparently never taken in method bifok(boolean)", 120,
                "/tt/TestJava.java:4: warning: else branch apparently never taken in method bifok(boolean)", -75,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method bifbad",150,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method bifbad2",140
        );
    }

    public void testOld() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                +"  //@ static constraint i > \\old(i);\n"
                +"  //@ modifies i;\n"
                +"  //@ ensures true;\n"
                +"  public static void bok() { i = i - 1; }\n"
                +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Constraint) in method bok",22,
                "/tt/TestJava.java:4: warning: Associated declaration", 25
        );
    }

    public void testOld2() {
//        options.put("-showbb","");
//        options.put("-trace","");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                +"  //@ modifies i;\n"
                +"  //@ ensures i == \\old(i)+2;\n"
                +"  public static void bok() { i = i + 1; i = i + 1;}\n"
                +"  //@ modifies i;\n"
                +"  //@ ensures i == \\old(i+1);\n"
                +"  public static void bbad() { i = i - 1; }\n"
                +"}",
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method bbad",22,
                "/tt/TestJava.java:8: warning: Associated declaration", 15
        );
    }

    public void testReturn() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires 0<=ii && ii <=3;\n"
                +"  //@ ensures ii<=0 ==> \\result ==-ii;\n"
                +"  public static int bok(int ii) { if (ii==1) return -1; else if (ii==2) return -2; else if (ii==3) return -3; return 0; }\n"
                +"  //@ ensures \\result == -ii;\n"
                +"  public static int bbad(int ii) { if (ii==1) return -1; else if (ii==2) return -2; else if (ii==3) return -3; return 0; }\n"
                +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method bbad",112,
                "/tt/TestJava.java:6: warning: Associated declaration",15
        );
    }

    public void testThrow() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void bok(int i) { if (i == 0) throw new RuntimeException(); /*@ assert i!=0; */ }\n"
                +"  public static void bbad(int i) { if (i == 0) throw new RuntimeException(); /*@ assert i==0; */ }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method bbad",82
        );
    }

    public void testNonNull() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  //@ requires ii == 10;\n"
                +"  //@ ensures true;\n"
                +"  public /*@ non_null */Object inst(int ii) { return null; }\n"
                +"  //@ requires ii == 10;\n"
                +"  //@ ensures true;\n"
                +"  public @NonNull Object inst2(int ii) {  return null; }\n"
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method inst",47,
                "/tt/TestJava.java:5: warning: Associated declaration",14,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method inst2",43,
                "/tt/TestJava.java:8: warning: Associated declaration",10
        );
    }

    public void testNonNull2() {
        options.put("-nullableByDefault",null);
        options.put("-nonnullByDefault","");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  //@ requires ii == 10;\n"
                +"  //@ ensures true;\n"
                +"  public                Object inst(int ii) { return null; }\n"
                +"  //@ requires ii == 10;\n"
                +"  //@ ensures true;\n"
                +"  public          Object inst2(int ii) {  return null; }\n"
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method inst",47,
                "/tt/TestJava.java:5: warning: Associated declaration",32,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method inst2",43,
                "/tt/TestJava.java:8: warning: Associated declaration",26
        );
    }

    public void testNonNull3() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                +"  //@ requires ii == 10;\n"
                +"  //@ ensures true;\n"
                +"  public                Object inst(int ii) { return null; }\n"
                +"  //@ requires ii == 10;\n"
                +"  //@ ensures true;\n"
                +"  public          Object inst2(int ii) {  return null; }\n"
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method inst",47,
                "/tt/TestJava.java:5: warning: Associated declaration",32,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method inst2",43,
                "/tt/TestJava.java:8: warning: Associated declaration",26
        );
    }
    
    // FIXME - the non-null return postcondition error message is not very clear (it is actually assigning null to a nonnull return value)

    public void testNonNull4() {
        options.put("-nullableByDefault",null);
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  //@ requires ii == 10;\n"
                +"  //@ ensures true;\n"
                +"  public                Object inst(int ii) { return null; }\n"
                +"  //@ requires ii == 10;\n"
                +"  //@ ensures true;\n"
                +"  public          Object inst2(int ii) {  return null; }\n"
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method inst",47,
                "/tt/TestJava.java:5: warning: Associated declaration",32,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method inst2",43,
                "/tt/TestJava.java:8: warning: Associated declaration",26
        );
    }

    public void testNonNullParam() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  //@ ensures \\result != null;\n"
                +"  public Object inst(boolean b, /*@ non_null */Object i, Object ii) { return i; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public Object instbad(boolean b, /*@ non_null */Object i, Object ii) { return ii; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public Object inst2(boolean b, @NonNull Object i, Object ii) { return i; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public Object inst2bad(boolean b, @NonNull Object i, Object ii) { return ii; }\n"
                +"}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method instbad",74,
                "/tt/TestJava.java:5: warning: Associated declaration",15,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method inst2bad", 69,
                "/tt/TestJava.java:9: warning: Associated declaration",15
        );
    }

    public void testNonNullParam2() {
        options.put("-nullableByDefault",null);
        options.put("-nonnullByDefault","");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  //@ ensures \\result != null;\n"
                +"  public /*@ nullable*/Object inst(boolean b,                Object i, /*@ nullable*/Object ii) { return i; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public /*@ nullable*/Object instbad(boolean b,                Object i, /*@ nullable*/Object ii) { return ii; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public /*@ nullable*/Object inst2(boolean b,          Object i, /*@ nullable*/Object ii) { return i; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public /*@ nullable*/Object inst2bad(boolean b,          Object i, /*@ nullable*/Object ii) { return ii; }\n"
                +"}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method instbad",102,
                "/tt/TestJava.java:5: warning: Associated declaration",15,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method inst2bad", 97,
                "/tt/TestJava.java:9: warning: Associated declaration",15
        );
    }

    public void testNonNullParam3() {
        options.put("-nullableByDefault",null);
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                +"  //@ ensures \\result != null;\n"
                +"  public /*@ nullable*/Object inst(boolean b,                Object i, /*@ nullable*/Object ii) { return i; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public /*@ nullable*/Object instbad(boolean b,                Object i, /*@ nullable*/Object ii) { return ii; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public /*@ nullable*/Object inst2(boolean b,          Object i, /*@ nullable*/Object ii) { return i; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public /*@ nullable*/Object inst2bad(boolean b,          Object i, /*@ nullable*/Object ii) { return ii; }\n"
                +"}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method instbad",102,
                "/tt/TestJava.java:5: warning: Associated declaration",15,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method inst2bad", 97,
                "/tt/TestJava.java:9: warning: Associated declaration",15
        );
    }

    public void testNonNullParam4() {
        options.put("-nullableByDefault",null);
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  //@ ensures \\result != null;\n"
                +"  public /*@ nullable*/Object inst(boolean b,                Object i, /*@ nullable*/Object ii) { return i; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public /*@ nullable*/Object instbad(boolean b,                Object i, /*@ nullable*/Object ii) { return ii; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public /*@ nullable*/Object inst2(boolean b,          Object i, /*@ nullable*/Object ii) { return i; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public /*@ nullable*/Object inst2bad(boolean b,          Object i, /*@ nullable*/Object ii) { return ii; }\n"
                +"}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method instbad",102,
                "/tt/TestJava.java:5: warning: Associated declaration",15,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method inst2bad", 97,
                "/tt/TestJava.java:9: warning: Associated declaration",15
        );
    }

    public void testMethodCall() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  static public int j;\n"
                +"  //@ requires i>0;\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures j == -i;\n"
                +"  static public void m(int i) { j = -i; }\n"
                +"  //@ requires i>1; \n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == -i;\n"
                +"  public int inst(boolean b, int i) { m(i); return j; }\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == j;\n"
                +"  public int instbad(boolean b, int i) { m(i); return j; }\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == i;\n"
                +"  public int instbad2(boolean b, int i) { m(1); return j; }\n"
                +"}",
                //"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Postcondition) in method instbad",14,
                //"/tt/TestJava.java:13: warning: Associated declaration",15,
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Precondition) in method instbad",43,
                "/tt/TestJava.java:4: warning: Associated declaration",16,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Postcondition) in method instbad2",49,
                "/tt/TestJava.java:16: warning: Associated declaration",15
        );
    }

    public void testMethodCall2() { // Had problems with static and non-static
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public int j;\n"
                +"  //@ requires i>0;\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures j == -i;\n"
                +"  public void m(int i) { j = -i; }\n"
                +"  //@ requires i>1; \n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == -i;\n"
                +"  public int inst(boolean b, int i) { m(i); return j; }\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == j;\n"
                +"  public int instbad(boolean b, int i) { m(i); return j; }\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == i;\n"
                +"  public int instbad2(boolean b, int i) { m(1); return j; }\n"
                +"}",
                //"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Postcondition) in method instbad",14,
                //"/tt/TestJava.java:13: warning: Associated declaration",15,
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Precondition) in method instbad",43,
                "/tt/TestJava.java:4: warning: Associated declaration",16,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Postcondition) in method instbad2",49,
                "/tt/TestJava.java:16: warning: Associated declaration",15
        );
    }

    public void testMethodCallRet() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  static public int j;\n"
                +"  //@ requires i>0;\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures j == i+1 && \\result == j;\n"
                +"  static public int m(int i) { j = i+1; return j; }\n"
                +"  //@ requires i>1; \n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == \\old(i)+1;\n"
                +"  public int inst(boolean b, int i) { m(i); m(i); m(i); return j; }\n"
                +"  //@ requires i>1; \n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == \\old(i)+3;\n"
                +"  public int inst2(boolean b, int i) { m(m(m(i))); return j; }\n"
                +"}"
        );
    }

    public void testMethodCallThis() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  static TestJava o;\n"
                +"  static TestJava p;\n"
                +"  public int j; static public int sj; \n"
                
                +"  //@ ensures \\result == j;\n"
                +"  public int m() { return j; }\n"
                
                +"  //@ modifies j,sj;\n"
                +"  //@ ensures \\result == \\old(j);\n"
                +"  public int nold() { return j; }\n"
                
                +"  //@ modifies j,sj;\n"
                +"  //@ ensures \\result == j;\n"
                +"  public int n() { return j; }\n"
                
                +"  //@ modifies j,sj;\n"
                +"  //@ ensures \\result == sj;\n"
                +"  public int sn() { return sj; }\n"
                
                +"  //@ requires o!=null && p != null && o.j == 1 && p.j == 2 && j == 3;\n"
                +"  //@ modifies j,sj,o.j,o.sj,p.j,p.sj;\n"
                +"  //@ ensures \\result == 6;\n"
                +"  public int inst() { return o.m() + p.m() + j; }\n"
                
                +"  //@ requires o!=null && p != null && o.j == 1 && p.j == 2 && j == 3;\n"
                +"  //@ modifies j,sj,o.j,o.sj,p.j,p.sj;\n"
                +"  //@ ensures \\result == 6;\n"
                +"  public int instok() { return o.nold() + p.nold() + j; }\n" // o.n and p.n modify o.j and p.j, returned value is before mod
                
                +"  //@ requires o!=null && p != null && o.j == 1 && p.j == 2 && j == 3;\n"
                +"  //@ modifies j,sj,o.j,o.sj,p.j,p.sj;\n"
                +"  //@ ensures \\result == 6;\n"
                +"  public int instbadx() { return o.n() + p.n() + j; }\n" // returned value is after modification
                
                +"  //@ modifies j,sj;\n"
                +"  //@ ensures \\result == 6;\n"
                +"  public int instbad() { return n() + j; }\n"  // n() modifies this.j
                
                +"  //@ requires o!=null && p != null && sj == 3;\n"
                +"  //@ modifies j,sj,o.j,o.sj,p.j,p.sj;\n"
                +"  //@ ensures \\result == 9;\n"
                +"  public int instbad2() { return o.sn() + p.sn() + sj; }\n"
                +"}"
                ,"/tt/TestJava.java:28: warning: The prover cannot establish an assertion (Postcondition) in method instbadx",27
                ,"/tt/TestJava.java:27: warning: Associated declaration",15
                ,"/tt/TestJava.java:31: warning: The prover cannot establish an assertion (Postcondition) in method instbad",26
                ,"/tt/TestJava.java:30: warning: Associated declaration",15
                ,"/tt/TestJava.java:35: warning: The prover cannot establish an assertion (Postcondition) in method instbad2",27
                ,"/tt/TestJava.java:34: warning: Associated declaration",15
        );
    }

    // TODO  need tests for for loops
    // TODO need tests for do loops

    // TODO - more tests needed, and with specs
    // FIXME (test disabled) - need a loop invariant to prove this
    public void _testForeachSpecs() { 
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst(int[] a) { \n"
                +"    //@ assume a.length > 2 && a[0] == 1;\n"
                +"    for(int i: a) a[i] = 0; \n"
                +"    //@ assert a[1] == 0;\n"
                +"  }\n"
                +"}"
        );
    }

    public void testForLoopSpecs() {  // FIXME - want error position at the end of the statement that is the loop body
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst() { int n = 0; /*@ loop_invariant 0<=i && i<=5 && n==i; decreases 5-i; */ for (int i=0; i<5; i++) n++; /*@ assert n == 5; */ }\n"
                +"  public void instb() { int n = 0; /*@ loop_invariant 0<=i && i<=5 && n==i; decreases 3-i; */ for (int i=0; i<5; i++) n++; /*@ assert n == 5; */ }\n"
                +"  public void instc() { int n = 0; /*@ loop_invariant 0<=i && i<5 && n==i; decreases 5-i; */ for (int i=0; i<5; i++) n++; /*@ assert n == 5; */ }\n"
                +"  public void instd() { int n = 0; /*@ loop_invariant 0<=i && i<=5 && n==i-1; decreases 5-i; */ for (int i=0; i<5; i++) n++;  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreasesNotPositive) in method instb",119
                ,"/tt/TestJava.java:4: warning: Associated declaration",77
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (LoopInvariant) in method instc",118
                ,"/tt/TestJava.java:5: warning: Associated declaration",40
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (LoopInvariantBeforeLoop) in method instd",97
                ,"/tt/TestJava.java:6: warning: Associated declaration",40
//                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (LoopInvariant) in method instd",122
//                "/tt/TestJava.java:6: warning: Associated declaration",40
        );
    }

    public void _testDoWhileSpecs() { // FIXME - figure out this better  // FIXME - want error position at the right place  // Note test is disabled
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst() { int i = 5; /*@ loop_invariant i>0; decreases i; */ do { i = i-1; } while (i>0); /*@ assert i == 0; */ }\n"
                +"  public void instb() { int i = 5; /*@ loop_invariant i>=0; decreases i-2; */ do  i = i+1;  while (i>0); /*@ assert i == 0; */ }\n"
                +"  public void instc() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ do { i = i+1; } while (i>0); /*@ assert i == 0; */ }\n"
                +"  public void instd() { int i = 5; /*@ loop_invariant i>0; decreases i; */ do { i = i-1; } while (i>0); /*@ assert i == 0; */ }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopInvariant) in method instb",91, // This presumably an effect of the 
                "/tt/TestJava.java:4: warning: Associated declaration",40,
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreasesNotPositive) in method instb",91,
                "/tt/TestJava.java:4: warning: Associated declaration",61,
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method instb",108,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (LoopDecreases) in method instc",89,
                "/tt/TestJava.java:5: warning: Associated declaration",61,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method instc",106,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (LoopInvariant) in method instd",88,
                "/tt/TestJava.java:6: warning: Associated declaration",40,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method instd",105
        );
    }

    public void testWhileSpecs() { 
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                +"  public void instb() { int i = 5; /*@ loop_invariant i>=0; decreases i-2; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                +"  public void instc() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ while (i>0) { i = i+1; } /*@ assert i == 0; */ }\n"
                +"  public void instd() { int i = 5; /*@ loop_invariant i>0; decreases i; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreasesNotPositive) in method instb",91,
                "/tt/TestJava.java:4: warning: Associated declaration",61,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (LoopDecreases) in method instc",100,
                "/tt/TestJava.java:5: warning: Associated declaration",61,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (LoopInvariant) in method instd",99,
                "/tt/TestJava.java:6: warning: Associated declaration",40
        );
    }

    // FIXME - need to sort out loop invariants for while loops with side effects
    //    public void testWhileSpecs2() {
    //        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
    //                +"public class TestJava { \n"
    //                +"  public void inst() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ while (--i > 0) { } /*@ assert i == 0; */ }\n"
    //                +"  public void instb() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ while (i-- >0) { } /*@ assert i == 0; */ }\n"
    //                              +"}",
    //                 "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreasesNotPositive) in method instb",91,
    //                 "/tt/TestJava.java:4: warning: Associated declaration",71,
    //                 "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method instb", 108
    //                );
    //    }

    public void testIncDec() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1() { int i = 5; i++; /*@ assert i == 6; */ }\n"
                +"  public void inst1b() { int i = 5; i++; /*@ assert i == 5; */ }\n"
                +"  public void inst2() { int i = 5; i--; /*@ assert i == 4; */ }\n"
                +"  public void inst2b() { int i = 5; i--; /*@ assert i == 5; */ }\n"
                +"  public void inst3() { int i = 5; ++i; /*@ assert i == 6; */ }\n"
                +"  public void inst3b() { int i = 5; ++i; /*@ assert i == 5; */ }\n"
                +"  public void inst4() { int i = 5; --i; /*@ assert i == 4; */ }\n"
                +"  public void inst4b() { int i = 5; --i; /*@ assert i == 5; */ }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1b",46,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst2b",46,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst3b",46,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst4b",46
        );
    }

    public void testIncDec2() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1() { int i = 5; int j = i++; /*@ assert j == 5; */ }\n"
                +"  public void inst1b() { int i = 5; int j = i++; /*@ assert j == 6; */ }\n"
                +"  public void inst2() { int i = 5; int j = i--; /*@ assert j == 5; */ }\n"
                +"  public void inst2b() { int i = 5; int j = i--; /*@ assert j == 4; */ }\n"
                +"  public void inst3() { int i = 5; int j = ++i; /*@ assert j == 6; */ }\n"
                +"  public void inst3b() { int i = 5; int j = ++i; /*@ assert j == 5; */ }\n"
                +"  public void inst4() { int i = 5; int j = --i; /*@ assert j == 4; */ }\n"
                +"  public void inst4b() { int i = 5; int j = --i; /*@ assert j == 5; */ }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1b",54,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst2b",54,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst3b",54,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst4b",54
        );
    }

    public void testAssignOp() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1() { int i = 5; i+=7; /*@ assert i == 12; */ }\n"
                +"  public void inst1b() { int i = 5; i+=7; /*@ assert i == 5; */ }\n"
                +"  public void inst1c() { int i = 5; int j = (i+=7); /*@ assert i == 12 && i == j; */ }\n"
                +"  public void inst1d() { int i = 5; int j = (i+=7); /*@ assert i == 5; */ }\n"
                +"  public void inst2() { int i = 5; i-=7; /*@ assert i == -2; */ }\n"
                +"  public void inst2b() { int i = 5; i-=7; /*@ assert i == 5; */ }\n"
                +"  public void inst2c() { int i = 5; int j = (i-=7); /*@ assert i == -2 && i == j; */ }\n"
                +"  public void inst2d() { int i = 5; int j = (i-=7); /*@ assert i == 5; */ }\n"
                +"  public void inst3() { int i = 5; i*=7; /*@ assert i == 5*7; */ }\n"
                +"  public void inst3b() { int i = 5; i*=7; /*@ assert i == 5; */ }\n"
                +"  public void inst3c() { int i = 5; int j = (i*=7); /*@ assert i == 5*7 && i == j; */ }\n"
                +"  public void inst3d() { int i = 5; int j = (i*=7); /*@ assert i == 5; */ }\n"
                +"  public void inst4() { int i = 5; i/=7; /*@ assert i == 5/7; */ }\n"
                +"  public void inst4b() { int i = 5; i/=7; /*@ assert i == 5; */ }\n"
                +"  public void inst4c() { int i = 5; int j = (i/=7); /*@ assert i == 5/7 && i == j; */ }\n"
                +"  public void inst4d() { int i = 5; int j = (i/=7); /*@ assert i == 5; */ }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1b",47,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst1d",57,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst2b",47,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst2d",57,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method inst3b",47,
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method inst3d",57,
                "/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Assert) in method inst4b",47,
                "/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Assert) in method inst4d",57
        ); // TODO -  need %= <<= >>= >>>= &= |= ^=
    }

    public void testConditional() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1(int i) { int j = i<0?-i:i; /*@ assert j >= 0; */ }\n"
                +"  public void inst1a(int i) { int j = i<0?-i:i; /*@ assert j == -1; */ }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1a",53
        );
    }

    public void testLblx() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1(int i) { /*@ assume i > 0; */ /*@ assert (\\lblpos ISP i>0); */}\n" // no report
                +"  public void inst1a(int i) { /*@ assume i > 0; */ /*@ assert (\\lblneg ISN i<0); */}\n" // reported
                +"  public void inst1b(int i) { /*@ assume i > 0; */ /*@ assert !(\\lblneg ISN2 i>0); */}\n" // no report
                +"  public void inst1c(int i) { /*@ assume i > 0; */ /*@ assert (\\lblpos ISP i<0); */}\n" // no report
                +"  public void inst1d(int i) { /*@ assume i > 0; */ /*@ assert !(\\lblpos ISP2 i>0); */}\n" // reported
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1a",56,
                "/tt/TestJava.java:4: warning: Label ISN reported",64,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method inst1b",56,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst1c",56,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst1d",56,
                "/tt/TestJava.java:7: warning: Label ISP2 reported",65
        );
    }

    public void testNewObject() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1() { Object o = new Object(); Object oo = new Object(); /*@ assert o != oo;*/ }\n" 
                +"  public void inst1a() { Object o = new Object(); Object oo = new Object(); /*@ assert o == oo;*/ }\n" 
                +"  public void inst2() { Object o = new Object(); /*@ assert o != null;*/ }\n" 
                +"  public void inst2a() { Object o = new Object(); /*@ assert o == null;*/ }\n" 
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1a",81,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst2a",55
        );
    }

    public void testNewArray() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1() { Object o = new int[5]; Object oo = new int[5]; /*@ assert o != oo;*/ }\n" 
                +"  public void inst1a() { Object o = new int[5]; Object oo = new int[5]; /*@ assert o == oo;*/ }\n" // FALSE
                +"  public void inst2() { int[] o = new int[5]; /*@ assert o != null; assert o.length == 5; */ }\n" 
                +"  public void inst2a() { int[] o = new int[5]; /*@ assert o.length == 6;*/ }\n"  // FALSE
                +"  public void inst3(/*@non_null*/int[] a) { /*@ assert a.length >= 0;*/ }\n" 
                +"  public void inst4() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 3; assert o[1] == 11;*/ }\n" 
                +"  public void inst4a() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 4; */ }\n"  // FALSE
                +"  public void inst4b() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 3; assert o[1] == 10;*/ }\n"  // FALSE
                +"  public void inst5() { Object o = new boolean[5]; Object oo = new boolean[5]; /*@ assert o != oo;*/ }\n" 
                +"  public void inst5a() { Object o = new boolean[5]; Object oo = new boolean[5]; /*@ assert o == oo;*/ }\n" // FALSE
                +"  public void inst6() { int[] o = {10,11,12}; /*@ assert o != null; assert o.length == 3; assert o[1] == 11;*/ }\n" 
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1a",77,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst2a",52,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method inst4a",61,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst4b",83,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method inst5a",85
        );
    }

    public void testNewArrayMD() { 
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst0() { Object o = new int[2][3]; o = new int[2][]; o = new int[][] {{2}, {3,4,5}}; int[][] oo = {{1},{2,3}}; /*@ assert oo[0] != oo[1]; */}\n" 
                +"  public void inst1() { Object o = new int[5][3]; Object oo = new int[5][3]; /*@ assert o != oo;*/ }\n" 
                +"  public void inst1a() { Object o = new int[5][3]; Object oo = new int[5][3]; /*@ assert o == oo;*/ }\n" // FALSE
                +"  public void inst2() { int[][] o = new int[5][3]; /*@ assert o.length == 5; assert o[1].length == 3; */ }\n" 
                +"  public void inst2a() { int[][] o = new int[5][3]; /*@ assert o.length == 6;*/ }\n" // FALSE
                +"  public void inst2b() { int[][] o = new int[5][3]; /*@ assert o[1].length == 4;*/ }\n" // FALSE
                +"  public void inst3(/*@non_null*/int[][] a) { /*@ assert a.length >= 0;*/ }\n" 
                +"  public void inst4() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o.length == 3; */ }\n" 
                +"  public void inst4a() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o.length == 2; */ }\n"  // FALSE
                +"  public void inst5() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[1][2] == 14; */ }\n" 
                +"  public void inst6() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[2].length == 1; */ }\n" 
                +"  public void inst7() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[0].length == 2; */ }\n" 
                +"  public void inst8() { int[][] o = new int[5][]; /*@ assert o != null; assert o.length == 5; assert o[1] == null; */ }\n" 
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method inst1a",83
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst2a",57
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst2b",57
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method inst4a",80
        );
    }

    public void testArrays() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst2(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  /*@ assert a[1] == 2; */ }\n" // OK
                +"  public void inst2a(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  /*@ assert a[1] == 3; */ }\n" // BAD
                +"  public void inst3(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */ }\n" // OK
                +"  public void inst3a(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 4; */ }\n" // BAD
                +"  public void inst4(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[0] == 2; */  a[1] = 3; /*@ assert a[0] == 2; */ }\n" // OK
                +"  public void inst4a(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[0] == 2; */  a[1] = 3; /*@ assert a[0] == 4; */ }\n" // BAD
                +"  public void inst5(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */  a[1] = 4; /*@ assert a[1] == 4; */}\n" // OK
                +"  public void inst5a(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */  a[1] = 4; /*@ assert a[1] == 5; */}\n" // BAD
                +"  public void inst6(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] == b[0]; */}\n" // OK
                +"  public void inst6a(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] != b[0]; */}\n" // BAD
                +"  public void inst7(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@ assume b.length == 10 && a.length == 10;*/ b[0] = 0; b = a; a[0] = 7; /*@ assert b[0] == 7; */}\n" // OK
                +"  public void inst7a(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@ assume b.length == 10 && a.length == 10;*/  b[0] = 0; b = a; a[0] = 7; /*@ assert b[0] == 8; */}\n" // BAD
                +"  public void inst8(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@ assume b.length == 10 && a.length == 12;*/ b = a; a[0] = 5; /*@ assert b != null; assert a != null; assert b.length == 12; assert a.length == 12; */}\n" // BAD
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst2a",103,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst3a",113,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst4a",113,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst5a",149,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method inst6a",106,
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method inst7a",147
        );
    }
    
    public void testArraysMD() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst2(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  /*@ assert a[1][2]; */ }\n" // OK
                +"  public void inst2a(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  /*@ assert !a[1][2]; */ }\n" // BAD
                +"  public void inst3(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  a[1][2] = false; /*@ assert !a[1][2]; */ }\n" // OK
                +"  public void inst3a(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  a[1][2] = true ; /*@ assert a[1][3]; */ }\n" // BAD
                +"  public void inst3b(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  a[1][2] = true ; /*@ assert a[0][2]; */ }\n" // BAD - a[0] might be null; even if it isn't a[0][2] is not necessarily true
                +"  public void inst4(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[0] != null; assume a[1].length == 5; assume a[0].length == 3; *//*@ assume a[0][0]; */  a[1][0] = false; /*@ assert a[0][0]; */ }\n" // OK
                +"  public void inst4a(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[0] != null; assume a[1].length == 5; assume a[0].length == 3; *//*@ assume a[0][0]; */  a[1][0] = false; /*@ assert !a[0][0]; */ }\n" // BAD
                +"  public void inst5(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; */  a[0] = a[1]; /*@ assert a[0][3] == a[1][3]; */}\n" // OK
                +"  public void inst5a(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; */ a[0] = a[1]; /*@ assert a[0][3] != a[1][3]; ; */}\n" // BAD
                +"  public void inst6(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] == b[0]; */}\n" // OK
                +"  public void inst6a(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] != b[0]; */}\n" // BAD
                +"  public void inst7(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@ assume b.length == 10 && a.length == 10 && b[0] != null && a[0] != null && b[0].length == 5 && a[0].length==6;*/ b[0][0] = true; b = a; a[0][0] = false; /*@ assert !b[0][0]; */}\n" // OK
                +"  public void inst7a(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@ assume b.length == 10 && a.length == 10 && b[0] != null && a[0] != null && b[0].length == 5 && a[0].length==6;*/  b[0][0] = true; b = a; a[0][0] = false; /*@ assert b[0][0]; */}\n" // BAD
                +"  public void inst8(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@ assume b.length == 10 && a.length == 12;*/ b = a; a[0] = null; /*@ assert b != null; assert a != null; assert b.length == 12; assert a.length == 12; */}\n" // OK
                +"  public void inst3c(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; assume a[0] != null; */  a[1][2] = false; /*@ assert a[0][2]; */ }\n" // BAD
                +"  public void inst3d(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; assume a[0] != null; assume a[0].length > 5; */  a[1][2] = false; /*@ assert a[0][2]; */ }\n" // BAD
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst2a",154
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst3a",171
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (UndefinedNullReference) in method inst3b",182
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method inst4a",217
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method inst5a",144
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method inst6a",118
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method inst7a",242
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method inst3c",-203
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method inst3c",-203
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Assert) in method inst3d",216
        );
    }
    
    public void testFields() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  int f; static int sf;\n"
                +"  int g; static int sg;\n"
                +"  static TestJava t;  //@ invariant t != null; \n"
                +"  public void inst2(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  /*@ assert t.f == 2; */ }\n" // OK
                +"  public void inst2a(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  /*@ assert t.f == 3; */ }\n" // BAD
                +"  public void inst3(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */ }\n" // OK
                +"  public void inst3a(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 4; */ }\n" // BAD
                +"  public void inst4(/*@non_null*/int[] a) { /*@ assume t.g == 2; */  t.f = 3; /*@ assert t.g == 2; */ }\n" // OK
                +"  public void inst4a(/*@non_null*/int[] a) { /*@ assume t.g == 2; */  t.f = 3; /*@ assert t.g == 4; */ }\n" // BAD
                +"  public void inst5(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */  t.f = 4; /*@ assert t.f == 4; */}\n" // OK
                +"  public void inst5a(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */  t.f = 4; /*@ assert t.f == 5; */}\n" // BAD
                +"  public void inst6(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b = a; /*@ assert a.f == b.f; */}\n" // OK
                +"  public void inst6a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b = a; /*@ assert a.f != b.f; */}\n" // BAD
                +"  public void inst7(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b.f = 0; b = a; a.f = 7; /*@ assert b.f == 7; */}\n" // OK
                +"  public void inst7a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b.f = 0; b = a; a.f = 7; /*@ assert b.f == 8; */}\n" // BAD
                +"  public void inst8(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { /*@ assert a.sf == b.sf; */}\n" // OK
                +"  public void inst8a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { /*@ assert a.sf != b.sf; */}\n" // BAD
                +"  public void inst9(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { a.sf = 3; /*@ assert 3 == b.sf; */}\n" // OK
                +"  public void inst9a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { a.sf = 3; /*@ assert 3 != b.sf; */}\n" // BAD
                +"  public void inst10(/*@non_null*/TestJava a) { /*@ assert f == this.f; */ /*@ assert a == this ==> a.f == f; */}\n" // OK
                +"  public void inst10a(/*@non_null*/TestJava a) { /*@ assert f == this.f; */ /*@ assert a.f == f; */}\n" // BAD
                +"  public void inst11(/*@non_null*/TestJava a) { /*@ assert sf == this.sf; */ /*@ assert a.sf == sf; */}\n" // OK
                +"}",
                "/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Invariant) in method <init>",8,
                "/tt/TestJava.java:5: warning: Associated declaration",37,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst2a",75,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method inst3a",84,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method inst4a",84,
                "/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method inst5a",118,
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method inst6a",85,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method inst7a",103,
                "/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Assert) in method inst8a",78,
                "/tt/TestJava.java:21: warning: The prover cannot establish an assertion (Assert) in method inst9a",88,
                "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Assert) in method inst10a",81
        );
    }

    public void testSwitch() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  int f; static int sf;\n"
                +"  int g; static int sg;\n"
                +"  static TestJava t;\n"
                +"  public void inst1(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; break; case 2: j = 2; } /*@ assert j!=0; */ }\n" // OK
                +"  public void inst1a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; break; case 2: j = 2; } /*@ assert j==1; */ }\n" // BAD
                +"  public void inst2(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; case 2: j = 2; } /*@ assert j>0; */ }\n" // OK
                +"  public void inst2a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; case 2: j = 2; } /*@ assert i==0 ==> j==-1; */ }\n" // BAD
                +"  public void inst3(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {default: i=4; } break; default: j=-1; case 2: j = 2; } /*@ assert j>=0; */ }\n" // OK
                +"  public void inst3a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {default: i=4; } break; default: j=-1; break; case 2: j = 2; } /*@ assert j>0; */ }\n" // OK
                +"  public void inst4(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {} break; default: j=-1; case 2: j = 2; } /*@ assert j>=0; */ }\n" // OK
                +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst1a",148,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method inst2a",141,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method inst3a",170
        );
    }

    public void testTry() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                +"  //@ ensures i == 2;\n"
                +"  public void inst1() { i=0; try { i = 1; return; } finally { i = 2; } }\n" // OK
                +"  //@ ensures i == 1;\n"
                +"  public void inst1a() { i=0; try { i = 1; return; } finally { i = 2; } }\n" // BAD
                +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method inst1a",44,
                "/tt/TestJava.java:6: warning: Associated declaration",15
        );
    }


    public void testMisc() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                +"  //@ requires i > 0;\n"
                +"  //@ ensures i > 0;\n"
                +"  public static void m() { i = i -1; }\n" // OK
                +"}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m",22,
                "/tt/TestJava.java:5: warning: Associated declaration",15
        );
    }

    public void testArith() {  // TODO - need more arithmetic support
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public static void m1(int a, int b) { /*@ assert a*2 == a + a; */ }\n"
                //+"  public static void m2(int a, int b) { /*@ assert a * b == a *(b-1) + a; */ }\n"
                +"  public static void m3(int a, int b) { /*@ assert (2*a)/2 == a; */ }\n"
                +"  public static void m4(int a, int b) { /*@ assert a >= 0 ==> (a%3) < 3; */ }\n"
                +"  public static void m5(int a, int b) { /*@ assert a >= 0 ==> (a%3) >= 0; */ }\n"
                //+"  public static void m6(int a, int b) { /*@ assert (a >= 0 && b > 0) ==> (a%b) >= 0; */ }\n"
                //+"  public static void m7(int a, int b) { /*@ assert (a >= 0 && b > 0) ==> ((a*b)%b) == 0; */ }\n"
                +"  public static void m8(int a, int b) { /*@ assert (a >= 0 ) ==> ((5*a)%5) == 0; */ }\n"
                +"}"
        );
    }

    public void testPureMethodStatic() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  //@ ensures \\result == i+1;\n"
                +"  //@ pure \n"
                +"  public static int m(int i) { return i+1; }\n"
                +"  public static void m1(int a, int b) { int k = a+1; /*@ assert k == m(a); */ }\n"
                +"  public static void m1a(int a, int b) { int k = a+2; /*@ assert k == m(a); */ }\n"
                +"  public static void m2(int a, int b) { int k = 2*a+2; /*@ assert k == m(a) + m(a); */ }\n"
                +"  public static void m2a(int a, int b) { int k = 2*a+2; /*@ assert k == 1 + m(a) + m(a); */ }\n"
                +"  public static void m3(int a, int b) { int k = a+3; /*@ assert k == m(m(a+1)); */ }\n"
                +"  public static void m3a(int a, int b) { int k = a+2; /*@ assert k == m(m(a+1)); */ }\n"
                +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m1a",59,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m2a",61,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method m3a",59
        );
    }

    public void testPureMethod() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  //@ ensures \\result == i+1;\n"
                +"  //@ pure \n"
                +"  public int m(int i) { return i+1; }\n"
                +"  public void m1(int a, int b) { int k = a+1; /*@ assert k == m(a); */ }\n"
                +"  public void m1a(int a, int b) { int k = a+2; /*@ assert k == m(a); */ }\n"
                +"  public void m2(int a, int b) { int k = 2*a+2; /*@ assert k == m(a) + m(a); */ }\n"
                +"  public void m2a(int a, int b) { int k = 2*a+2; /*@ assert k == 1 + m(a) + m(a); */ }\n"
                +"  public void m3(int a, int b) { int k = a+3; /*@ assert k == m(m(a+1)); */ }\n"
                +"  public void m3a(int a, int b) { int k = a+2; /*@ assert k == m(m(a+1)); */ }\n"
                +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m1a",52,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m2a",54,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method m3a",52
        );
    }

    public void testPureNonFunction() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  int z;\n"
                +"  //@ ensures \\result == z+1;\n"
                +"  //@ pure \n"
                +"  public int m() { return z+1; }\n"
                +"  public void m1(int a, int b) { int k = z+1; /*@ assert k == m(); */ }\n"
                +"  public void m1a(int a, int b) { int k = z+2; /*@ assert k == m(); */ }\n"
                +"  public void m2(int a, int b) { int k = 2*z+2; /*@ assert k == m() + m(); */ }\n"
                +"  public void m2a(int a, int b) { int k = 2*z+2; /*@ assert k == 1 + m() + m(); */ }\n"
                +"  public void m3(int a, int b) { z = 7; int k = z+1; /*@ assert k == m(); */ }\n"
                +"  public void m3a(int a, int b) { z = 7; int k = z+2; /*@ assert k == m(); */ }\n"
                +"}",
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m1a",52,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m2a",54,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method m3a",59
        );
    }

    public void testPureNoArguments() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  static int z;\n"
                +"  //@ ensures \\result == z+1;\n"
                +"  //@ pure \n"
                +"  public static int m() { return z+1; }\n"
                +"  public void m1(int a, int b) { int k = z+1; /*@ assert k == m(); */ }\n"
                +"  public void m1a(int a, int b) { int k = z+2; /*@ assert k == m(); */ }\n"
                +"  public void m2(int a, int b) { int k = 2*z+2; /*@ assert k == m() + m(); */ }\n"
                +"  public void m2a(int a, int b) { int k = 2*z+2; /*@ assert k == 1 + m() + m(); */ }\n"
                +"}",
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m1a",52,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m2a",54
        );
    }

    public void testInheritedPost() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"abstract class TestJavaA { \n"
                +"  //@ requires iii > 0;\n"
                +"  //@ ensures \\result > 0;\n"
                +"  abstract public int m(int iii);\n"
                +"}\n"
                +"abstract class TestJavaB extends TestJavaA { \n"
                +"  //@ also\n"
                +"  //@ ensures \\result > ii;\n"
                +"  abstract public int m(int ii);\n"
                +"}\n"
                +"public class TestJava extends TestJavaB { \n"
                +"  //@ also\n"
                +"  //@ ensures \\result == i+1;\n"
                +"  //@ pure\n"
                +"  public int m(int i) { return i+1; }\n"
                +"  //@ ensures \\result == a+1;\n"
                +"  public int m1(int a) { return m(a); }\n"
                +"  public int m1a(int a) { return m(-1); }\n"
                +"}"
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method m",25
                ,"/tt/TestJava.java:4: warning: Associated declaration",15
        );
    }

    public void testInheritedPostB() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"abstract class TestJavaA { \n"
                +"  //@ requires iii > 0;\n"
                +"  //@ ensures \\result > 0;\n"
                +"  abstract public int m(int iii);\n"
                +"}\n"
                +"abstract class TestJavaB extends TestJavaA { \n"
                +"  //@ also\n"
                +"  //@ requires ii > 0;\n"
                +"  //@ ensures \\result > ii;\n"
                +"  abstract public int m(int ii);\n"
                +"}\n"
                +"public class TestJava extends TestJavaB { \n"
                +"  //@ also\n"
                +"  //@ requires i > 0;\n"
                +"  //@ ensures \\result == i+1;\n"
                +"  //@ pure\n"
                +"  public int m(int i) { return i+1; }\n"
                +"}"
        );
    }

    public void testInheritedPre() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"abstract class TestJavaA { \n"
                +"  //@ requires iii == 1;\n"
                +"  //@ ensures \\result == iii;\n"
                +"  abstract public int m(int iii);\n"
                +"}\n"
                +"abstract class TestJavaB extends TestJavaA { \n"
                +"  //@ also\n"
                +"  //@ requires ii == 2;\n"
                +"  //@ ensures \\result == ii;\n"
                +"  abstract public int m(int ii);\n"
                +"}\n"
                +"public class TestJava extends TestJavaB { \n"
                +"  //@ also\n"
                +"  //@ requires i == 3;\n"
                +"  //@ ensures \\result == i;\n"
                +"  //@ pure\n"
                +"  public int m(int i) { return i; }\n"
                +"  //@ requires a >= 1 && a <= 3;\n"
                +"  //@ ensures \\result == a;\n"
                +"  public int m1(int a) { return m(a); }\n"
                +"  //@ ensures \\result == a;\n"
                +"  public int m1a(int a) { return m(-1); }\n"
                +"}",
                //"/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Postcondition) in method m1a",14,
                //"/tt/TestJava.java:22: warning: Associated declaration",15,
                "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Precondition) in method m1a",35,
                "/tt/TestJava.java:15: warning: Associated declaration",7
        );
    }

    public void testTrace() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires 0<=ii && ii <=3;\n"
                +"  //@ ensures \\result < 0;\n"
                +"  public static int m(int ii) { \n"
                +"    if (ii==1) return -1; \n"
                +"    if (ii==2) return -2; \n"
                +"    if (ii==3) return -3; \n"
                +"    ii = 7;\n"
                +"    return 0; }\n"
                +"  //@ requires ii == 2;\n"
                +"  //@ ensures \\result == 0;\n"
                +"  public static int mm(int ii) { \n"
                +"    if (ii==1) return -1; \n"
                +"    if (ii==2) return -2; \n"
                +"    if (ii==3) return -3; \n"
                +"    ii = 7;\n"
                +"    return 0; }\n"
                +"  public static int is;"
                +"  //@ ensures is == 6;\n"
                +"  public static int m3(int ii) { \n"
                +"    try { ii = 0; \n"
                +"      if (ii == 0) return -2; \n"
                +"    } finally { \n"
                +"      is = 7;\n"
                +"    }"
                +"    return 0; }\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public static int m4(int ii) { \n"
                +"    try { ii = 0; \n"
                +"      if (ii == 0) return -2; \n"
                +"    } finally { \n"
                +"      is = 7;\n"
                +"    }"
                +"    return 0; }\n"
                +"}",
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method m",5,
                "/tt/TestJava.java:4: warning: Associated declaration",15,
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Postcondition) in method mm",16,
                "/tt/TestJava.java:12: warning: Associated declaration",15,
                "/tt/TestJava.java:22: warning: The prover cannot establish an assertion (Postcondition) in method m3",20,
                "/tt/TestJava.java:19: warning: Associated declaration",38,
                "/tt/TestJava.java:29: warning: The prover cannot establish an assertion (Postcondition) in method m4",20,
                "/tt/TestJava.java:26: warning: Associated declaration",15
        );
    }

    public void _testForwardInit() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static int m() { \n"
                +"    int c = c+1; \n"
                +"    //@ assert c == 1; \n"
                +"    return c; \n"
                +"  }\n"
                +"}",
                "/tt/TestJava.java:4: variable c might not have been initialized",13
        );
    }

    public void testGhostVars() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static int m() { \n"
                +"    int c = 4; \n"
                +"    //@ ghost int d = c+1;\n"
                +"    //@ assert d + c == 9; \n"
                +"    return c; \n"
                +"  }\n"
                +"  public static int mm() { \n"
                +"    int c = 4; \n"
                +"    //@ ghost int d = c+1;\n"
                +"    //@ assert d + c == 10; \n"
                +"    return c; \n"
                +"  }\n"
                +"}",
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method mm",9
        );
    }

    public void testSetDebug() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static int m() { \n"
                +"    int c = 4; \n"
                +"    //@ ghost int d = c+1;\n"
                +"    //@ set d = 10;\n"
                +"    //@ assert d + c == 14; \n"
                +"    return c; \n"
                +"  }\n"
                +"  public static int mm() { \n"
                +"    int c = 4; \n"
                +"    //@ ghost int d = c+1;\n"
                +"    //@ set d = 10;\n"
                +"    //@ assert d + c == 15; \n"
                +"    return c; \n"
                +"  }\n"
                +"  public static int q() { \n"
                +"    int c = 4; \n"
                +"    //@ ghost int d = c+1;\n"
                +"    //@ debug d = 10;\n"
                +"    //@ assert d + c == 14; \n"
                +"    return c; \n"
                +"  }\n"
                +"  public static int qq() { \n"
                +"    int c = 4; \n"
                +"    //@ ghost int d = c+1;\n"
                +"    //@ debug d = 10;\n"
                +"    //@ assert d + c == 15; \n"
                +"    return c; \n"
                +"  }\n"
                +"}",
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method mm",9,
                "/tt/TestJava.java:28: warning: The prover cannot establish an assertion (Assert) in method qq",9
        );
    }

    /** Tests whether various ways of guarding a field reference are successful in
     * avoiding a failed assertion.
     */
    public void testUndefinedInJava() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j;\n"
                +"  public static void m(TestJava o) { \n"
                +"    int i = o.j; \n"
                +"  }\n"
                +"  public static void m1(/*@non_null*/ TestJava o) { \n"
                +"    int i = o.j; \n"
                +"  }\n"
                +"  //@ requires o != null;\n"
                +"  public static void m2(TestJava o) { \n"
                +"    int i = o.j; \n"
                +"  }\n"
                +"  public static void m3(TestJava o) { \n"
                +"    boolean i = o != null && o.j == 1; \n"
                +"  }\n"
                +"  public static void m4(TestJava o) { \n"
                +"    boolean i = o == null || o.j == 1; \n"
                +"  }\n"
                +"  public static void m5(TestJava o) { \n"
                +"    int i = ( o != null ? o.j : 6); \n"
                +"  }\n"
                +"  public static void m6(TestJava o) { \n"
                +"    int i = ( o == null ? 7 : o.j); \n"
                +"  }\n"
                +"  public static void m6a(TestJava o) { \n"
                +"    int i = ( o != null ? 7 : o.j); \n"
                +"  }\n"
                +"  //@ public normal_behavior  ensures \\result == (oo != null);\n"
                +"  public static boolean p(TestJava oo) { \n"
                +"    return oo != null; \n"
                +"  }\n"
                +"  public static void m7(TestJava o) { \n"
                +"    boolean i = p(o) && o.j == 0; \n"
                +"  }\n"
                +"  public static void m7a(TestJava o) { \n"
                +"    boolean i = p(o) || o.j == 0; \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m",14
                ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m6a",32
                ,"/tt/TestJava.java:37: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m7a",26
        );
    }
    /** Tests whether the various kinds of undefined constructs are actually detected.
     */ 
    public void testUndefinedInJava2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j;\n"
                +"  public static void m(TestJava o) { \n"
                +"    int i = o.j; \n"
                +"  }\n  "
                +"  public static void m1(int[] a) { \n"
                +"    int i = a[0]; \n"
                +"  }\n"
                +"  //@ requires a != null;\n"
                +"  public static void m2(int[] a) { \n"
                +"    int i = a[-1]; \n"
                +"  }\n"
                +"  //@ requires a != null;\n"
                +"  public static void m3(int[] a) { \n"
                +"    //@ assume a.length == 1; \n"
                +"    int i = a[1]; \n"
                +"  }\n"
                +"  public static void m4(int i, int j) { \n"
                +"    int k = i/j; \n"
                +"  }\n"
                +"  public static void m5(int i, int j) { \n"
                +"    int k = i%j; \n"
                +"  }\n"
                +"  public static void m6( RuntimeException r) { \n"
                +"    Throwable t = r;\n"
                +"    Exception rr = ((Exception)t); \n"
                +"  }\n"
                +"  public static void m6a(Exception r) { \n"
                +"    Throwable t = r;\n"
                +"    RuntimeException rr = ((RuntimeException)t) ; \n"
                +"  }\n"
                +"  public static void m7(/*@ non_null*/ RuntimeException r) { \n"
                +"    Throwable t = r;\n"
                +"    Exception rr = ((Exception)t); \n"
                +"  }\n"
                +"  public static void m7a(/*@ non_null*/Exception r) { \n"
                +"    Throwable t = r;\n"
                +"    RuntimeException rr = ((RuntimeException)t) ; \n"
                +"  }\n"
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m",14,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m1",-14,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1",-14,  // FIXME - does need to have one of these errors in m1
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m2",14,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m3",14,
                "/tt/TestJava.java:20: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m4",14,
                "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m5",14,
                "/tt/TestJava.java:31: warning: The prover cannot establish an assertion (PossiblyBadCast) in method m6a",28,
                "/tt/TestJava.java:39: warning: The prover cannot establish an assertion (PossiblyBadCast) in method m7a",28
        );
    }


    /** Tests whether various ways of guarding a field reference are successful in
     * avoiding a failed assertion.
     */
    public void testUndefinedInSpec() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j;\n"
                +"  public static void m(TestJava o) { \n"
                +"    //@ assume o.j == 1; \n"
                +"  }\n"
                +"  public static void m1(/*@non_null*/ TestJava o) { \n"
                +"    //@ assume o.j == 1; \n"
                +"  }\n"
                +"  //@ requires o != null;\n"
                +"  public static void m2(TestJava o) { \n"
                +"    //@ assume o.j == 1; \n"
                +"  }\n"
                +"  public static void m3(TestJava o) { \n"
                +"    //@ assume o != null && o.j == 1; \n"
                +"  }\n"
                +"  public static void m4(TestJava o) { \n"
                +"    //@ assume o == null || o.j == 1; \n"
                +"  }\n"
                +"  public static void m5(TestJava o) { \n"
                +"    //@ assume o != null ==> o.j == 1; \n"
                +"  }\n"
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m",17
        );
    }

    /** Tests whether the various kinds of undefined constructs are actually detected.
     */  // TODO - need pure method violating preconditions, bad array element assignment
    public void testUndefinedInSpec2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j;\n"
                +"  public static void m(TestJava o) { \n"
                +"    //@ assume o.j == 1; \n"
                +"  }\n  "
                +"  public static void m1(int[] a) { \n"
                +"    //@ assume a[0] == 1; \n"
                +"  }\n"
                +"  //@ requires a != null;\n"
                +"  public static void m2(int[] a) { \n"
                +"    //@ assume a[-1] == 1; \n"
                +"  }\n"
                +"  //@ requires a != null;\n"
                +"  public static void m3(int[] a) { \n"
                +"    //@ assume a.length == 1; \n"
                +"    //@ assume a[1] == 1; \n"
                +"  }\n"
                +"  public static void m4(int i, int j) { \n"
                +"    //@ assume i/j == 4; \n"
                +"  }\n"
                +"  public static void m5(int i, int j) { \n"
                +"    //@ assume i%j == 4; \n"
                +"  }\n"
                +"  public static void m6(RuntimeException r) { \n"
                +"    Throwable t = r;\n"
                +"    //@ assume ((Exception)t) != null ? true : true; \n"
                +"  }\n"
                +"  public static void m6a(Exception r) { \n"
                +"    Throwable t = r;\n"
                +"    //@ assume ((RuntimeException)t) != null ? true : true ; \n"
                +"  }\n"
                +"  public static void m7(/*@ non_null*/RuntimeException r) { \n"
                +"    Throwable t = r;\n"
                +"    //@ assume ((Exception)t) != null ? true : true; \n"
                +"  }\n"
                +"  public static void m7a(/*@ non_null*/Exception r) { \n"
                +"    Throwable t = r;\n"
                +"    //@ assume ((RuntimeException)t) != null ? true : true ; \n"
                +"  }\n"
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m",17,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m1",-17, // Sometimes found
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m1",-17, // Sometimes found
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m2",17,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m3",17,
                "/tt/TestJava.java:20: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m4",17,
                "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m5",17
                ,"/tt/TestJava.java:31: warning: The prover cannot establish an assertion (UndefinedBadCast) in method m6a",17
                ,"/tt/TestJava.java:39: warning: The prover cannot establish an assertion (UndefinedBadCast) in method m7a",17
        );
    }

    /** Tests whether undefinedness is caught in various JML constructions */
    // TODO - loop invariants, variants,  represents,  signals, modifies 
    // TODO - old constructs, quantifications, set comprehension, pure methods - check other JMl expressions
    public void testUndefinedInSpec3() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  int j = 1;\n"
                +"  static @Nullable TestJava t;\n"
                +"  public static void m(TestJava o) { \n"
                +"    //@ assume o.j == 1; \n"
                +"  }\n  "
                +"  public static void m1(TestJava o) { \n"
                +"    //@ assert o.j == 1 ? true : true; \n"
                +"  }\n  "
                +"  public static void m2(TestJava o) { \n"
                +"    //@ ghost int i = o.j; \n"
                +"  }\n  "
                +"  public static void m3(TestJava o) { \n"
                +"    //@ ghost int i; debug i = o.j; \n"
                +"  }\n  "
                +"  //@ requires o.j == 1;\n"
                +"  public static void m4(@Nullable TestJava o) { \n"
                +"  }\n  "
                +"  //@ ensures t.j == 1 ? true : true;\n"
                +"  public static void m5(TestJava o) { \n"
                +"  }\n  "
                +"  public static void m6(TestJava o) { \n"
                +"    //@ ghost int i; set i = o.j; \n"
                +"  }\n  "
                +"}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m",17,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m1",17,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m2",24,
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m3",33,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m4",19,
                "/tt/TestJava.java:20: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m5",18,
                "/tt/TestJava.java:24: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m6",31
        );   
    }
    /** Tests whether undefinedness is caught in various JML constructions */
    // TODO - readable writable, represents, assert, other clauses
    public void testUndefinedInSpec4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j = 1;\n"
                +"  static TestJava t;\n"
                +"  public void m(TestJava o) { \n"
                +"    //@ assume o.j == 1; \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m",17
        );
    }
    
    public void testUndefinedInSpec4d() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j = 1;\n"
                +"  static TestJava t;\n"
                +"  public void m(TestJava o) { \n"
                +"  }\n"
                +"  //@ invariant t.j ==1 ? true: true;\n"
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (UndefinedNullReference) in method <init>",18
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m",18
        );
    }
    
    /** Check to catch undefinedness in an initially clause */
    public void testUndefinedInSpec4a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  boolean j = true;\n"
                +"  static TestJava t;\n"
                +"  public TestJava() { \n"
                +"  }\n"
                +"  //@ initially t.j ? true : true;\n"
                +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (UndefinedNullReference) in method <init>",18
        );
    }

    /** Check to catch undefinedness in a constraint clause */
    public void testUndefinedInSpec4b() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j = 1;\n"
                +"  static TestJava t;\n"
                +"  public void m(TestJava o) { \n"
                +"  }\n  "
                +"  //@ constraint t.j ==1 ? true: true;\n"
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m",21
        );
    }

    /** Check to catch undefinedness in a axiom clause */
    public void testUndefinedInSpec4c() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j = 1;\n"
                +"  static TestJava t;\n"
                +"  public void m(TestJava o) { \n"
                +"  }\n  "
                +"  // @ axiom (\\forall TestJava q;; q.j ==1);\n" // FIXME
                +"}"
        );
    }
    
    // TODO - class initialization
    public void _testUndefinedInSpec5() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static TestJava t;\n"
                +"  int j = t.j;\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m2",19
        );
    }

    public void testUndefinedInJava6() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static TestJava t;\n"
                +"  int j = 1;\n"
                +"  public void m1(TestJava o) { \n"
                +"    int i = t.j; \n"
                +"  }\n  "
                +"  public void m2(TestJava o) { \n"
                +"    t.j = 1; \n"
                +"  }\n  "
                +"  public void m3(TestJava o) { \n"
                +"    t.j += 1; \n"
                +"  }\n  "
                +"  public void m4(TestJava o) { \n"
                +"    int i = 0; i += t.j; \n"
                +"  }\n  "
                +"  public void m5(TestJava o) { \n"
                +"    assert t.j == 1 ? true : true; \n"
                +"  }\n  "
                // TODO for, while, foreach, do, switch, case, if, throw, method call, index, conditional, 
                // annotation, binary, unary, conditional, new array, new class, return, synchronized
                +"}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m1",14,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m2",6,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m3",6,
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m4",22,
                "/tt/TestJava.java:18: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m5",13
        );
    }

    // TODO - need tests within various Java constructs, including with short-circuits

    /** This test tests catch blocks */
    public void testCatch() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m() {\n"
                +"    int i = 0;\n"
                +"    try {\n"
                +"      throw new RuntimeException();\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    }\n"
                +"    //@ assert i == 1;\n"
                +"  }\n"
                +"  public void ma() {\n"
                +"    int i = 0;\n"
                +"    try {\n"
                +"      throw new RuntimeException();\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    }\n"
                +"    //@ assert i == 2;\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Assert) in method ma",9
                );
    }
    
    public void testCatch2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m() {\n"
                +"    int i = 0;\n"
                +"    try {\n"
                +"      throw new Exception();\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    }\n"
                +"    //@ assert i == 2;\n"
                +"  }\n"
                +"  public void mp() {\n"
                +"    int i = 0; int j = 0;\n"
                +"    try {\n"
                +"      throw new Exception();\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    } finally {\n"
                +"      j=3;\n"
                +"    }\n"
                +"    //@ assert i == 2 && j == 3;\n"
                +"  }\n"
                +"  public void ma() {\n"
                +"    int i = 0;\n"
                +"    try {\n"
                +"      throw new Exception();\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    }\n"
                +"    //@ assert i == 1;\n"
                +"  }\n"
                +"  public void m1(int k) {\n"
                +"    int i = 0; int j = 0; //@ assume k == 0; \n"
                +"    try {\n"
                +"      try {\n"
                +"         if (k == 0) throw new Exception();\n"
                +"      } finally {\n"
                +"         j = 50;\n"
                +"      }\n"
                +"      j = 60;\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    }\n"
                +"    //@ assert i == 2 && j == 50;\n"
                +"  }\n"
                +"  public void m11(int k) throws Exception {\n"
                +"    int i = 0; int j = 0; //@ assume k == 0; \n"
                +"    try {\n"
                +"    try {\n"
                +"      try {\n"
                +"         if (k == 0) throw new Exception();\n"
                +"      } finally {\n"
                +"         j = 50;\n"
                +"      }\n"
                +"      j = 60;\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } finally {\n"
                +"      i=2;\n"
                +"    }\n"
                +"    } finally {\n"
                +"    //@ assert i == 2 && j == 50;\n"
                +"    }\n"

                +"  }\n"
                +"  public void m2() {\n"
                +"    int i = 20;\n"
                +"    try {\n"
                +"      i=10;\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    }\n"
                +"    i = 0;\n"
                +"    //@ assert i == 0;\n"
                +"  }\n"
                +"  public void m3() {\n"
                +"    int i = 20;\n"
                +"    try {\n"
                +"      i=10;\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    } finally {\n"
                +"      i = 0;\n"
                +"    }\n"
                +"    //@ assert i == 0;\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (Assert) in method ma",9
                ,"/tt/TestJava.java:42: warning: else branch apparently never taken in method m1(int)",14
                ,"/tt/TestJava.java:59: warning: else branch apparently never taken in method m11(int)",14
                );
    }
    
    public void testTypes() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1(/*@non_null*/Object o) {\n"
                +"    //@ assume \\typeof(o) == \\type(Object);\n"
                +"    //@ assert \\typeof(o) == \\typeof(o);\n"
                +"    //@ assert \\typeof(o) == \\type(Object);\n"
                +"    //@ assert \\typeof(o) <: \\type(Object);\n"
                +"  }\n"
                +"  public void m1a(/*@non_null*/Object o) {\n"
                +"    //@ assume \\typeof(o) == \\type(Object);\n"
                +"    //@ assert \\typeof(o) != \\type(Object);\n"
                +"  }\n"
                +"  public void m2(/*@non_null*/Object o) {\n"
                +"    //@ assume \\typeof(o) == \\type(Object);\n"
                +"    //@ assert \\typeof(o) == \\type(Object);\n"
                +"  }\n"
                +"  public void m2a(/*@non_null*/Object o) {\n"
                +"    //@ assume \\typeof(o) == \\type(Object);\n"
                +"    //@ assert \\typeof(o) == \\type(TestJava);\n"
                +"  }\n"
                +"  public void m3(/*@non_null*/Object o) {\n"
                +"    //@ assume \\typeof(o) == \\type(Object);\n"
                +"    //@ assert \\type(TestJava) <: \\typeof(o);\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method m1a",9
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Assert) in method m2a",9
                );
    }
    public void testTypes2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1(/*@non_null*/TestJava o) {\n"
                +"    //@ assume \\typeof(o) <: \\type(TestJava);\n"
                +"    //@ assert \\typeof(o) <: \\type(Object);\n"
                +"  }\n"
                +"  public void m2(/*@non_null*/TestJava o) {\n"
                +"    //@ assert \\typeof(o) <: \\type(Object);\n"
                +"  }\n"
                +"}"
                );
    }
    
    public void testTypes3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1(/*@non_null*/Object o) {\n"
                +"    //@ assert \\typeof(o).erasure() == o.getClass();\n"
                +"  }\n"
                +"}"
                );
    }

    public void testSignals() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                +"  //@ requires i >= 0;\n"
                +"  //@ ensures i>0;\n"
                +"  //@ signals (Exception e) i == 0;\n"
                +"  public void m1() throws Exception {\n"
                +"    if (i==0) throw new Exception();\n"
                +"  }\n"
                +"  //@ requires i >= 0;\n"
                +"  //@ ensures i>0;\n"
                +"  //@ signals (Exception e) i == 1;\n" // FAILS
                +"  public void m1a() throws Exception {\n"
                +"    if (i==0) throw new Exception();\n"
                +"  }\n"
                +"  //@ requires i >= 0;\n"
                +"  //@ ensures i>0;\n"
                +"  //@ signals (RuntimeException e) i == 1;\n"
                +"  public void m2() throws Exception {\n"
                +"    if (i==0) throw new Exception();\n"
                +"  }\n"
                +"  //@ requires i >= 0;\n"
                +"  //@ ensures i>0;\n"
                +"  //@ signals (Exception e) i == 0;\n"
                +"  public void m3() {\n"
                +"    if (i==0) throw new RuntimeException();\n"
                +"  }\n"
                +"  //@ requires i >= 0;\n"
                +"  //@ ensures i>0;\n"
                +"  //@ signals (Exception e) i == 1;\n" // FAILS
                +"  public void m3a() {\n"
                +"    if (i==0) throw new RuntimeException();\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1a",15
                ,"/tt/TestJava.java:12: warning: Associated declaration",7
                ,"/tt/TestJava.java:32: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m3a",15
                ,"/tt/TestJava.java:30: warning: Associated declaration",7
                );
    }

    public void testSignalsOnly() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                +"  //@ signals_only java.io.IOException;\n" // FAILS
                +"  public void m1a() throws Exception {\n"
                +"    if (i==0) throw new Exception();\n"
                +"  }\n"
                +"  //@ signals_only \\nothing;\n"  // FAILS
                +"  public void m2a() {\n"
                +"    if (i==0) throw new RuntimeException();\n"
                +"  }\n"
                +"  //@ signals_only Exception;\n"  // OK
                +"  public void m3() {\n"
                +"    if (i==0) throw new RuntimeException();\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1a",15
                ,"/tt/TestJava.java:4: warning: Associated declaration",20
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m2a",15
                ,"/tt/TestJava.java:8: warning: Associated declaration",7
                );
    }

    
}

