package tests;

import org.jmlspecs.openjml.esc.JmlEsc;

/** This class of JUnit tests checks various uses of generic types.
 * @author David R. Cok
 *
 */
public class escgeneric extends EscBase {

    public void setUp() throws Exception {
        //print = true;
        //noCollectDiagnostics = true;
        super.setUp();
        options.put("-noPurityCheck","");
        options.put("-nullableByDefault",""); // Because the tests were written this way
//        options.put("-showbb",   "");
//        options.put("-jmlverbose",   "");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        JmlEsc.escdebug = false;
    }
    
    // FIXME - disabled until we get generic types implemented better
    public void testConstructor() {
//        options.put("-showbb","");
//        options.put("-trace","");
//        options.put("-method","ma");
        //JmlEsc.escdebug = true;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void mx(Integer i) {\n"
                +"    Object oo = new TestG<Integer>(i);\n"
                +"  }\n"
                +"  public void ma(Object o) {\n"
                +"    Object oo = new TestG<Object>(o);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"  //@   requires \\type(E) != \\type(Integer) ;\n"
                +"  public TestG(E i) {}\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method mx",17
                ,"/tt/TestJava.java:12: warning: Associated declaration",10
                );
    }
    
    /** Tests that we can reason about the result of \\typeof */
    public void testTypeOf() {
//        options.put("-showbb","");
//        options.put("-trace","");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m(Integer i) {\n"
                +"    //@ assert \\typeof(this) <: \\type(TestJava);\n"
                +"  }\n"
                +"  public void ma(Object o) {\n"
                +"    //@ assume \\typeof(this) == \\type(Object);\n"
                +"    //@ assert false;\n" // should not trigger
                +"  }\n"
                +"  public void mb(Object o) {\n"
                +"    //@ assert \\typeof(this) == \\type(Object);\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:7: warning: An assumption appears to be infeasible in method ma(java.lang.Object)",9
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method mb",9
                );
    }
    
    public void testGenericType() {
//        options.put("-showbb","");
//        options.put("-trace","");
//        options.put("-method","m");
//        JmlEsc.escdebug= true;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava<T extends B> { \n"
                
                +"  public void m(Integer i) {\n"
                +"    //@ assert Object.class == java.lang.Object.class;\n"
                +"    //@ assert \\type(TestJava<Integer>) != \\type(Object);\n" // FIXME - should be an error because Integer does not extend B
                +"    //@ assert \\type(TestJava<Integer>) != \\type(TestJava<Object>);\n" // FIXME - should be error because
                +"  }\n"
                +"  public void mz(Object o) {\n"
                +"    //@ assert Object.class == \\type(T).erasure();\n"  // NO
                +"  }\n"
                +"  public void ma(Object o) {\n"
                +"    //@ assert \\type(TestJava<Integer>) == \\type(TestJava<T>);\n"  // NO
                +"  }\n"
                +"  public void mb(Object o) {\n"
                +"    //@ assert \\typeof(this) == \\type(Object);\n"  // NO
                +"  }\n"
                +"  public void mc(Object o) {\n"
                +"    //@ assert \\type(TestJava<Integer>) == \\type(TestJava<Object>);\n"  // NO
                +"  }\n"
                +"  public void mz1(Object o) {\n"
                +"    //@ assert Object.class != \\type(T).erasure();\n"  // OK because T extends B so can't be Object
                +"  }\n"
                +"  public TestJava() {}\n"
                +"}\n"
                +"class B {}\n"
                +"class C {}\n"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method mz",9
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method ma",9
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method mb",9
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Assert) in method mc",9
        );
    }

    public void testStatic() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  public void ma(Integer i) {\n"
                +"    TestG.<Integer>mm(i);\n"
                +"  }\n"
                +"  public void mb(Object o) {\n"
                +"    TestG.<Object>mm(o);\n"
                +"  }\n"
                +"}\n"
                +"class TestG {\n"
                +"  //@   requires \\type(E) != \\type(Integer) ;\n"
                +"  public static <E> void mm(E t) {}\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method ma",22
                ,"/tt/TestJava.java:11: warning: Associated declaration",24
        );
    }

    public void testTypeParameter() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void ma(/*@ non_null*/ TestG<Integer> i, Integer j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"  public void mb(/*@ non_null*/ TestG<Object> i, Object j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"    //@ requires \\type(E) != \\type(Integer);\n"
                +"    public void mm(E t) {}\n"
                +"}\n"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method ma",9
                ,"/tt/TestJava.java:11: warning: Associated declaration",24
                );
    }
    
    public void testTypeParameter2() {
//        options.put("-showbb","");
//        options.put("-trace","");
//              options.put("-method","mb");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void ma(/*@ non_null*/TestG<Integer>.TestH i, Integer j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"  public void mb(/*@ non_null*/TestG<Object>.TestH i, Object j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"  class TestH extends TestG<Integer> {\n"
                +"    //@ requires \\type(E) != \\type(Integer);\n"
                +"    public void mm(E t) {}\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method ma",9
                ,"/tt/TestJava.java:12: warning: Associated declaration",24
                );
    }
 
    // FIXME - autoboxing not working for ESC
//    public void testForEach3() {
//      options.put("-showbb","");
//      options.put("-trace","");
//            options.put("-method","m");
//        helpTCX("tt.TestJava"," class A { void m(java.util.List<Integer> list) { \n "
//                +"int sum = 0; \n"
//                +"//@ loop_invariant sum >= 0; \n"
//                +"for (int o: list) { /*@ assume o >= 0; */ sum += o; }  \n"
//                +"//@ assert sum >= 0; \n"
//                +"}}"
//                );
//    }
//
//    public void testForEach3bad() {
//        helpTCX("tt.TestJava"," class A { void m(java.util.List<Integer> list) { \n "
//                +"int sum = 0; \n"
//                +"//@ loop_invariant sum >= 0; \n"
//                +"for (int o: list) { /*@ assume o >= 0; */ sum += o; }  \n"
//                +"//@ assert sum > 0; \n"
//                +"}}"
//                );
//    }
//
    
}
    
