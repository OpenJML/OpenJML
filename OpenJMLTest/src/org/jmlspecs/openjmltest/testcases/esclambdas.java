package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.ParameterizedWithNames;

import java.util.function.Function;

@RunWith(ParameterizedWithNames.class)
public class esclambdas extends EscBase {

    public esclambdas(String options, String solver) {
        super(options,solver);
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
    
    @Test
    public void testIterable1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public static class MMM {\n"
                +"    public int i ;\n"
                +"    public void bump() { i++; }\n"
                +"  }\n"
                
                +"  public void m1(Iterable<@org.jmlspecs.annotation.Nullable MMM> a) {\n"
                +"    a.forEach(MMM::bump);\n"
                +"  }\n"
                                
                +"}"
                // FIXME - the column location is wrong - it is not clear that the possible null value is an element of the iterable, with the element being the receiver of the bump call in the foreach loop
                ,"$SPECS/java8/java/lang/Iterable.jml:11: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",0
                );
    }
    
    @Test
    public void testIterable1b() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public static class MMM {\n"
                +"    public int i ;\n"
                +"    public void bump() { i++; }\n"
                +"  }\n"
                
                +"  public void m1(Iterable<@org.jmlspecs.annotation.NonNull MMM> a) {\n"
                +"    a.forEach(MMM::bump);\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    @Test
    public void testIterable2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public static class MMM {\n"
                +"    public int i ;\n"
                +"    public void bump() { i++; }\n"
                +"  }\n"
                
                +"  public void m1(/*@ non_null*/ Iterable<@org.jmlspecs.annotation.Nullable MMM> a) {\n"  // We do not know that each element returned by the iterable is non-null
                +"    a.forEach(m->m.bump());\n"
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",19
                );
    }
    
    @Test
    public void testIterable2b() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public static class MMM {\n"
                +"    public int i ;\n"
                +"    public void bump() { i++; }\n"
                +"  }\n"
                
                +"  public void m1(/*@ non_null*/ Iterable<@org.jmlspecs.annotation.NonNull MMM> a) {\n"
                +"    a.forEach(m->m.bump());\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    @Test
    public void testIterable3() {
        main.addOptions("-code-math=java","-spec-math=java");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int j;\n"
                +"  public int k() { return 7; };\n"
                +"  public static class MMM {\n"
                +"    public int i ;\n"
                +"  }\n"
                
                +"  public void bump(MMM m1, MMM m2) {"
                +"     m1.i += (j + m2.i + k());\n"
                +"  }\n"
                
                +"  public void m1(/*@ non_null*/ Iterable<MMM> a) {\n"
                +"    a.forEach(m->bump(m,m));\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    
    @Test @Ignore // FIXME - not working yet
    public void testIdentity() {
        helpTCX("tt.TestJava","package tt;  import java.util.function.Function;\n"
                                +"public class TestJava { \n"
                                
                                +"  //@ public normal_behavior\n"
                                +"  //@   ensures \\result == i;\n"
                                +"  //@ pure\n"
                                +"  public static Integer m1(Integer i) {\n"
                                +"    Function<Integer,Integer> f = Function.<Integer>identity();\n"
                                +"    return f.apply(i);\n"
                                +"  }\n"
                                                
                                +"}"
                                );
                    }

    @Test @Ignore // FIXME - not working yet
    public void testIdentity2() {
        helpTCX("tt.TestJava","package tt; import java.util.function.Function;\n"
                                +"public class TestJava { \n"
                                
                                +"  //@ public normal_behavior\n"
                                +"  //@   ensures \\result == i;\n"
                                +"  //@ pure\n"
                                +"  public static <T> T m1(T i) {\n"
                                +"    Function<T,T> f = Function.<T>identity();\n"
                                +"    return f.apply(i);\n"
                                +"  }\n"
                                                
                                +"}"
                                );
                    }

    @Test
    public void testIdentity3() {
        helpTCX("tt.TestJava","package tt;  import java.util.function.Function;\n"
                                +"public class TestJava { \n"
                                
                                +"  public /*@ immutable */ static interface Identity<T> extends Fun<T,T> {\n"
                                +"  //@   public model_program {\n"
                                +"  //@      return t;\n"
                                +"  //@    }\n"
                                +"  //@ pure function\n"
                                +"  public T apply(T t);\n"
                                +"  }\n"

                                +"  static /*@ immutable */ public interface Fun<T,R> {\n"
                                +"     //@ public normal_behavior ensures true; pure function\n"
                                +"     static <T> Identity<T> identity() { return null; }\n"
                                +"  }\n"
                                
                                +"  //@ public normal_behavior\n"  // Line 14
                                +"  //@   ensures \\result == i;\n"
                                +"  //@ pure\n"
                                +"  public static Integer m1(Integer i) {\n"
                                +"    Identity<Integer> f = Fun.<Integer>identity();\n"
                                +"    return f.apply(i);\n"
                                +"  }\n"
                                                
                                +"}"
                                );
                    }

    @Test
    public void testIdentity4() {
        helpTCX("tt.TestJava","package tt;  import java.util.function.Function;\n"
                                +"public class TestJava { \n"
                                
                                +"  public /*@ immutable */ static interface Identity<T> extends Fun<T,T> {\n"
                                +"  //@   public normal_behavior \n"
                                +"  //@      ensures \\result == t;\n"
                                +"  //@ pure function\n"
                                +"  public T apply(T t);\n"
                                +"  }\n"

                                +"  static /*@ immutable */ public interface Fun<T,R> {\n"
                                +"     //@ public normal_behavior ensures true; pure function\n"
                                +"     static <T> Identity<T> identity() { return null; }\n"
                                +"  }\n"
                                
                                +"  //@ public normal_behavior\n"  // Line 14
                                +"  //@   ensures \\result == i;\n"
                                +"  //@ pure\n"
                                +"  public static Integer m1(Integer i) {\n"
                                +"    Identity<Integer> f = Fun.<Integer>identity();\n"
                                +"    return f.apply(i);\n"
                                +"  }\n"
                                                
                                +"}"
                                );
                    }

    @Test
    public void testIterable4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public static class MMM {\n"
                +"    public boolean i = false;\n"
                +"    //@ public normal_behavior assignable i; ensures i == !\\old(i) ;\n"
                +"    public void bump() { i = !i; }\n"
                +"  }\n"
                
                +"  //@ requires a != null;\n"
                +"  public void m1(Iterable<@org.jmlspecs.annotation.NonNull MMM> a) {\n"  // NonNull should shut off the error message
                +"    a.forEach(MMM::bump);\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    @Test
    public void testMethodReference() {
//        main.addOptions("-show","-method=m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"@org.jmlspecs.annotation.CodeBigintMath public class TestJava { \n"
                
                +"  public int field;\n"
                +"  \n"
                
                +"    //@ public normal_behavior assignable field; ensures \\result == i + 1 && field == i ;\n"
                +"    public Integer bump(Integer i) { field = i; return i+1; }\n"
                +"    //@ public normal_behavior assignable field; ensures \\result == i + 1 ;\n"
                +"    public Integer bump2(Integer i) {  return i+1; }\n"
                
                +"  //@ requires j < 1000 && j > -1000;\n"
                +"  //@ assignable field;\n"
                +"  public void m1(java.util.function.BiFunction<TestJava,Integer,Integer> a, int j) {\n"
                +"   java.util.function.BiFunction<TestJava,Integer,Integer>  b = a;\n"
                +"    int k = (int)b.apply(this,(Integer)(j+100));\n"
                +"    assert k == j + 101 && field == j + 100;\n"
                +"  }\n"
                                
                +"  //@ assignable field;\n"
                +"  public void m2() {\n"
                +"    m1(TestJava::bump, 200);\n"
                +"    //@ assert field == 300;\n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test  // FIXME - using references or lambdas in these contexts is not Java
    public void testEquality() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                                
                +"  //@ public exceptional_behavior requires true;\n"
                +"  public static void m() {\n"
                +"    //@ ghost boolean b = RuntimeException::new == RuntimeException::new;\n"
                +"    //@ assert b;\n"
                +"    //@ set b = RuntimeException::new != null;\n"
                +"    //@ assert b;\n"
                +"    //@ set b = null != RuntimeException::new;\n"
                +"    //@ assert b;\n"
                +"    //@ set b = null != (x -> x);\n"
                +"    //@ assert b;\n"
                +"  }\n"
                +"}"
                );
    	
    }
    
    @Test
    public void testConstructor() {
//    	main.addOptions("-show","-method=m");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  @FunctionalInterface\n"
                +"  public static interface ExFactory {\n"
                +"    //@ public normal_behavior\n"
                +"    //@   ensures \\result instanceof NullPointerException;\n"
                +"    public RuntimeException create();\n"
                +"  }\n"

                +"  public ExFactory exx;\n"
                +"  \n"
                
                +"  //@ public normal_behavior\n"
                +"  //@ ensures exx == ex;\n"
                +"  public TestJava(ExFactory ex) {\n"
                +"     exx = ex;\n"
                +"  }\n"
                                
                +"  //@ public normal_behavior\n"
                +"  //@ ensures exx == RuntimeException::new;\n"
                +"  public TestJava() {\n"
                +"     exx = RuntimeException::new ;\n"
                +"  }\n"
                                
                +"  //@ public normal_behavior\n"
                +"  //@ assignable exx;\n"
                +"  //@ ensures exx == ex;\n"
                +"  public void set(ExFactory ex) {\n"
                +"     exx = ex;\n"
                +"  }\n"
                                
                +"  //@ public normal_behavior\n"
                +"  //@ assignable exx;\n"
                +"  //@ ensures exx == NullPointerException::new;\n"
                +"  public void set() {\n"
                +"     exx = NullPointerException::new ;\n"
                +"  }\n"
                
				+"  //@ public exceptional_behavior requires true; signals_only NullPointerException;\n"
				+"  public static void m() {\n"
				+"    TestJava t = new TestJava(NullPointerException::new);\n"
				+"    t.set(NullPointerException::new);\n"
				+"    throw t.exx.create();\n"
				+"  }\n"

				+"  //@ public exceptional_behavior requires true; signals_only NullPointerException;\n"
				+"  public static void mm() {\n"
				+"    TestJava t = new TestJava(NullPointerException::new);\n"
				+"    t.set();\n"
				+"    throw t.exx.create();\n"
				+"  }\n"
                
                +"}"
                );
    }
    
    
    @Test
    public void testConstructor2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  @FunctionalInterface\n"
                +"  public static interface ExFactory {\n"
                +"    //@ public normal_behavior\n"
                +"    //@   ensures \\result instanceof NullPointerException;\n"
                +"    public RuntimeException create();\n"
                +"  }\n"

                +"  public ExFactory exx;\n"
                +"  \n"
                
                +"  //@ public normal_behavior\n"
                +"  //@ ensures exx == NullPointerException::new;\n"
                +"  public TestJava() {\n"
                +"     exx = NullPointerException::new ;\n"
                +"  }\n"
                                
                +"  //@ public exceptional_behavior requires true; signals_only ArithmeticException;\n"
                +"  public static void m() {\n"
                +"    TestJava t = new TestJava();\n"
                +"    throw t.exx.create();\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (ExceptionList) in method m",5
                ,"/tt/TestJava.java:16: warning: Associated declaration",50
                );
    }
    
    @Test
    public void testCast() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  @FunctionalInterface\n"
                +"  public static interface PureSupplier<T> extends java.util.function.Supplier<T> {\n"
                +"    //@ also public normal_behavior\n"
                +"    //@   requires true;\n"
                +"    //@ pure\n"
                +"    @Override public T get();\n"
                +"  }\n"

                +"  //@ public behavior requires true; pure\n"   // Line 10
                +"  public static /*@ nullable */ Boolean m(java.util.function.Supplier<Boolean> s) {\n"
                +"      return s.get();\n"
                +"  }\n"
                
                +"  //@ public normal_behavior requires true; pure\n"
                +"  public static boolean mm(PureSupplier<Boolean> s) {\n"
                +"      return s.get();\n"
                +"  }\n"

                +"  //@ public normal_behavior requires true; pure\n"
                +"  public static boolean  mmm(/*@ {java.util.function.Supplier.Pure<Boolean>}*/ java.util.function.Supplier<Boolean> s) {\n"
                +"      return s.get();\n"   // Line 20
                +"  }\n"
                +"  //@ public normal_behavior requires true; pure\n"
                +"  public static boolean  mmmm(/*@ {java.util.function.Supplier.PureNonNull<Boolean>}*/ java.util.function.Supplier<Boolean> s) {\n"
                +"      return s.get();\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assignable) in method m:  \\everything",19
                ,"/tt/TestJava.java:10: warning: Associated declaration",14
                ,"/tt/TestJava.java:20: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method mmm",7
                
                );
    }
    
    @Test
    public void testLambda() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ public model_program { return x -> x; }\n"
                +"  public static java.util.function.Function<Integer,Integer> m() { return x -> x; }\n"
                +"  }\n"
                );
    }
    

}
