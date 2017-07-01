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
        //main.addOptions("-show","-method=m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public static class MMM {\n"
                +"    public int i ;\n"
                +"    public void bump() { i++; }\n"
                +"  }\n"
                
                +"  public void m1(Iterable<MMM> a) {\n"
                +"    a.forEach(MMM::bump);\n"
                +"  }\n"
                                
                +"}"
                // FIXME - the column location is wrong - it is not clear that the possible null value is an element of the iterable, with the element being the receiver of the bump call in the foreach loop
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",0
                );
    }
    
    @Test
    public void testIterable1b() {
        //main.addOptions("-show","-method=m1");
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
                
                +"  public void m1(/*@ non_null*/ Iterable<MMM> a) {\n"  // We do not know that each element returned by the iterable is non-null
                +"    a.forEach(m->m.bump());\n"
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",19
                );
    }
    
    @Test
    public void testIterable2b() {
        main.addOptions("-show","-method=m1");
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
        main.addOptions("-show","-method=m1");
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
        //main.addOptions("-show","-method=m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public static class MMM {\n"
                +"    public boolean i = false;\n"
                +"    //@ public normal_behavior assignable i; ensures i == !\\old(i) ;\n"
                +"    public void bump() { i = !i; }\n"
                +"  }\n"
                
                +"  //@ requires a != null;\n"
                +"  public void m1(Iterable<@org.jmlspecs.annotation.NonNull MMM> a) {\n"
                +"    a.forEach(MMM::bump);\n"
                +"  }\n"
                                
                +"}"
                // FIXME - we would like the NonNull annotation to tell JML that each iterate is non null.
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",11
                );
    }
    

}
