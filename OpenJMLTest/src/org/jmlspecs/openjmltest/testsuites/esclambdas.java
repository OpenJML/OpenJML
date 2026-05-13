package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

import java.util.function.Function;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class esclambdas extends EscBase {
    
    @Test
    public void testIterable1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static class MMM {
                    public int i ;
                    //@ assignable i;
                    public void bump() { if (i>0) i--; i++; }
                  }
                  //@ assigns \\everything;
                  public void m1(Iterable<@org.jmlspecs.annotation.Nullable MMM> a) {
                    //@ loop_modifies \\everything;
                    //@ inlined_loop;
                    a.forEach(MMM::bump);
                  }
                }
                """
                ,"$SPECS/java/lang/Iterable.jml:51: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",40
                );
    }
    
    @Test
    public void testIterable1a() {
        addOptions("--code-math=java");
        helpEsc("tt.TestJava",
                """
                package tt;
                //@ non_null_by_default
                public class TestJava {
                
                  public static class MMM {
                    public int i;
                    //@ writes i;
                    public void bump() { i++; }
                  }
                
                  // @ assignable a.values[*].i;
                  public void m1(Iterable<MMM> a) {
                    // @ loop_invariant a.values == \\old(a.values);
                    //@ loop_assigns \\everything;
                    for (MMM t: a) t.bump();
                  }
                }
                """
                ); // FIXME - no way to write the frame condition for m1
    }
    
    @Test
    public void testIterable1b() {
        addOptions("--code-math=java");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                
                  public static class MMM {
                    public int i;
                    //@ writes i;
                    public void bump() { i++; }
                  }
                
                  public void m1(Iterable<@org.jmlspecs.annotation.NonNull MMM> a) {
                    //@ loop_invariant a.values == \\old(a.values);
                    //@ loop_assigns \\everything;
                    //@ inlined_loop;
                    a.forEach(MMM::bump);
                  }
                }
                """
                ); // FIXME - no way to write the frame condition for m1
    }
    
    @Test
    public void testIterable2() {
    	addOptions("--code-math=java"); // Just to avoid overflow errors
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {

                  public static class MMM {
                    public int i ;
                    //@ writes i;
                    public void bump() { i++; }
                  }
                  public void m1(/*@ non_null*/ Iterable<@org.jmlspecs.annotation.Nullable MMM> a) {
                    //@ loop_invariant a.values == \\old(a.values);
                    //@ loop_assigns \\everything;
                    //@ inlined_loop;
                    a.forEach(m->m.bump());
                  }
                }
                """
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",19
                );
    }
    
    @Test
    public void testIterable2b() {
    	addOptions("--code-math=java"); // Just to avoid overflow errors
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {

                  public static class MMM {
                    public int i ;
                    /*@ assignable i; */ public void bump() { i++; }
                  }
                  public void m1(/*@ non_null*/ Iterable<@org.jmlspecs.annotation.NonNull MMM> a) {
                    //@ loop_assigns \\everything;
                    //@ inlined_loop;
                    a.forEach(m->m.bump());
                  }
                }
                """
                );
    }
    
    @Test
    public void testIterable3() {
        addOptions("--code-math=java","--spec-math=java");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int j;
                  /*@ pure */ public int k() { return 7; };
                  public static class MMM {
                    public int i ;
                  }
                  //@ assignable m1.i;
                  public void bump(MMM m1, MMM m2) {
                     m1.i += (j + m2.i + k());
                  }
                  //@ requires a.containsNull == false;
                  public void m1(/*@ non_null*/ Iterable</*@ non_null*/ MMM> a) {
                    //java.util.function.Consumer<MMM> action = (m->bump(m,m)); for (@org.jmlspecs.annotations.NonNull MMM t: a) action.accept(t);
                    //@ loop_assigns \\everything;
                    //@ inlined_loop;
                    a.forEach(m->bump(m,m));
                  }
                }
                """
                );
    }
    
    // FIXME - identity and identity2 need dynamic specs (f.ensures...)
    @Test
    public void testIdentity() {
        helpEsc("tt.TestJava",
                """
                package tt;import java.util.function.Function;
                public class TestJava {
                  //@ public normal_behavior
                  //@   ensures \\result == i;
                  //@ pure
                  public static Integer m1(Integer i) {
                    Function<Integer,Integer> f = Function.<Integer>identity();
                    return f.apply(i);
                  }
                }
                """
                );
    }

    @Test
    public void testIdentity2() {
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.function.Function;
                public class TestJava {
                  //@ public normal_behavior
                  //@   ensures \\result == i;
                  //@ pure
                  public static <T> T m1(T i) {
                    Function<T,T> f = Function.<T>identity();
                    return f.apply(i);
                  }
                }
                """
                );
    }

    @Test
    public void testIdentity3() {
        helpEsc("tt.TestJava",
                """
                package tt;  import java.util.function.Function;
                public class TestJava {
                  public /*@ immutable */ static interface Identity<T> extends Fun<T,T> {
                  //@   public model_program {
                  //@      return t;
                  //@    }
                  //@ pure
                  public T apply(T t);
                  }
                  static /*@ immutable */ public interface Fun<T,R> {
                     //@ public normal_behavior
                     //@   ensures true;
                     //@   spec_pure
                     static <T> Identity<T> identity() { return (x -> x); }
                  }
                  //@ public normal_behavior
                  //@   ensures \\result == i;
                  //@ pure
                  public static Integer m1(Integer i) {
                    Identity<Integer> f = Fun.<Integer>identity();
                    return f.apply(i);
                  }
                }
                """
                );
    }

    @Test
    public void testIdentity4() {
        helpEsc("tt.TestJava",
                """
                package tt;  import java.util.function.Function;
                public class TestJava {
                  public /*@ immutable */ static interface Identity<T> extends Fun<T,T> {
                  //@   public normal_behavior
                  //@      ensures \\result == t;
                  //@ pure
                  public T apply(T t);
                  }
                  static /*@ immutable */ public interface Fun<T,R> {
                     //@ public normal_behavior
                     //@   ensures true;
                     //@   spec_pure
                     static <T> Identity<T> identity() { return (x->x); }
                  }
                  //@ public normal_behavior
                  //@   ensures \\result == i;
                  //@ pure
                  public static Integer m1(Integer i) {
                    Identity<Integer> f = Fun.<Integer>identity();
                    return f.apply(i);
                  }
                }
                """
                );
    }

    @Test
    public void testIterable4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {

                  public static class MMM {
                    public boolean i = false;
                    //@ public normal_behavior
                    //@   assignable i;
                    //@   ensures i == !\\old(i) ;
                    public void bump() { i = !i; }
                  }
                  //@ requires a != null;
                  public void m1(Iterable<@org.jmlspecs.annotation.NonNull MMM> a) {
                    //@ loop_assigns \\everything;
                    //@ inlined_loop;
                    a.forEach(MMM::bump);
                  }
                }
                """
                );
    }
    
    @Test
    public void testMethodReference() {
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.function.*;
                @org.jmlspecs.annotation.CodeBigintMath public class TestJava {
                  public int field;
                  //@ requires j < 1000 && j > -1000;
                  //@ assignable field;
                  //@ ensures \\result == j+101;
                  //@ ensures field == j+100;
                  public int m1(/*@[FF]*/ BiFunction<TestJava,Integer,Integer> a, int j) {
                   final /*@[FF]*/ BiFunction<TestJava,Integer,Integer>  b = a;
                    return (int)b.apply(this,(Integer)(j+100));
                  }
                  /*@ @FunctionalInterface model public static interface FF extends BiFunction<TestJava,Integer,Integer> {
                        also assignable t.field; ensures t.field == n; ensures \\result == n+1;
                        non_null
                       Integer apply(TestJava t, Integer n);} */
                    //@ public normal_behavior
                    //@   assignable field;
                    //@   ensures \\result == i + 1 && field == i ;
                    public Integer bump(Integer i) { field = i; return i+1; }
                    //@ public normal_behavior
                    //@   assignable field;
                    //@   ensures \\result == i + 1 ;
                    public Integer bump2(Integer i) {  return i+1; }
                  //@ requires j < 1000 && j > -1000;
                  //@ assignable field;
                  public int m3(/*@[FF]*/ BiFunction<TestJava,Integer,Integer> a, int j) {
                    /*@[FF]*/ BiFunction<TestJava,Integer,Integer>  b = a;
                    return (int)b.apply(this,(Integer)(j+100));
                  }
                  //@ assignable field;
                  public void m2() {
                    m1(TestJava::bump, 200);
                    //@ assert field == 300;
                  }
                }
                """
                );
    }
    
    @Test
    public void testEquality() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ public normal_behavior
                  //@   requires true;
                  public static void m() {
                    //@ ghost boolean b;
                    //@ set b = (java.util.function.Supplier)RuntimeException::new == (java.util.function.Supplier<Throwable>)RuntimeException::new;
                    //@ assert b;
                    //@ set b = (java.util.function.Supplier)RuntimeException::new != null;
                    //@ assert b;
                    //@ set b = null != (java.util.function.Supplier)RuntimeException::new;
                    //@ assert b;
                    //@ set b = null != (java.util.function.Function)(x -> x);
                    //@ assert b;
                  }
                }
                """
                // FIXME: //@ set b = (java.util.function.Function<Object,Object>)java.util.function.Function::identity != (java.util.function.Function<Object,Object>)(x -> x);
                //        //@ assert b;
                );
    }
    
    @Test
    public void testReplacementType() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static class C {};
                  //@ model public static class R extends C {};
                  public /*@ nullable [R] */C field;
                  public void set( /*@[R]*/C f) { field = f; }
                  //@ public normal_behavior
                  //@   requires true;
                  public void m() {
                    //@ assert field == null || field instanceof R;
                  }
                }
                """
                );
    }

    @Test
    public void testReplacementType2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static class C {};
                  public static class R extends C {};
                  public /*@ nullable [R]*/C field;
                  public void set( /*@[R]*/C f) { field = f; }
                  //@ public normal_behavior
                  //@   requires true;
                  public void m() {
                    //@ assert field == null || field instanceof R;
                  }
                }
                """
                );
    }
    
    @Test
    public void testConstructor() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  @FunctionalInterface
                  public static interface ExFactory {
                    //@ public normal_behavior
                    //@   ensures \\result instanceof NullPointerException;
                    public RuntimeException create();
                  }
                  public ExFactory exx;

                  //@ public normal_behavior
                  //@ ensures exx == ex;
                  public TestJava(ExFactory ex) {
                     exx = ex;
                  }
                  //@ public normal_behavior
                  //@ ensures exx == (ExFactory)RuntimeException::new;
                  public TestJava() {
                     exx = RuntimeException::new ;
                  }
                  //@ public normal_behavior
                  //@ assignable exx;
                  //@ ensures exx == ex;
                  public void set(ExFactory ex) {
                     exx = ex;
                  }
                  //@ public normal_behavior
                  //@ assignable exx;
                  //@ ensures exx == (ExFactory)NullPointerException::new;
                  public void set() {
                     exx = NullPointerException::new ;
                  }
                  //@ public exceptional_behavior
                  //@   requires true;
                  //@   signals_only NullPointerException;
                  public static void m() {
                    TestJava t = new TestJava(NullPointerException::new);
                    t.set(NullPointerException::new);
                    throw t.exx.create();
                  }
                  //@ public exceptional_behavior
                  //@   requires true;
                  //@   signals_only NullPointerException;
                  public static void mm() {
                    TestJava t = new TestJava(NullPointerException::new);
                    t.set();
                    throw t.exx.create();
                  }
                }
                """
                );
    }
    
    
    @Test
    public void testConstructor2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  @FunctionalInterface
                  public static interface ExFactory {
                    //@ public normal_behavior
                    //@   ensures \\result instanceof NullPointerException;
                    public RuntimeException create();
                  }
                  public ExFactory exx;

                  //@ public normal_behavior
                  //@ ensures exx == (ExFactory)NullPointerException::new;
                  public TestJava() {
                     exx = NullPointerException::new ;
                  }
                  //@ public exceptional_behavior
                  //@   requires true;
                  //@   signals_only ArithmeticException;
                  public static void m() {
                    TestJava t = new TestJava();
                    throw t.exx.create();
                  }
                }
                """
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (ExceptionList) in method m",5
                ,"/tt/TestJava.java:18: verify: Associated declaration",9
                );
    }
    
    @Test
    public void testCast() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  @FunctionalInterface
                  public static interface PureSupplier<T> extends java.util.function.Supplier<T> {
                    //@ also public normal_behavior
                    //@   requires true;
                    //@ pure
                    @Override public T get();
                  }
                  //@ public behavior
                  //@   requires true;
                  //@   pure
                  public static /*@ nullable */ Boolean m(java.util.function.Supplier<Boolean> s) {
                      return s.get();
                  }
                  //@ public normal_behavior
                  //@   requires true;
                  //@   pure
                  public static boolean mm(PureSupplier<Boolean> s) {
                      return s.get();
                  }
                  //@ public normal_behavior
                  //@   requires true;
                  //@   pure
                  public static boolean  mmm(/*@ [java.util.function.Supplier.Pure<Boolean>]*/ java.util.function.Supplier<Boolean> s) {
                      return s.get();
                  }
                  //@ public normal_behavior
                  //@   requires true;
                  //@   pure
                  public static boolean  mmmm(/*@ [java.util.function.Supplier.PureNonNull<Boolean>]*/ java.util.function.Supplier<Boolean> s) {
                      return s.get();
                  }
                }
                """
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Assignable) in method m: \\everything",19
                ,"/tt/TestJava.java:12: verify: Associated declaration",9
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method mmm",19 // FIXME _ 15?
                );
    }
    
    @Test
    public void testCast1() {
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.function.Supplier;
                public class TestJava {
                  //@ public normal_behavior
                  //@   requires true;
                  //@   pure
                  public static boolean  mmm(/*@ [java.util.function.Supplier.Pure<Boolean>]*/ java.util.function.Supplier<Boolean> s) {
                      return s.get();
                  }
                  //@ public normal_behavior
                  //@   requires true;
                  //@   pure
                  public static boolean  mmmm(/*@ [Supplier.PureNonNull<Boolean>]*/ java.util.function.Supplier<Boolean> s) {
                      return s.get();
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method mmm",19 // FIXME _ 15?
                );
    }

    @Test
    public void testCast2() {
        helpEsc("tt.TestJava",
                """
                package tt; import static java.util.function.Supplier.*;
                public class TestJava {
                  //@ public normal_behavior
                  //@   requires true;
                  //@   pure
                  public static boolean  mmm(/*@ [Pure<Boolean>]*/ java.util.function.Supplier<Boolean> s) {
                      return s.get();
                  }
                  //@ public normal_behavior
                  //@   requires true;
                  //@   pure
                  public static boolean  mmmm(/*@ [PureNonNull<Boolean>]*/ java.util.function.Supplier<Boolean> s) {
                      return s.get();
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method mmm",19 // FIXME _ 15?
                );
    }
    
    @Test
    public void testCast3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  @FunctionalInterface
                  public static interface PureSupplier extends java.util.function.Supplier<Integer> {
                    //@ also public normal_behavior
                    //@   requires true;
                    //@ pure
                    @Override public Integer get();
                  }
                  //@ public behavior
                  //@   ensures true;
                  //@   pure
                  public static /*@[PureSupplier] */ java.util.function.Supplier<Integer> m() {
                      return /*@{PureSupplier}@*/ ()->1;
                  }
                  //@ public behavior
                  //@   ensures true;
                  //@   pure
                  public static /*@[PureSupplier]*/ java.util.function.Supplier<Integer> mm() {
                      return ()->1;
                  }
                }
                """
                );
    }
    
    @Test
    public void testLambda() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ public model_program { return x -> x; }
                  public static java.util.function.Function<Integer,Integer> m() { return x -> x; }
                  }
                """
                );
    }
    
    @Test @Ignore // has developped a timeout, so ignorig for now -- FIXME
    public void testBindLambda() {
        addOptions("--method=mm"); // Part of test
        addOptions("--code-math=bigint","--spec-math=bigint");  // Part of test
        // is this supposed to be nullableByDefault from the test harness -- FIXME
        helpEsc("tt.TestJava",
                """
                package tt;
                import java.util.function.Function;
                public class TestJava {
                      public Object ppp;

                  public void mm(Object ppp) {
                      boolean b = m(ppp, x->{return this.ppp;});
                       //@ assert b;  // Should be false
                  }
                  //@ inline
                  final public boolean m(Object aaa, /*@ non_null */ Function<Object,Object> f) {
                       Object a = aaa; return a != f.apply(null);
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method mm",12
                );
    }
    
    @Test
    public void testBindLambdaA() {
        addOptions("--method=mm");
        addOptions("--code-math=bigint","--spec-math=bigint");
        // is this supposed to be nullableByDefault from the test harness -- FIXME
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.function.Function;
                public class TestJava {
                      public Object ppp;
                  //@ requires ppp == this.ppp;
                  public void mm(Object ppp) {
                      boolean b = m(ppp, x->{return this.ppp;});
                       //@ assert b;
                  }
                  //@ inline
                  final public boolean m(Object aaa, /*@ non_null */ Function<Object,Object> f) {
                       Object a = aaa; return a == f.apply(null);  }
                  }
                """
                );
    }
    
    @Test
    public void testBindLambdaB() {
        addOptions("--method=mm");
        addOptions("--code-math=bigint","--spec-math=bigint");
        // nullableByDefault
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.function.Function;
                public class TestJava {
                      public Object ppp;
                  public void mm(Object ppp) {
                      boolean b = m(this.ppp, x->{return this.ppp;});
                       //@ assert b;
                  }
                  //@ inline
                  final public boolean m(Object aaa, /*@ non_null */ Function<Object,Object> f) {
                       Object a = aaa; return a == f.apply(null);  }
                  }
                """
                );  // No errors
    }
    
    @Test
    public void testBindLambdaC() {
        addOptions("--method=mm");
        addOptions("--code-math=bigint","--spec-math=bigint");
        // nullableByDefault
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.function.Function;
                public class TestJava {
                      public Object ppp;
                  public void mm(Object ppp) {
                      boolean b = m(this.ppp, x->{return x;});
                       //@ assert b;
                  }
                  //@ inline
                  final public boolean m(Object aaa, /*@ non_null */ Function<Object,Object> f) {
                       Object a = aaa; return a == f.apply(this.ppp);  }
                  }
                """
                );  // No errors
    }
    
    @Test
    public void testBindLambdaD() {
        addOptions("--method=mm");
        addOptions("--code-math=bigint","--spec-math=bigint");
        // nullableByDefault
        helpEsc("tt.TestJava",
                """
                package tt;  import java.util.function.Function;
                public class TestJava {
                      public Object ppp;
                  public void mm(Object ppp) {
                      boolean b = m(this.ppp, x->x);
                       //@ assert b;
                  }
                  //@ inline
                  final public boolean m(Object aaa, /*@ non_null */ Function<Object,Object> f) {
                       Object a = aaa; return a == f.apply(this.ppp);  }
                  }
                """
                );
    }
    
    @Test
    public void testBindLambda2() {
        addOptions("--method=mm");
        addOptions("--code-math=bigint","--spec-math=bigint");
        helpEsc("tt.TestJava",
                """
                package tt;  import java.util.function.Function;
                /*@ non_null_by_default*/ public class TestJava {
                      public int a = 11;
                  //@ requires this.a == 11;
                  public void mm() {
                      int a = 9;
                      int b = a + m(a, this.a, x->{return x+a+this.a+100;});
                       //@ assert b == 9 + 7 + 11 + (11+9+11+100);
                  }
                  //@ inline
                  final public int m(int aa, int b, /*@ non_null */ Function<Integer,Integer> f) {
                       int a = 7; return a + b + f.apply(this.a);  }
                  }
                """
                );  // No errors
    }
    
    @Test
    public void testBindLambda21() {
        addOptions("--method=m");
        addOptions("--code-math=bigint","--spec-math=bigint");
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.function.Function;
                /*@ non_null_by_default*/ public class TestJava {
                      //@ model public static interface NNFunction<T,R> extends Function<T,R> { non_null R apply(non_null T t); }
                      public int a = 11;
                  //@ requires this.a == 11;
                  public void mm() {
                      int a = 9;
                      int b = a + m(a, this.a, x->{return x+a+this.a+100;});
                       //@ assert b == 9 + 7 + 11 + (11+9+11+100);
                  }
                  //@ requires f != null;
                  //@ inline
                  final public int m(int aa, int b, /*@[NNFunction<Integer,Integer>]*/ Function<Integer,Integer> f) {
                       int a = 7; return a + b + f.apply(this.a);  }
                  }
                """
                );  // No errors
    }
    
    @Test
    public void testBindLambdaByte() {
        addOptions("--code-math=bigint","--spec-math=bigint");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  private /*@ spec_public nullable */ Byte aaaaaaaaaaa = null;
                      //@ assignable this.aaaaaaaaaaa;
                      //@ ensures this.aaaaaaaaaaa != null;
                      //@ ensures this.aaaaaaaaaaa.byteValue() == aaaaaaaaaaa;
                  public void mm(byte aaaaaaaaaaa) {
                      //this.aaaaaaaaaaa = aaaaaaaaaaa;
                      set(()->this.aaaaaaaaaaa = aaaaaaaaaaa);
                  }
                  //@ public model static interface NoException extends Runnable { also public normal_behavior ensures true; void run(); }
                  //@ public normal_behavior
                  //@   requires true;
                  //@   { r.run(); }
                  //@   ensures true;
                  public void set(/*@[NoException] @*/ Runnable r) {
                       r.run();  }
                }
                """
                );  // No errors
    }
    
    @Test
    public void testBindLambdaInt() {
        addOptions("--code-math=bigint","--spec-math=bigint");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public /*@ nullable */ Integer aaaaaaaaaaa = null;
                      //@ assignable this.aaaaaaaaaaa;
                      //@ ensures this.aaaaaaaaaaa != null;
                      //@ ensures this.aaaaaaaaaaa.intValue() == aaaaaaaaaaa;
                  public void mm(int aaaaaaaaaaa) {
                      set(()->this.aaaaaaaaaaa = aaaaaaaaaaa);
                  }
                  //@ public behavior
                  //@   requires true;
                  //@   { r.run(); }
                  //@   ensures true;
                  public void set(Runnable r) {
                       r.run();  }
                }
                """
                );  // No errors
    }
}
