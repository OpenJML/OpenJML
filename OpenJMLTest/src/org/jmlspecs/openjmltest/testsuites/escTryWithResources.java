package org.jmlspecs.openjmltest.testsuites;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escTryWithResources extends EscBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
    }

    // -----------------------------------------------------------------------
    // Traditional declaration-style try-with-resources (moved from escall3)
    // -----------------------------------------------------------------------

    // If RR() throws an exception, mmm exits exceptionally
    @Test public void testTryResources() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1;  }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR r = new RR()){
                       flag = 2;
                       //@ assert TestJava.flag == 2;
                    }
                    //@ assert TestJava.flag == 1;
                  }
                }
                """
                );
    }

    // If RR() throws an exception, mmm exits exceptionally
    // If close throws an exception, then mmm exits exceptionally and flag is not tested
    @Test public void testTryResources1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR r = new RR()){
                       flag = 2;
                       //@ assert TestJava.flag == 2;
                    }
                    //@ assert TestJava.flag == 1;
                  }
                }
                """
                );
    }

    // If RR() throws an exception, flag == 0
    // If close exits normally, flag == 1
    // If close throws an exception, flag == 10
    @Test public void testTryResources1x() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       /*@ pure */ public RR(){}
                       //@ also
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 1;
                       //@ signals (Exception e) TestJava.flag == 10;
                       public void close() { TestJava.flag = 1; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() {
                    //@ assert TestJava.flag == 0;
                    try {
                    try (RR r = new RR()){
                       flag = 2;
                       //@ assert TestJava.flag == 2;
                    }
                    } catch (Exception eee) {
                    //@ assert (\\lbl FLAG TestJava.flag) == 0 || TestJava.flag == 1|| TestJava.flag == 10;
                    }
                  }
                }
                """
                );
    }

    // If RR() throws an exception, mmm exits exceptionally
    @Test public void testTryResources1a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 1;
                       //@ signals (Exception e) TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR r = new RR()){
                       flag = 2;
                       //@ assert TestJava.flag == 2;
                    }
                    //@ assert TestJava.flag == 1;
                  }
                }
                """
                );
    }

    // Checks that close calls execute in reverse order
    @Test public void testTryResources2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1;}
                    }
                    public static class RR2 implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 2;
                       public void close() { TestJava.flag = 2; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR2 r = new RR2(); RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                    }
                    //@ assert TestJava.flag == 2;
                  }
                }
                """
                );
    }

    // Checks the class of the resulting exception when try body and close calls throw exceptions
    @Test public void testTryResources2b() {
        addOptions("-checkFeasibility=assert","-defaults=constructor:pure");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static class EE extends Exception {  /*@ public normal_behavior ensures true; */public EE() {}}
                    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}
                    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}
                    public static class EE3 extends EE {/*@ public normal_behavior ensures true; */public EE3() {}}
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       /*@ public normal_behavior ensures true; */ public RR() { }
                       //@ also public exceptional_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ signals_only EE1;
                       //@ signals (Exception e) TestJava.flag == 1;
                       public void close() throws EE { TestJava.flag = 1; throw new EE1(); }
                    }
                    public static class RR2 implements AutoCloseable {
                       /*@ public normal_behavior ensures true; */ public RR2() { }
                       //@ also public exceptional_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ signals_only EE2;
                       //@ signals (Exception e) TestJava.flag == 2;
                       public void close() throws EE { TestJava.flag = 2; throw new EE2(); }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm(boolean b) {
                    //@ assert TestJava.flag == 0;
                    try {
                      if (b || !b) try (RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                       throw new EE3();
                      }
                      //@ assert TestJava.flag == 1;
                    } catch (EE e) {
                      //@ assert TestJava.flag == 1;
                       //@ assert e instanceof EE3 ;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:34: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.mmm(boolean)",11
                );
    }

    // Checks the class of the resulting exception when try body and close calls throw exceptions
    @Test public void testTryResources2c() {
        addOptions("-checkFeasibility=assert","-defaults=constructor:pure");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static class EE extends RuntimeException {  /*@ public normal_behavior ensures true; */public EE() {}}
                    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}
                    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}
                    public static class EE3 extends EE {/*@ public normal_behavior ensures true; */public EE3() {}}
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       /*@ public normal_behavior ensures true; */ public RR() { }
                       //@ also public exceptional_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ signals_only EE1;
                       //@ signals (Exception e) TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; throw new EE1(); }
                    }
                    public static class RR2 implements AutoCloseable {
                       /*@ public normal_behavior ensures true; */ public RR2() { }
                       //@ also public exceptional_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ signals_only EE2;
                       //@ signals (Exception e) TestJava.flag == 2;
                       public void close() { TestJava.flag = 2; throw new EE2(); }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm(boolean b) {
                    //@ assert TestJava.flag == 0;
                    try {
                      if (b || !b) try (RR2 r = new RR2(); RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                       throw new EE3();
                      }
                      //@ assert TestJava.flag == 2;
                    } catch (EE1 | EE2 | EE3 e) {
                       //@ assert e instanceof EE3 ;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:34: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.mmm(boolean)",11
                );
    }

    // Checks the class of the resulting exception when close calls throw exceptions, but not the try body
    @Test public void testTryResources2a() {
        addOptions("--check-feasibility=assert","--defaults=constructor:pure");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public static class EE extends Exception {  /*@ public normal_behavior ensures true; */public EE() {}}
                    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}
                    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@
                       /*@ public normal_behavior ensures true; */ public RR() { }
                       //@ also public exceptional_behavior
                       //@ assignable TestJava.flag,this.autocloseableContent;
                       //@ signals_only EE1;
                       //@ signals (Exception e) TestJava.flag == 1;
                       public void close() throws EE1 { TestJava.flag = 1; throw new EE1(); }
                    }
                    public static class RR2 implements AutoCloseable {
                       //@
                       /*@ public normal_behavior ensures true; */ public RR2() { }
                       //@ also public exceptional_behavior
                       //@ assignable TestJava.flag,this.autocloseableContent;
                       //@ signals_only EE2;
                       //@ signals (Exception e) TestJava.flag == 2;
                       public void close() throws EE2 { TestJava.flag = 2; throw new EE2(); }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() throws EE {
                    //@ assert TestJava.flag == 0;
                    try {
                      try (RR2 r = new RR2(); RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                      }
                      //@ assert TestJava.flag == 2;
                    } catch (EE e) {
                       //@ assert TestJava.flag == 2;
                       //@ assert e instanceof EE1;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:34: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.mmm()",11
                );
    }

    // Check that finally block of try encloses declarations and calls to close
    @Test public void testTryResources3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1;  }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                    } finally {
                      flag = 2;    }
                    //@ assert TestJava.flag == 2;
                  }
                }
                """
                );
    }

    // If RR() throws an exception, then catch block will execute
    @Test public void testTryResources4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1;  }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() {
                    boolean normal = true;
                    //@ assert TestJava.flag == 0;
                    try (RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                    } catch (Exception e) {
                      flag = 2;      normal = false;    }
                    //@ assert normal ==> flag == 1;
                    //@ assert !normal ==> flag == 2;
                  }
                }
                """
                );
    }

    @Test public void testTryResources4a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1;  }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                       throw new Exception();
                    } catch (Exception e) {
                      flag = 2;
                    }
                    //@ assert TestJava.flag == 2;
                  }
                }
                """
                );
    }

    @Test public void testTryResources4b() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1;  }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                       throw new Exception();
                    } catch (Exception e) {
                      flag = 2;
                    }
                    //@ assert TestJava.flag == 2;
                  }
                }
                """
                );
    }

    // No resource - executes the catch block
    @Test public void testTryResources4c() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1;  }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() {
                    //@ assert TestJava.flag == 0;
                    try {
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                       throw new Exception();
                    } catch (Exception e) {
                      flag = 2;
                    }
                    //@ assert TestJava.flag == 2;
                  }
                }
                """
                );
    }

    // Checks that the outer finally block is last to execute
    @Test public void testTryResources5() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1;  }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() {
                    //@ assert TestJava.flag == 0;
                    try (RR rr = new RR()){
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                    } catch (Exception e) {
                      flag = 2;    } finally {
                      flag = 5;    }
                    //@ assert TestJava.flag == 5;
                  }
                }
                """
                );
    }

    // -----------------------------------------------------------------------
    // Java 9+ expression resources -- flag-based verification with RR/RR2
    // These use the same pattern as the declaration tests above but pass an
    // already-declared variable as the resource: try (r) or try (r2; r).
    // -----------------------------------------------------------------------

    // Single variable resource: close() is called after the body.
    @Test public void testTryResourcesIdentifierSingle() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() {
                    RR r = new RR();
                    //@ assert TestJava.flag == 0;
                    try (r) {
                       flag = 2;
                       //@ assert TestJava.flag == 2;
                    }
                    //@ assert TestJava.flag == 1;
                  }
                }
                """
                );
    }

    // Two variable resources listed in one try: close() called in reverse order.
    @Test public void testTryResourcesIdentifierMultiple() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 1;
                       public void close() { TestJava.flag = 1; }
                    }
                    public static class RR2 implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 2;
                       public void close() { TestJava.flag = 2; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() {
                    RR2 r2 = new RR2();
                    RR r = new RR();
                    //@ assert TestJava.flag == 0;
                    try (r2; r) {
                       flag = 3;
                       //@ assert TestJava.flag == 3;
                    }
                    //@ assert TestJava.flag == 2;
                  }
                }
                """
                );
    }

    // Two identifier resources; the second (first to close) throws.
    // Confirms the first resource (second to close) is still closed.
    // In try(r2; r): r closes first (throws), r2 closes second (sets flag=2).
    @Test public void testTryResourcesIdentifierSecondCloseThrows() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    static public int flag = 0;
                    public static class RR implements AutoCloseable {
                       //@ also public exceptional_behavior
                       //@ assignable this.autocloseableContent;
                       //@ signals_only RuntimeException;
                       public void close() { throw new RuntimeException(); }
                    }
                    public static class RR2 implements AutoCloseable {
                       //@ also public normal_behavior
                       //@ assignable TestJava.flag, this.autocloseableContent;
                       //@ ensures TestJava.flag == 2;
                       public void close() { TestJava.flag = 2; }
                    }
                  //@ requires flag == 0;
                  //@ assignable flag;
                  public void mmm() {
                    RR r = new RR();
                    RR2 r2 = new RR2();
                    try {
                      try (r2; r) {
                         flag = 3;
                         //@ assert TestJava.flag == 3;
                      }
                    } catch (Exception e) {
                      //@ assert TestJava.flag == 2;
                    }
                  }
                }
                """
                );
    }

    // -----------------------------------------------------------------------
    // Java 9+ expression resources (Bug A from PR #951):
    //   try (existingVar) { ... }
    //   In dev-21 crashes: JCIdent cannot be cast to JCVariableDecl
    // -----------------------------------------------------------------------

    @Test public void testTryResourcesExpressionResource() {
        helpEsc("tt.A", """
                package tt;
                import java.io.*;
                public class A {
                    public void process(/*@ non_null */ BufferedReader br) throws IOException {
                        try (br) {
                            br.readLine();
                        }
                    }
                }
                """);
    }

    @Test public void testTryResourcesMultipleExpressionResources() {
        helpEsc("tt.A", """
                package tt;
                import java.io.*;
                public class A {
                    //@ requires \\invariant_for(in);
                    public void copy(/*@ non_null */ InputStream in,
                                    /*@ non_null */ OutputStream out) throws IOException {
                        try (in; out) {
                            out.write(in.read());
                        }
                    }
                }
                """);
    }

    @Test public void testTryResourcesExpressionResourceConcrete() {
        helpEsc("tt.A", """
                package tt;
                import java.io.*;
                public class A {
                    public void use(/*@ non_null */ InputStream in) throws IOException {
                        try (in) {
                            in.read();
                        }
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    // Generic-bounded resource types (Bug B from PR #951):
    //   try (R r = expr) where R extends Closeable
    //   In dev-21 crashes: TypeVariableSymbol cannot be cast to ClassSymbol
    // -----------------------------------------------------------------------

    @Test public void testTryResourcesGenericCloseable() {
        helpEsc("tt.A", """
                package tt;
                import java.io.*;
                public class A {
                    public static <R extends Closeable> void use(/*@ non_null */ R resource)
                            throws IOException {
                        try (R r = resource) {
                            r.toString();
                        }
                    }
                }
                """);
    }

    @Test public void testTryResourcesGenericAutoCloseable() {
        helpEsc("tt.A", """
                package tt;
                public class A {
                    public static <R extends AutoCloseable> void use(/*@ non_null */ R resource)
                            throws Exception {
                        try (R r = resource) {
                            r.toString();
                        }
                    }
                }
                """);
    }

    @Test public void testTryResourcesGenericMultipleTypeParams() {
        helpEsc("tt.A", """
                package tt;
                import java.io.*;
                public class A {
                    public static <T, R extends Closeable> void process(T data,
                            /*@ non_null */ R resource) throws IOException {
                        try (R r = resource) {
                            r.toString();
                        }
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    // Combined Bug A + Bug B: expression resource with generic type
    // -----------------------------------------------------------------------

    @Test public void testTryResourcesExpressionResourceGenericType() {
        helpEsc("tt.A", """
                package tt;
                import java.io.*;
                public class A {
                    public static <R extends AutoCloseable> void use(/*@ non_null */ R resource)
                            throws Exception {
                        try (resource) {
                            resource.toString();
                        }
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    // TypeVar resolution for signals_only: verifies that close() is resolved
    // to the most specific bound, preserving its declared throws clause.
    // With Closeable as the bound, close() declares only IOException.
    // If the resolver falls back to AutoCloseable, close() declares Exception,
    // and signals_only IOException would be incorrectly flagged as a violation.
    // -----------------------------------------------------------------------

    /** Chained type variables: R extends S, S extends Closeable.
     *  The resolver walks R -> S -> Closeable, finding close() throws IOException. */
    @Test public void testTryResourcesChainedTypeVar() {
        helpEsc("tt.A", """
                package tt;
                import java.io.*;
                public class A {
                    //@ requires resource != null;
                    public static <S extends Closeable, R extends S> void use(R resource)
                            throws IOException {
                        try (resource) {
                            var r = resource;
                        }
                    }
                }
                """);
    }

    /** Intersection bound: R extends Closeable & Serializable.
     *  Closeable is the most specific AutoCloseable component, so
     *  close() is resolved as throwing IOException. */
    @Test public void testTryResourcesIntersectionBoundCloseable() {
        helpEsc("tt.A", """
                package tt;
                import java.io.*;
                public class A {
                    //@ requires resource != null;
                    public static <R extends Closeable & Serializable> void use(R resource)
                            throws IOException {
                        try (resource) {
                            var r = resource;
                        }
                    }
                }
                """);
    }

    /** Intersection bound with a concrete class: R extends InputStream & Serializable.
     *  InputStream extends Closeable, so close() throws IOException -- more specific
     *  than if we had fallen back to AutoCloseable. */
    @Test public void testTryResourcesIntersectionBoundConcreteClass() {
        helpEsc("tt.A", """
                package tt;
                import java.io.*;
                public class A {
                    //@ requires resource != null;
                    //@ signals_only IOException, RuntimeException;
                    public static <R extends InputStream & Serializable> void use(R resource)
                            throws IOException {
                        try (resource) {
                            resource.read();
                        }
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    // Additional scenarios from PR#951
    // -----------------------------------------------------------------------

    /** Field access expression resource: try (this.stream) */
    @Test public void testTryResourcesFieldAccess() {
        helpEsc("tt.A", """
                package tt;
                import java.io.*;
                public class A {
                    final InputStream stream;
                    A(InputStream s) throws IOException { this.stream = s; }
                    void process() throws IOException {
                        try (this.stream) {
                            stream.read();
                        }
                    }
                }
                """);
    }

    /** Mixed declaration and expression resources in one try statement. */
    @Test public void testTryResourcesMixed() {
        helpEsc("tt.A", """
                package tt;
                import java.io.*;
                public class A {
                    void process(/*@ non_null */ InputStream existing) throws IOException {
                        try (existing;
                             BufferedReader br = new BufferedReader(new InputStreamReader(existing))) {
                            ;
                        }
                    }
                }
                """);
    }

    /** Mixed expression and generic declaration resources. */
    @Test public void testTryResourcesMixedGeneric() {
        helpEsc("tt.A", """
                package tt;
                import java.io.*;
                public class A {
                    static <R extends Closeable> void process(/*@ non_null */ R resource,
                            /*@ non_null */ InputStream extra) throws IOException {
                        try (R r = resource;
                             extra) {
                            ;
                        }
                    }
                }
                """);
    }

    /** TWR nested inside a try-catch block. */
    @Test public void testTryResourcesNestedInTryCatch() {
        helpEsc("tt.A", """
                package tt;
                import java.io.*;
                public class A {
                    void process(/*@ non_null */ InputStream in) {
                        try {
                            try (in) {
                                in.read();
                            }
                        } catch (IOException e) {
                        }
                    }
                }
                """);
    }

    /** Nested try-with-resources statements. */
    @Test public void testTryResourcesNestedTwr() {
        helpEsc("tt.A", """
                package tt;
                import java.io.*;
                public class A {
                    void process(/*@ non_null */ String path) throws IOException {
                        try (FileInputStream fis = new FileInputStream(path)) {
                            try (BufferedInputStream bis = new BufferedInputStream(fis)) {
                                bis.read();
                            }
                        }
                    }
                }
                """);
    }
}
