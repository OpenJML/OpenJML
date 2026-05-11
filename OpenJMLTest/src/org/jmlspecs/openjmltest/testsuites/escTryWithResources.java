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
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;  }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR r = new RR()){\n"
                +"       flag = 2; \n"
                +"       //@ assert TestJava.flag == 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 1;\n"
                +"  }\n"
                +"}"
                );
    }

    // If RR() throws an exception, mmm exits exceptionally
    // If close throws an exception, then mmm exits exceptionally and flag is not tested
    @Test public void testTryResources1() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR r = new RR()){\n"
                +"       flag = 2; \n"
                +"       //@ assert TestJava.flag == 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 1;\n"
                +"  }\n"
                +"}"
                );
    }

    // If RR() throws an exception, flag == 0
    // If close exits normally, flag == 1
    // If close throws an exception, flag == 10
    @Test public void testTryResources1x() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       /*@ pure */ public RR(){}\n"
                +"       //@ also\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 10;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try {\n"
                +"    try (RR r = new RR()){\n"
                +"       flag = 2; \n"
                +"       //@ assert TestJava.flag == 2;\n"
                +"    }\n"
                +"    } catch (Exception eee) { \n"
                +"    //@ assert (\\lbl FLAG TestJava.flag) == 0 || TestJava.flag == 1|| TestJava.flag == 10;\n"
                +"    }\n"
                +"  }\n"
                +"}"
                );
    }

    // If RR() throws an exception, mmm exits exceptionally
    @Test public void testTryResources1a() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR r = new RR()){\n"
                +"       flag = 2; \n"
                +"       //@ assert TestJava.flag == 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 1;\n"
                +"  }\n"
                +"}"
                );
    }

    // Checks that close calls execute in reverse order
    @Test public void testTryResources2() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;}\n"
                +"    }\n"
                +"    public static class RR2 implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 2;\n"
                +"       public void close() { TestJava.flag = 2; }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR2 r = new RR2(); RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2;\n"
                +"  }\n"
                +"}"
                );
    }

    // Checks the class of the resulting exception when try body and close calls throw exceptions
    @Test public void testTryResources2b() {
        addOptions("-checkFeasibility=assert","-defaults=constructor:pure");
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    public static class EE extends Exception {  /*@ public normal_behavior ensures true; */public EE() {}}\n"
                +"    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}\n"
                +"    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}\n"
                +"    public static class EE3 extends EE {/*@ public normal_behavior ensures true; */public EE3() {}}\n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       /*@ public normal_behavior ensures true; */ public RR() { }\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ signals_only EE1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 1;\n"
                +"       public void close() throws EE { TestJava.flag = 1; throw new EE1(); }\n"
                +"    }\n"
                +"    public static class RR2 implements AutoCloseable {\n"
                +"       /*@ public normal_behavior ensures true; */ public RR2() { }\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ signals_only EE2;\n"
                +"       //@ signals (Exception e) TestJava.flag == 2;\n"
                +"       public void close() throws EE { TestJava.flag = 2; throw new EE2(); }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm(boolean b) {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try {\n"
                +"      if (b || !b) try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new EE3();\n"
                +"      }\n"
                +"      //@ assert TestJava.flag == 1;\n"
                +"    } catch (EE e) {\n"
                +"      //@ assert TestJava.flag == 1;\n"
                +"       //@ assert e instanceof EE3 ;\n"
                +"    }\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:34: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.mmm(boolean)",11
                );
    }

    // Checks the class of the resulting exception when try body and close calls throw exceptions
    @Test public void testTryResources2c() {
        addOptions("-checkFeasibility=assert","-defaults=constructor:pure");
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    public static class EE extends RuntimeException {  /*@ public normal_behavior ensures true; */public EE() {}}\n"
                +"    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}\n"
                +"    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}\n"
                +"    public static class EE3 extends EE {/*@ public normal_behavior ensures true; */public EE3() {}}\n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       /*@ public normal_behavior ensures true; */ public RR() { }\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ signals_only EE1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; throw new EE1(); }\n"
                +"    }\n"
                +"    public static class RR2 implements AutoCloseable {\n"
                +"       /*@ public normal_behavior ensures true; */ public RR2() { }\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ signals_only EE2;\n"
                +"       //@ signals (Exception e) TestJava.flag == 2;\n"
                +"       public void close() { TestJava.flag = 2; throw new EE2(); }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm(boolean b) {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try {\n"
                +"      if (b || !b) try (RR2 r = new RR2(); RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new EE3();\n"
                +"      }\n"
                +"      //@ assert TestJava.flag == 2;\n"
                +"    } catch (EE1 | EE2 | EE3 e) {\n"
                +"       //@ assert e instanceof EE3 ;\n"
                +"    }\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:34: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.mmm(boolean)",11
                );
    }

    // Checks the class of the resulting exception when close calls throw exceptions, but not the try body
    @Test public void testTryResources2a() {
        addOptions("--check-feasibility=assert","--defaults=constructor:pure");
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    public static class EE extends Exception {  /*@ public normal_behavior ensures true; */public EE() {}}\n"
                +"    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}\n"
                +"    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}\n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ \n"
                +"       /*@ public normal_behavior ensures true; */ public RR() { }\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag,this.autocloseableContent;\n"
                +"       //@ signals_only EE1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 1;\n"
                +"       public void close() throws EE1 { TestJava.flag = 1; throw new EE1(); }\n"
                +"    }\n"
                +"    public static class RR2 implements AutoCloseable {\n"
                +"       //@ \n"
                +"       /*@ public normal_behavior ensures true; */ public RR2() { }\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag,this.autocloseableContent;\n"
                +"       //@ signals_only EE2;\n"
                +"       //@ signals (Exception e) TestJava.flag == 2;\n"
                +"       public void close() throws EE2 { TestJava.flag = 2; throw new EE2(); }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() throws EE {\n"
                +"    //@ assert TestJava.flag == 0;  \n"
                +"    try {\n"
                +"      try (RR2 r = new RR2(); RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"      }\n"
                +"      //@ assert TestJava.flag == 2;\n"
                +"    } catch (EE e) {\n"
                +"       //@ assert TestJava.flag == 2;\n"
                +"       //@ assert e instanceof EE1;\n"
                +"    }\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:34: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.mmm()",11
                );
    }

    // Check that finally block of try encloses declarations and calls to close
    @Test public void testTryResources3() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;  }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"    } finally {\n"
                +"      flag = 2;"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2;\n"
                +"  }\n"
                +"}"
                );
    }

    // If RR() throws an exception, then catch block will execute
    @Test public void testTryResources4() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;  }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    boolean normal = true;\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;"
                +"      normal = false;"
                +"    }\n"
                +"    //@ assert normal ==> flag == 1;\n"
                +"    //@ assert !normal ==> flag == 2;\n"
                +"  }\n"
                +"}"
                );
    }

    @Test public void testTryResources4a() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;  }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new Exception();\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2;\n"
                +"  }\n"
                +"}"
                );
    }

    @Test public void testTryResources4b() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;  }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new Exception();\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2;\n"
                +"  }\n"
                +"}"
                );
    }

    // No resource - executes the catch block
    @Test public void testTryResources4c() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;  }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try {\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new Exception();\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2; \n"
                +"  }\n"
                +"}"
                );
    }

    // Checks that the outer finally block is last to execute
    @Test public void testTryResources5() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;  }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;"
                +"    } finally {\n"
                +"      flag = 5;"
                +"    }\n"
                +"    //@ assert TestJava.flag == 5;\n"
                +"  }\n"
                +"}"
                );
    }

    // -----------------------------------------------------------------------
    // Java 9+ expression resources -- flag-based verification with RR/RR2
    // These use the same pattern as the declaration tests above but pass an
    // already-declared variable as the resource: try (r) or try (r2; r).
    // -----------------------------------------------------------------------

    // Single variable resource: close() is called after the body.
    @Test public void testTryResourcesIdentifierSingle() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    RR r = new RR();\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (r) {\n"
                +"       flag = 2;\n"
                +"       //@ assert TestJava.flag == 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 1;\n"
                +"  }\n"
                +"}"
                );
    }

    // Two variable resources listed in one try: close() called in reverse order.
    @Test public void testTryResourcesIdentifierMultiple() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                +"    public static class RR2 implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 2;\n"
                +"       public void close() { TestJava.flag = 2; }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    RR2 r2 = new RR2();\n"
                +"    RR r = new RR();\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (r2; r) {\n"
                +"       flag = 3;\n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2;\n"
                +"  }\n"
                +"}"
                );
    }

    // Two identifier resources; the second (first to close) throws.
    // Confirms the first resource (second to close) is still closed.
    // In try(r2; r): r closes first (throws), r2 closes second (sets flag=2).
    @Test public void testTryResourcesIdentifierSecondCloseThrows() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable this.autocloseableContent;\n"
                +"       //@ signals_only RuntimeException;\n"
                +"       public void close() { throw new RuntimeException(); }\n"
                +"    }\n"
                +"    public static class RR2 implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 2;\n"
                +"       public void close() { TestJava.flag = 2; }\n"
                +"    }\n"
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    RR r = new RR();\n"
                +"    RR2 r2 = new RR2();\n"
                +"    try {\n"
                +"      try (r2; r) {\n"
                +"         flag = 3;\n"
                +"         //@ assert TestJava.flag == 3;\n"
                +"      }\n"
                +"    } catch (Exception e) {\n"
                +"      //@ assert TestJava.flag == 2;\n"
                +"    }\n"
                +"  }\n"
                +"}"
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
                    //@ signals_only IOException;
                    public static <S extends Closeable, R extends S> void use(R resource)
                            throws IOException {
                        try (resource) {
                            resource.toString();
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
                    //@ signals_only IOException;
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
}
