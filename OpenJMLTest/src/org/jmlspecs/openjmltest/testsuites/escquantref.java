package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** A quantified variable of a reference type ranges over the values of that type: null (unless the
 *  variable is non-null, explicitly or by default) and the objects whose type is a subtype (#984). */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escquantref extends EscBase {

    static final String TRIGGER = "warning: No term in this quantified expression can serve as an SMT trigger for a: it is used only in arithmetic, comparisons or logical operations, so the solver may not use the quantifier, or may instantiate it without end; consider stating the property with a model function or pure method";

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--check-feasibility=none");
    }

    @Test // was proved, with a = o
    public void testExistsOtherType() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static class A {}
                  //@ requires o != null && !(o instanceof A);
                  //@ ensures (\\exists A a; (Object)a == o);
                  public static void m(Object o) {}
                }
                """
                ,"/tt/TestJava.java:5: " + TRIGGER,16
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition: /tt/TestJava.java:5:) in method m",22
                ,"/tt/TestJava.java:5: verify: Associated declaration: /tt/TestJava.java:6:",7
        );
    }

    @Test // an assumed \forall says nothing about objects of other types
    public void testForallAssumed() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static class A {}
                  //@ public normal_behavior
                  //@ pure
                  public static boolean p(Object o) { return true; }
                  //@ requires (\\forall A a; p(a));
                  //@ requires o != null && !(o instanceof A);
                  public static void m(Object o) {
                    //@ assert p(o);
                  }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m",9
        );
    }

    @Test // was not proved: the variable's type is known
    public void testForallTyped() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static class A {}
                  //@ ensures (\\forall A a; a instanceof A);
                  //@ ensures (\\forall nullable A a; a == null || a instanceof A);
                  public static void m() {}
                }
                """
        );
    }

    @Test // non-null by default, unless declared nullable
    public void testNullness() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static class A {}
                  //@ ensures (\\forall A a; a != null);
                  public static void m1() {}
                  //@ ensures (\\forall nullable A a; a != null);
                  public static void m2() {}
                  //@ ensures (\\exists nullable A a; a == null);
                  public static void m3() {}
                  //@ ensures (\\exists A a; a == null);
                  public static void m4() {}
                }
                """
                ,"/tt/TestJava.java:4: " + TRIGGER,16
                ,"/tt/TestJava.java:6: " + TRIGGER,16
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Postcondition: /tt/TestJava.java:6:) in method m2",22
                ,"/tt/TestJava.java:6: verify: Associated declaration: /tt/TestJava.java:7:",7
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Postcondition: /tt/TestJava.java:10:) in method m4",22
                ,"/tt/TestJava.java:10: verify: Associated declaration: /tt/TestJava.java:11:",7
        );
    }

    @Test // an unannotated type variable may be instantiated with a nullable type
    public void testTypeVariable() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava<T> {
                  //@ ensures (\\exists T t; t == null);
                  public void m1() {}
                  //@ ensures (\\exists non_null T t; t == null);
                  public void m2() {}
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition: /tt/TestJava.java:5:) in method m2",15
                ,"/tt/TestJava.java:5: verify: Associated declaration: /tt/TestJava.java:6:",7
        );
    }

    @Test // \choose is well-defined only if a value of the type satisfies the predicate
    public void testChoose() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static class A {}
                  //@ requires o != null && !(o instanceof A);
                  public static void m(Object o) {
                    //@ ghost A a = (\\choose A x; (Object)x == o);
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (ChooseNotDefined) in method m",22
        );
    }
}
