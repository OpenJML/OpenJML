package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class esc1 extends EscBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--nullable-by-default"); // Because the tests were written this way
        addOptions("--code-math=bigint","--spec-math=bigint");
        addOptions("--no-require-white-space");
    }

    @Test
    public void testCollectD() {
        addOptions("--nonnull-by-default", "--method=m");
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.*;
                public abstract class TestJava extends java.io.InputStream implements Comparable<TestJava> {
                  public String m(Integer i, Number b) {
                    Vector<Integer> v = new Vector<Integer>();
                    return null; // FAILS
                  }
                }
                """
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method m", 10
                ,"/tt/TestJava.java:3: verify: Associated declaration", 17
                ,"/tt/TestJava.java:5: verify: Associated method exit", 5);
    }

    @Test  // version of testCollectB without the calls of getClass and v.add
    public void testCollectA() {
        addOptions("--nonnull-by-default", "--method=m"); // Keep these options
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.*;
                public abstract class TestJava extends java.io.InputStream implements Comparable<TestJava> {
                  /*@ pure */ public String m(Integer i, Number b) {
                    Vector<Integer> v = new Vector<Integer>();

                    boolean bb = v.elements().hasMoreElements();
                    return null; // FAILS
                  }
                }
                """
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method m", 22
                ,"/tt/TestJava.java:3: verify: Associated declaration", 29
                ,"/tt/TestJava.java:7: verify: Associated method exit", 5);
    }

    @Test @Ignore // timesout
    public void testCollectB() {
        addOptions("--nonnull-by-default", "--timeout=300");
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.*;
                public abstract class TestJava extends java.io.InputStream implements Comparable<TestJava> {
                  public String m(java.lang.Integer i, Number b) {
                    Vector<Integer> v = new Vector<Integer>();
                    boolean bb = b instanceof Double;
                    Object oo = v.getClass();
                    v.add(0,i);
                    bb = v.elements().hasMoreElements();
                    return null; // FAILS
                  }
                }
                """
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method m", 5
                ,"/tt/TestJava.java:9: verify: Associated declaration", 5
                );
    }

    @Test @Ignore // timesout
    public void testCollectC() {
        addOptions("--nonnull-by-default", "--timeout=300");
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.*;
                public abstract class TestJava extends java.io.InputStream implements Comparable<TestJava> {
                  public String m(java.lang.Integer i, Number b) {
                    Vector<Integer> v = new Vector<Integer>();
                    boolean bb = b instanceof Double;
                    Object oo = v.getClass();
                    Object o = (Class<?>)v.getClass();
                    v.add(0,Integer.valueOf(0));
                    bb = v.elements().hasMoreElements();
                    return null; // FAILS
                  }
                }
                """
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method m", 5
                ,"/tt/TestJava.java:10: verify: Associated declaration", 5
                );
    }

    // Just testing a binary method
    // It gave trouble because the specs were missing
    @Test
    public void testGen() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1() {
                    Integer a = Integer.valueOf(0);
                  }
                }
                """);
    }

    @Test
    public void testForEachA() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1() {
                    long[] a = { 1,2,3,4};
                    for (Long k: a) {
                      //@ assert \\count >= 0; // OK
                      //@ assert \\count < a.length; // OK
                    }
                  }
                  public void m3() { // Line 10
                    long[] a = { 1,2,3,4};
                    for (long k: a) {
                      //@ assert \\count >= 1; // BAD
                    }
                  }
                  public void m4() {
                    long[] a = { 1};
                    long[] b = { 1,2};
                    for (long k: a) {
                      //@ ghost int i = \\count; // OK
                      //@ assert \\count >= 0; // OK
                      for (long kk: b) {
                         //@ assert \\count < 2; // OK
                      }
                      //@ assert \\count == i; // OK
                    }
                  }
                  public void m5() {
                    long[] a = { 1,2,3,4};
                    long[] b = { 1,2}; // Line 30
                    for (long k: a) {
                       //@ assert \\count == k-1; // OK
                    }
                  }
                  public void m6() {
                    long[] a = { 1,2,3,4};
                    //@ loop_invariant \\count >= 0 && \\count <= a.length; // OK
                    //@ decreases a.length - \\count; // OK
                    for (long k: a) {
                    } // Line 40
                  }
                  public void m6ld() {
                    long[] a = { 1,2,3,4};
                    //@ loop_invariant \\count >= 0 && \\count <= a.length; // OK
                    //@ loop_decreases a.length - \\count; // OK
                    for (long k: a) {
                    }
                  }
                  public void m7x() {
                    long[] a = { 1,2,3,4}; // Line 50
                    //@ decreases a.length - \\count - 2; // -1 on last iteration - BAD
                    for (long k: a) {
                    }
                  }
                  public TestJava() {}
                }
                """

                , "/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assert) in method m3", 11
                , "/tt/TestJava.java:51: verify: The prover cannot establish an assertion (LoopDecreasesNonNegative) in method m7x", 9
                );
    }

    @Test
    public void testForEach() {
        addOptions("--check-feasibility=reachable");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m7y() {
                    long[] a = { 1,2,3,4};
                    //@ decreases a.length - \\count -2; // BAD - last time through
                    for (long k: a) {
                    }
                  }
                  public void m7a() {
                    long[] a = { 1,2,3,4};
                    //@ decreases \\count+10; // BAD - loop does not decrease variant
                    for (long k: a) {
                    }
                  }
                  public void m8() {
                    long[] a = { 1,2,3,4};
                    //@ loop_invariant \\count > 0 && \\count <= a.length; // BAD - first time through loop
                    for (long k: a) {
                    }
                  }
                  public void m9() {
                    long[] a = { 1,2,3,4};
                    //@ loop_invariant \\count >= 0 && \\count < a.length; // BAD - laswt time through loop
                    for (long k: a) {
                    }
                  }
                  public void m2() {
                    long[] a = { 1L,2L,3L };
                    for (Long k: a) {
                      //@ assert \\count >= 0; // OK
                      //@ assert \\count < a.length; // OK
                    }
                  }
                  public void m10() {
                    long[] a = { 1,2 };
                    long[] b = { 1,2};
                    for (long k: a) {
                      //@ ghost int i = \\count; // OK
                      //@ assert \\count >= 0; // OK
                      for (long kk: b) {
                         //@ assert \\count < 2; // OK
                      }
                      //@ assert \\count == i; // OK
                    }
                  }
                  public void m2a() {
                    long[] a = {  };
                    for (Long k: a) {
                      //@ reachable; // knows that the loop is not executed, so this assert is infeasible
                    }
                  }
                  public TestJava() {}
                }
                """

                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (LoopDecreasesNonNegative) in method m7y",9
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (LoopDecreases) in method m7a",9
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (LoopInvariantBeforeLoop) in method m8",9
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (LoopInvariant) in method m9",9
                ,"/tt/TestJava.java:49: verify: There is no feasible path to program point at reachable statement in method tt.TestJava.m2a()",11
                );
    }

    @Test
    @Ignore // Needs more builtin invariants to help the prover along and definition of \values
    public void testForEach3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1() {
                    Integer[] a = { 1,2,3,4};
                    //@ loop_invariant \\values.size() == \\count;
                    for (Integer k: a) {
                    }
                  }
                  public void m2() {
                    Integer[] a = { 1,2,3,4};
                    //@ loop_invariant \\values.size() == \\count;
                    for (Integer k: a) {
                      //@ assert \\values.size() == \\count;
                    }
                  }
                  public void m3() {
                    Integer[] a = { 1,2,3,4};
                    for (Integer k: a) {
                      //@ assert \\values.size() == \\count;
                    }
                  }
                  public TestJava() {}
                  public void m3a() { // Line 23
                    long[] a = { 1,2,3,4};
                    for (long k: a) {
                      //@ assert \\count >= 1; // BAD
                    }
                  }
                }
                """

                , "/tt/TestJava.java:26: verify: The prover cannot establish an assertion (Assert) in method m3a", 11);
    }

    @Test
    public void testForEach2() {
        //addOptions("--smt=esc1a.smt","--method=m2bad");
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.*;
                public class TestJava {
                  //@ public normal_behavior  ensures true;
                  public void m2() {
                    Set<Integer> a = new HashSet<Integer>(); //@ assume a != null;
                    Iterator<Integer> it = a.iterator();
                    //@ loop_assigns it.objectState, it.remove_called_since, it.moreElements;
                    for (; it.hasNext();  ) {
                        it.next(); // OK
                    }
                  }
                  //@ public normal_behavior  ensures true;
                  public void m2bad() {
                    Set<Integer> a = new HashSet<Integer>(); //@ assume a != null;
                    Iterator<Integer> it = a.iterator();
                    //@ loop_assigns it.objectState, it.remove_called_since, it.moreElements;
                    for (; it.hasNext();  ) {
                        it.next(); // OK
                        it.next(); // ERROR - exception
                    }
                  }
                  //@ public normal_behavior  ensures true;
                  public void m3bad() {
                    Set<Integer> a = new HashSet<Integer>(); //@ assume a != null;
                    Iterator<Integer> it = a.iterator(); //@ assume it != null;
                    it.next(); // ERROR - exception
                  }
                  //@ public normal_behavior  ensures true;
                  public void m4bad() {
                    Set<Integer> a = new HashSet<Integer>(); //@ assume a != null;
                    Iterator<Integer> it = a.iterator(); //@ assume it != null;
                    for (; it.hasNext();  ) { // ERROR - should fail frame checks -- problem is with allocation check
                        it.next();
                    }
                  }
                  //@ public normal_behavior  ensures true;
                  public void m5() {
                    Set<Integer> a = new HashSet<Integer>(); //@ assume a != null;
                    Iterator<Integer> it = a.iterator(); //@ assume it != null;
                    //@ loop_assigns it.*;
                    for (; it.hasNext();  ) { // ERROR - should fail frame checks -- problem is with allocation check
                        it.next();
                    }
                  }
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m2bad", 16
                ,"/tt/TestJava.java:12: verify: Associated declaration", 14
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m3bad", 12
                ,"/tt/TestJava.java:22: verify: Associated declaration", 14
                ,anyorder(
                seq("/tt/TestJava.java:33: verify: The prover cannot establish an assertion (Assignable) in method m4bad: objectState", 16
                ,"/tt/TestJava.java:32: verify: Associated declaration", 5)
                ,seq("/tt/TestJava.java:33: verify: The prover cannot establish an assertion (Assignable) in method m4bad: moreElements", 16
                ,"/tt/TestJava.java:32: verify: Associated declaration", 5)
                ,seq("/tt/TestJava.java:33: verify: The prover cannot establish an assertion (Assignable) in method m4bad: remove_called_since", 16
                ,"/tt/TestJava.java:32: verify: Associated declaration", 5)
                )
                );
    }

    @Test
    public void testForEach2n() {
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.*; import org.jmlspecs.annotation.*;
                /*@ nullable_by_default */ public class TestJava {
                  //@ public normal_behavior  ensures true;
                  public void m2() {
                    Set<@NonNull Integer> a = new HashSet<@NonNull Integer>();
                    Iterator<@NonNull Integer> it = a.iterator();
                    //@ loop_assigns it.*;
                    for (; it.hasNext();  ) {
                        @NonNull Integer k = it.next();
                    }
                  }
                  //@ public normal_behavior  ensures true;
                  public void m2bad() {
                    Set<@Nullable Integer> a = new HashSet<@Nullable Integer>();
                    Iterator<@Nullable Integer> it = a.iterator();
                    //@ loop_assigns it.*;
                    for (; it.hasNext();  ) {
                        @NonNull Integer k = it.next(); // ERROR
                    }
                  }
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (PossiblyNullInitialization) in method m2bad: k",26
                );
    }

    @Test
    public void testForEach2a1() {
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.*; import java.util.Map.Entry;
                public class TestJava {
                  //@ public normal_behavior  ensures true;
                  public void m1() {
                    Set<Entry<String,String>> a = new HashSet<Entry<String,String>>();
                    for (Entry<String,String> k: a) {
                    }
                  }
                  public TestJava() {}
                }
                """
        );
    }

    @Test
    public void testForEach2a2() {
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava", 
                """
                package tt; import java.util.*; import java.util.Map.Entry;
                public class TestJava {
                  //@ public behavior  ensures true;
                  public void m2() {
                    List<Entry<String,String>> values = new LinkedList<Entry<String,String>>();
                    //@ assume values != null; set values.containsNull = true;
                    Set<Entry<String,String>> a = new HashSet<Entry<String,String>>();
                    Iterator<Entry<String,String>> it = a.iterator();
                    Entry<String,String> k;
                    //@ ghost List<Entry<String,String>> v = values; // Line 10
                    //@ loop_invariant values == v;
                    //@ loop_assigns it.*, k, values.*;
                    for (; it.hasNext(); values.add(k) ) {
                        k = it.next();  // k might be null -- default is nullable
                        //@ assert k != null ==> \\typeof(k) <:= \\type(Entry<String,String>);
                    }
                  }
                  public TestJava() {}
                }
                """
        );
    }

    @Test
    public void testForEach2a2a() {
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava", 
                """
                package tt; import org.jmlspecs.annotation.*; import java.util.*; import java.util.Map.Entry;
                public class TestJava {

                  //@ public behavior  ensures true;
                  public void m2a() {
                    List<Entry<String,String>> values = new LinkedList<Entry<String,String>>();
                    //@ set values.containsNull = false;
                    Set<@NonNull Entry<String,String>> azz = new HashSet<@NonNull Entry<String,String>>();
                    Iterator<@NonNull Entry<String,String>> it = azz.iterator();
                    @NonNull Entry<String,String> k;
                    //@ ghost List<Entry<String,String>> v = values;
                    //@ loop_invariant values == v;
                    //@ loop_assigns k,it.*, values.*;
                    while (it.hasNext()) {
                        k = it.next();
                        //@ assert k != null;
                        values.add(k);
                    }
                  }
                  public TestJava() {}
                }
                """
        );
    }
    
    // This example originally crashed because NonNull is not resolvable (no import of the annotations)
    @Test
    public void testForEach2a2b() {
        addOptions("--esc-max-warnings=1");
        expectedExit = 1;
        helpEsc("tt.TestJava", 
                """
                package tt; import java.util.*; import java.util.Map.Entry;
                public class TestJava {

                  //@ public behavior  ensures true;
                  public void m2a() {
                    List<Entry<String,String>> values = new LinkedList<Entry<String,String>>();
                    //@ set values.containsNull = false;
                    Set<@NonNull Entry<String,String>> a = new HashSet<@NonNull Entry<String,String>>();
                    Iterator<@NonNull Entry<String,String>> it = a.iterator();
                    @NonNull Entry<String,String> k;
                    //@ ghost List<Entry<String,String>> v = values;
                    //@ loop_invariant values == v;
                    //@ loop_assigns k, it.*, values.*;
                    while (it.hasNext()) {
                        k = it.next();
                        //@ assert k != null;
                        values.add(k);
                    }
                  }
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: error: cannot find symbol\n"
                        + "  symbol:   class NonNull\n"
                        + "  location: class tt.TestJava", 57
                ,"/tt/TestJava.java:8: error: cannot find symbol\n"
                        + "  symbol:   class NonNull\n"
                        + "  location: class tt.TestJava", 10
                ,"/tt/TestJava.java:9: error: cannot find symbol\n"
                        + "  symbol:   class NonNull\n"
                        + "  location: class tt.TestJava", 15
                ,"/tt/TestJava.java:10: error: cannot find symbol\n"
                        + "  symbol:   class NonNull\n"
                        + "  location: class tt.TestJava", 6
        );
    }
    



    @Test
    public void testFresh() {
        helpEsc("tt.TestJava",
                """
                package tt;
                abstract public class TestJava {
                  //@ requires p != null && p != this;
                  //@ assigns \\everything;
                  public void m1(Object p) {
                    Object pp = c1(p); // result is fresh
                    //@ assert pp != p; // OK
                    //@ assert pp != this; // OK
                  }
                  //@ requires p != null && p != this;
                  //@ assigns \\everything;
                  public void m2(Object p) {
                    Object pp = c2(p);
                    //@ assert pp != p; // BAD
                  }
                  //@ requires p != null && p != this;
                  //@ assigns \\everything;
                  public void m3(Object p) {
                    Object pp = c2(p);
                    //@ assert pp != this; // BAD // Line 20
                  }
                  //@ requires p != null && p != this;
                  //@ assigns \\everything;
                  public void m4(Object p) {
                    Object pp = c1(p);
                    Object q = new Object();
                    //@ assert pp != q; // OK
                  }
                  //@ requires p != null && p != this;
                  //@ assigns \\everything; // Line 30
                  public void m5(Object p) {
                    Object pp = c2(p);
                    Object q = new Object();
                    //@ assert pp != q; // OK
                  }
                  //@ assigns \\everything;
                  //@ ensures \\result != null && \\fresh(\\result);
                  //@ ensures \\result != p && \\result != this;
                  public Object m6(Object p) {
                    return new Object(); // Line 40
                  }
                  //@ assigns \\everything;
                  //@ ensures \\result == null; // BAD
                  public Object m6a(Object p) {
                    return new Object();
                  }
                  //@ assigns \\everything;
                  //@ ensures \\result != null && \\fresh(\\result);
                  //@ ensures \\result == p || \\result == this; // BAD
                  public Object m6b(Object p) {
                    return new Object();
                  }
                  //@ assigns \\everything;
                  //@ ensures \\result != null && !\\fresh(\\result); // BAD
                  public Object m6c(Object p) {
                    return new Object();
                  }
                  Object o;
                  //@ ghost public Object oo;
                  static Object so;
                  //@ static ghost Object soo;
                  //@ assigns \\nothing;
                  public void m7(Object p) {
                    Object pp = c1(p);
                    //@ assert pp != o && pp != oo; // OK
                  }
                  //@ assigns \\nothing;
                  public void m7a(Object p) {
                    Object pp = c2(p);
                    //@ assert pp != o; // BAD
                  }
                  //@ assigns \\nothing;
                  public void m7b(Object p) {
                    Object pp = c2(p);
                    //@ assert pp != oo; // BAD
                  }
                  //@ assigns \\everything;
                  public void m7c(Object p) {
                    Object pp = c1ex(p); // fresh result, but oo is not modified
                    //@ assert pp != oo; // OK
                  }
                  //@ assigns \\everything;
                  public void m7cx(Object p) {
                    Object pp = c1e(p); // fresh result, but oo is possibly modified and possibly to the same thing
                    //@ assert pp != oo; // FAILS
                  }
                  //@ assigns \\everything;
                  public void m7d(Object p) {
                    Object pp = c2e(p); // not-necessarily fresh result
                    //@ assert pp != o; // BAD
                  }
                  //@ assigns \\nothing;
                  public void m8(Object p) {
                    Object pp = c1(p);
                    //@ assert pp != so && pp != soo; // OK
                  }
                  //@ assigns \\nothing;
                  public void m8a(Object p) {
                    Object pp = c2(p);
                    //@ assert pp != so; // BAD
                  }
                  //@ assigns \\nothing;
                  public void m8b(Object p) {
                    Object pp = c2(p);
                    //@ assert pp != soo; // BAD -- \\result might have been set to soo
                  }
                  //@ assigns \\everything;
                  public void m8c(Object p) {
                    Object pp = c1e(p); // fresh result, but soo might be modified also
                    //@ assert pp != soo; // FAILS
                  }
                  //@ assigns \\everything;
                  public void m8d(Object p) {
                    Object pp = c1e(p); // fresh result, but so might be modified also
                    //@ assert pp != so; // FAILS
                  }
                  //@ assigns \\nothing;
                  public void m9a(Object p) {
                    Object pp = c1n(p); // if pp is allowed to be null, then it might equal o or oo
                    //@ assert pp != o && pp != oo; // BAD
                  }
                  //@ assigns \\nothing;
                  public void m9b(Object p) {
                    Object pp = c1n(p);
                    //@ assert pp != so && pp != soo; // BAD
                  }
                  //@ assigns \\nothing;
                  //@ ensures \\fresh(\\result);
                  abstract public Object c1(Object o);
                  //@ assigns \\nothing;
                  //@ ensures \\result == null || \\fresh(\\result);
                  abstract public Object c1n(Object o);
                  //@ assigns \\nothing;
                  //@ ensures true;
                  abstract public Object c2(Object o);
                  //@ assigns \\everything;
                  //@ ensures \\result != null && \\fresh(\\result);
                  abstract public Object c1e(Object o);
                  //@ assigns \\everything;
                  //@ ensures true;
                  abstract public Object c2e(Object o);
                  //@ assigns \\everything;
                  //@ ensures \\result != null && \\fresh(\\result) && oo == \\old(oo);
                  abstract public Object c1ex(Object o);
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Assert) in method m2", 9
                ,"/tt/TestJava.java:20: verify: The prover cannot establish an assertion (Assert) in method m3", 9
                ,"/tt/TestJava.java:45: verify: The prover cannot establish an assertion (Postcondition) in method m6a",5
                , "/tt/TestJava.java:43: verify: Associated declaration", 7
                ,"/tt/TestJava.java:51: verify: The prover cannot establish an assertion (Postcondition) in method m6b",5
                , "/tt/TestJava.java:49: verify: Associated declaration", 7
                ,"/tt/TestJava.java:56: verify: The prover cannot establish an assertion (Postcondition) in method m6c",5
                , "/tt/TestJava.java:54: verify: Associated declaration", 7
                ,"/tt/TestJava.java:70: verify: The prover cannot establish an assertion (Assert) in method m7a", 9
                ,"/tt/TestJava.java:75: verify: The prover cannot establish an assertion (Assert) in method m7b", 9
                ,"/tt/TestJava.java:85: verify: The prover cannot establish an assertion (Assert) in method m7cx",9
                ,"/tt/TestJava.java:90: verify: The prover cannot establish an assertion (Assert) in method m7d", 9
                ,"/tt/TestJava.java:100: verify: The prover cannot establish an assertion (Assert) in method m8a", 9
                ,"/tt/TestJava.java:105: verify: The prover cannot establish an assertion (Assert) in method m8b", 9
                ,"/tt/TestJava.java:110: verify: The prover cannot establish an assertion (Assert) in method m8c", 9
                ,"/tt/TestJava.java:115: verify: The prover cannot establish an assertion (Assert) in method m8d", 9
                ,"/tt/TestJava.java:120: verify: The prover cannot establish an assertion (Assert) in method m9a", 9
                ,"/tt/TestJava.java:125: verify: The prover cannot establish an assertion (Assert) in method m9b", 9);
    }

    @Test
    public void testAssignables4a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k; public static int sk;
                  public static TestJava p;
                  //@ requires p != null && p != this;
                  //@ assigns  \\everything;
                  public void m1() {
                    //@ assume this.k == 0;
                    c1(p); // havoc p.*, including p.k, but p != this
                    //@ assert this.k == 0; // OK
                  }
                  //@ requires p != null && p != this;
                  //@ assigns  \\everything;
                  public void m1a() {
                    //@ assume sk == 0;
                    c1(p); // havoc p.* does not include sk
                    //@ assert sk == 0; // OK
                  }
                  //@ requires o != null;
                  //@ assigns  o.*; // Line 20
                  public void c1(TestJava o) { }
                  //@ requires o != null;
                  //@ assigns  TestJava.*;
                  public void c2(TestJava o) { }
                  //@ assigns  o.sk; // ERROR - receiver is checked even if the field is static
                  public void c3(TestJava o) { }
                  //@ requires o != null;
                  //@ assigns  o.sk;
                  public void c4(TestJava o) { }
                }
                """
                ,"/tt/TestJava.java:25: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method c3",17
                );
    }

    @Test
    public void testAssignables4b() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k; public static int sk;
                  public static TestJava p;
                  //@ requires p != null && p != this;
                  //@ assigns \\everything;
                  public void m2a() {
                    //@ assume k == 0;
                    c1(this); // havoc
                    //@ assert k == 0; // FAILS
                  }
                  //@ requires p != null && p != this;
                  //@ assigns \\everything;
                  public void m2b() {
                    //@ assume sk == 0;
                    c1(this); // havoc this.*, not static fields
                    //@ assert sk == 0; // OK
                  }
                  //@ requires o != null;
                  //@ assigns o.*;
                  public void c1(TestJava o) { }
                  //@ requires o != null;
                  //@ assigns TestJava.*;
                  public void c2(TestJava o) { }
                }
                """
                , "/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m2a",
                9);
    }

    @Test
    public void testAssignables4c() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k; public static int sk;
                  public static TestJava p;
                  //@ requires p != null && p != this;
                  //@ assigns \\everything;
                  public void m3() {
                    //@ assume k == 0;
                    c2(this); // havoc TestJava.* does not include non-static k
                    //@ assert k == 0; // OK
                  }
                  //@ requires p != null && p != this;
                  //@ assigns \\everything;
                  public void m3a() {
                    //@ assume sk == 0;
                    c2(this); // havoc TestJava.* does include static sk
                    //@ assert sk == 0; // FAILS
                  }
                  //@ requires o != null;
                  //@ assigns o.*;
                  public void c1(TestJava o) { }
                  //@ requires o != null;
                  //@ assigns TestJava.*;
                  public void c2(TestJava o) { }
                }
                """
                , "/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assert) in method m3a",
                9);
    }

    @Test
    public void testAssignables1a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  int k; static int sk;
                  int[] a; static int[] sa;
                  //@ assigns \\everything;
                  public void m1x() {
                    //@ assume k == 0;
                    c1(1);
                    //@ assert k == 0;
                  }
                  //@ requires i == 0;
                  //@ assigns \\everything;
                  //@ also requires i > 0;
                  //@ assigns \\nothing;
                  public void c1(int i) { }
                }
                """);
    }

    @Test
    public void testAssignables1b() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  int k; static int sk;
                  int[] a; static int[] sa;
                  //@ assigns \\everything;
                  public void m1a() {
                    //@ assume k == 0;
                    c1(0);
                    //@ assert k == 0; // FAILS
                  }
                  //@ requires i == 0;
                  //@ assigns \\everything;
                  //@ also requires i > 0;
                  //@ assigns \\nothing;
                  public void c1(int i) { }
                }
                """,
                "/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m1a", 9);
    }

    @Test
    public void testAssignables1c() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  int k; static int sk;
                  int[] a; static int[] sa;
                  //@ assigns \\everything;
                  public void m2() {
                    //@ assume sk == 0;
                    c1(1);
                    //@ assert sk == 0;
                  }
                  //@ requires i == 0;
                  //@ assigns \\everything;
                  //@ also requires i > 0;
                  //@ assigns \\nothing;
                  public void c1(int i) { }
                }
                """);
    }

    @Test
    public void testAssignables1d() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  int k; static int sk;
                  int[] a; static int[] sa;
                  //@ assigns \\everything;
                  public void m2a() {
                    //@ assume sk == 0;
                    c1(0);
                    //@ assert sk == 0; // FAILS
                  }
                  //@ requires i == 0;
                  //@ assigns \\everything;
                  //@ also requires i > 0;
                  //@ assigns \\nothing;
                  public void c1(int i) { }
                }
                """,
                "/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m2a", 9);
    }

    @Test
    public void testAssignables6a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k; public static int sk;
                  public int[] a; static public int[] sa;
                  //@ requires a != null && a.length > 10;
                  //@ assigns \\everything;
                  public void m3() {
                    //@ assume a[0] == 0;
                    c1(1);
                    //@ assert a[0] == 0;
                  }
                  //@ requires i == 0;
                  //@ assigns \\everything;
                  //@ also requires i > 0;
                  //@ assigns \\nothing;
                  public void c1(int i) { }
                }
                """);
    }

    @Test
    public void testAssignables6b() {
        addOptions("--exclude=<init>");  // FIXME - I think <init> here and elsewhere is out of date
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k; public static int sk;
                  public int[] a; public static int[] sa;
                  //@ requires a != null && a.length > 10;
                  //@ assigns \\everything;
                  public void m3a() {
                    //@ assume a[0] == 0;
                    c1(0); // assigns everything
                    //@ assert a[0] == 0; // FAILS
                  }
                  //@ requires i == 0;
                  //@ assigns \\everything;
                  //@ also requires i > 0;
                  //@ assigns \\nothing;
                  public void c1(int i) { }
                }
                """,
                anyorder(
                        seq("/tt/TestJava.java:10: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m3a",
                                17),
                        seq("/tt/TestJava.java:10: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m3a",
                                17),
                        seq("/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m3a",
                                9))

        );
    }

    @Test
    public void testAssignables6c() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k; public static int sk;
                  public int[] a; public static int[] sa;
                  //@ requires sa != null && sa.length > 10;
                  //@ assigns \\everything;
                  public void m4() {
                    //@ assume sa[0] == 0;
                    c1(1);
                    //@ assert sa[0] == 0;
                  }
                  //@ requires i == 0;
                  //@ assigns \\everything;
                  //@ also requires i > 0;
                  //@ assigns \\nothing;
                  public void c1(int i) { }
                }
                """);
    }

    @Test
    public void testAssignables6d() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k; public static int sk;
                  public int[] a; public static int[] sa;
                  //@ requires sa != null && sa.length > 10;
                  //@ assigns \\everything;
                  public void m4a() {
                    //@ assume sa[0] == 0;
                    c1(0);
                    //@ assert sa[0] == 0; // FAILS
                  }
                  //@ requires i == 0;
                  //@ assigns \\everything;
                  //@ also requires i > 0;
                  //@ assigns \\nothing;
                  public void c1(int i) { }
                }
                """
        // Should be just three messages, but in an arbitrary order
                ,
                anyorder(
                        seq("/tt/TestJava.java:10: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m4a",
                                18),
                        seq("/tt/TestJava.java:10: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m4a",
                                18),
                        seq("/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m4a",
                                9)));
    }

    @Test
    public void testAssignables5a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k; public static int sk;
                  public int[] a; public static int[] sa;
                  //@ requires sa != null && sa.length > 10;
                  //@ assigns \\everything;
                  public void m5() {
                    //@ assume a == \\old(a);
                    c1(1);
                    //@ assert a == \\old(a);
                  }
                  //@ requires i == 0;
                  //@ assigns \\everything;
                  //@ also requires i > 0;
                  //@ assigns \\nothing;
                  public void c1(int i) { }
                }
                """);
    }

    @Test
    public void testAssignables5b() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k; public static int sk;
                  public int[] a; public static int[] sa;
                  //@ requires sa != null && sa.length > 10;
                  //@ assigns \\everything;
                  public void m5a() {
                    //@ assume a == \\old(a);
                    c1(0);
                    //@ assert a == \\old(a); // FAILS
                  }
                  //@ requires i == 0;
                  //@ assigns \\everything;
                  //@ also requires i > 0;
                  //@ assigns \\nothing;
                  public void c1(int i) { }
                }
                """,
                "/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m5a", 9);
    }

    @Test
    public void testAssignables5c() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  int k; static int sk;
                  int[] a; static int[] sa;
                  //@ assigns \\everything;
                  public void m6(/*@ non_null*/TestJava t) {
                    //@ assume t.k == 0;
                    c1(1);
                    //@ assert t.k == 0;
                  }
                  //@ requires i == 0;
                  //@ assigns \\everything;
                  //@ also requires i > 0;
                  //@ assigns \\nothing;
                  public void c1(int i) { }
                }
                """);
    }

    @Test
    public void testAssignables5d() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  int k; static int sk;
                  int[] a; static int[] sa;
                  //@ assigns \\everything;
                  public void m6a(/*@ non_null*/TestJava t) {
                    //@ assume t.k == 0;
                    c1(0);
                    //@ assert t.k == 0; // FAILS
                  }
                  //@ requires i == 0;
                  //@ assigns \\everything;
                  //@ also requires i > 0;
                  //@ assigns \\nothing;
                  public void c1(int i) { }
                }
                """,
                "/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m6a", 9);
    }

    @Test
    public void testAssignables5e() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  int k; static int sk;
                  int[] a; static int[] sa;
                  //@ assigns \\everything;
                  public void m7() {
                    c1(1);
                    //@ assert sk == \\old(sk); // Should be OK
                  }
                  //@ requires i == 0;
                  //@ assigns \\everything;
                  //@ also requires i > 0;
                  //@ assigns \\nothing;
                  public void c1(int i) { }
                }
                """);
    }

    @Test
    public void testAssignables5f() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  int k; static int sk;
                  int[] a; static int[] sa;
                  //@ assigns \\everything;
                  public void m7a() {
                    c1(0);
                    //@ assert sk == \\old(sk); // FAILS
                  }
                  //@ requires i == 0;
                  //@ assigns \\everything;
                  //@ also requires i > 0;
                  //@ assigns \\nothing;
                  public void c1(int i) { }
                }
                """,
                "/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method m7a", 9);
    }

    @Test
    public void testAssignables2a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k;
                  public static int sk;
                  //@ assigns k,sk;
                  public void m1() {
                    //@ assume k == 0 && sk == 0;
                    c1(0);
                    //@ assert sk == 0;
                  }
                  //@ assigns k,sk;
                  public void m1a() {
                    //@ assume k == 0 && sk == 0;
                    c1(1);
                    //@ assert sk == 0; // FAILS
                  }
                  //@ assigns k,sk;
                  public void m2() {
                    //@ assume k == 0 && sk == 0;
                    c1(1);
                    //@ assert k == 0;
                  }
                  //@ assigns k,sk;
                  public void m2a() {
                    //@ assume k == 0 && sk == 0;
                    c1(0);
                    //@ assert k == 0; // FAILS
                  }
                  public static int[] a; public int[] b;
                  //@ requires i == 0;
                  //@ assigns k;
                  //@ also requires i > 0;
                  //@ assigns sk;
                  public void c1(int i) { }
                  //@ requires i == 10 && t != null;
                  //@ assigns t.k;
                  //@ also requires i == 0;
                  //@ assigns \\nothing;
                  public void c2(int i, TestJava t) {}
                  //@ requires a!=null && 0<=i && i<a.length;
                  //@ assigns a[i];
                  public void c3(int i) {}
                  //@ requires b!=null && 0<=i && i<b.length;
                  //@ assigns b[i];
                  public void c4(int i) {}
                }
                """,
                "/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Assert) in method m1a", 9,
                "/tt/TestJava.java:27: verify: The prover cannot establish an assertion (Assert) in method m2a", 9);
    }

    @Test
    public void testAssignables2b() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k;
                  public static int sk;
                  //@ assigns k,sk;
                  public void m3() {
                    //@ assume k == 0 && sk == 0;
                    c2(0,this);
                    //@ assert k == 0;
                  }
                  //@ assigns k,sk;
                  public void m3a() {
                    //@ assume k == 0 && sk == 0;
                    c2(10,this);
                    //@ assert k == 0; // FAILS
                  }
                  public static int[] a; public int[] b;
                  //@ requires a != null && a.length == 5;
                  //@ assigns a[0];
                  public void m4() {
                    //@ assume a[0] == 0 && a[1] == 1;
                    c3(0);
                    //@ assert a[1] == 1;
                  }
                  //@ requires a != null && a.length == 5;
                  //@ assigns a[0];
                  public void m4a() {
                    //@ assume a[0] == 0 && a[1] == 1;
                    c3(0);
                    //@ assert a[0] == 0; // FAILS // Line 30
                  }
                  //@ requires i == 0;
                  //@ assigns k;
                  //@ also requires i > 0;
                  //@ assigns sk;
                  public void c1(int i) { }
                  //@ requires i == 10 && t != null;
                  //@ assigns t.k;
                  //@ also requires i == 0;
                  //@ assigns \\nothing;
                  public void c2(int i, TestJava t) {}
                  //@ requires a!=null && 0<=i && i<a.length;
                  //@ assigns a[i];
                  public void c3(int i) {}
                  //@ requires b!=null && 0<=i && i<b.length;
                  //@ assigns b[i];
                  public void c4(int i) {}
                }
                """,
                "/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Assert) in method m3a", 9,
                "/tt/TestJava.java:30: verify: The prover cannot establish an assertion (Assert) in method m4a", 9);
    }

    @Test
    public void testAssignables2c() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k;
                  public static int sk;
                  public static int[] a; public int[] b;
                  //@ requires b != null && b.length == 5;
                  //@ assigns b[0];
                  public void m5() {
                    //@ assume b[0] == 0 && b[1] == 1;
                    c4(0);
                    //@ assert b[1] == 1;
                  }
                  //@ requires b != null && b.length == 5;
                  //@ assigns b[0];
                  public void m5a() {
                    //@ assume b[0] == 0 && b[1] == 1;
                    c4(0);
                    //@ assert b[0] == 0; // FAILS
                  }
                  //@ requires b != null && b.length == 5; // Line 20
                  //@ assigns b[0];
                  public void m6a() {
                    //@ assume b[0] == 0 && b[1] == 1;
                    c3(0); // changes a[0] - also get a null deference warning
                  }
                  //@ requires a != null && b != null && b.length == 5  && a.length ==5;
                  //@ assigns a[0],b[0];
                  public void m6() {
                    //@ assume b[0] == 0 && b[1] == 1;
                    c3(0); // changes a[0] - now ok
                    //@ assert b[1] == 1;
                  }
                  //@ requires i == 0;
                  //@ assigns k;
                  //@ also requires i > 0;
                  //@ assigns sk;
                  public void c1(int i) { }
                  //@ requires i == 10 && t != null;
                  //@ assigns t.k;
                  //@ also requires i == 0; // Line 40
                  //@ assigns \\nothing;
                  public void c2(int i, TestJava t) {}
                  //@ requires a!=null && 0<=i && i<a.length;
                  //@ assigns a[i];
                  public void c3(int i) {}
                  //@ requires b!=null && 0<=i && i<b.length;
                  //@ assigns b[i];
                  public void c4(int i) {}
                }
                """,
                seq("/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Assert) in method m5a", 9,
                  anyorder(
                    seq("/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Assignable) in method m6a: a[i]",7
                      , "/tt/TestJava.java:21: verify: Associated declaration", 7
                      ),
                    seq("/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Precondition) in method m6a",7
                      , "/tt/TestJava.java:45: verify: Associated declaration", 15
                      , oneof(
                         seq("/tt/TestJava.java:43: verify: Precondition conjunct is false: a != null",17)
                        ,seq("/tt/TestJava.java:43: verify: Precondition conjunct is false: i < a.length",36)
                        )
                 ))));
    }

    @Test
    public void testAssignables3a() {
        addOptions("--method=m1a");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int[] a;  //@ public invariant a != null && a.length == 10;
                  /*@ assignable a; */ public TestJava() {
                     a = new int[10];
                  }
                  //@ assigns a[*];
                  public void m1() {
                    //@ assume a[0] == 0 && a[2] == 2;
                    c1();
                    //@ assert a[0] == 0;
                  }
                  //@ assigns a[*];
                  public void m1a() {
                    //@ assume a[0] == 0 && a[2] == 2;
                    c1();
                    //@ assert a[2] == 3; // FAILS
                  }
                  //@ assigns a[2 .. 4];
                  public void c1() { }
                  //@ assigns a[*];
                  public void c2() {}
                  //@ assigns a[2 .. ];
                  public void c3() {}
                }
                """,
                "/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assert) in method m1a", 9);
    }

    @Test
    public void testAssignables3b() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int[] a;  //@ public invariant a != null && a.length == 10;
                  //@ assignable a;
                  public TestJava() {
                     a = new int[10];
                  }
                  //@ assigns a[*];
                  public void m2a() {
                    //@ assume a[0] == 0 && a[2] == 2;
                    c2();
                    //@ assert a[0] == 0; // FAILS
                  }
                  //@ assigns a[*];
                  public void m2b() {
                    //@ assume a[0] == 0 && a[2] == 2;
                    c2();
                    //@ assert a[2] == 2; // FAILS
                  }
                  //@ assigns a[2 .. 4];
                  public void c1() { }
                  //@ assigns a[*];
                  public void c2() {}
                  //@ assigns a[2 .. ];
                  public void c3() {}
                }
                """,
                "/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method m2a", 9,
                "/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Assert) in method m2b", 9);
    }

    @Test
    public void testAssignables3c() {
        addOptions("--exclude=<init>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int[] a;  //@ public invariant a != null && a.length == 10;
                  //@ assignable a;
                  public TestJava() {
                     a = new int[10];
                  }
                  //@ assigns a[*];
                  public void m3() {
                    //@ assume a[0] == 0 && a[2] == 2;
                    c3();
                    //@ assert a[0] == 0;
                  }
                  //@ assigns a[*];
                  public void m3a() {
                    //@ assume a[0] == 0 && a[9] == 2;
                    c3();
                    //@ assert a[9] == 2; // FAILS
                  }
                  //@ assigns a[2 .. 4];
                  public void c1() { }
                  //@ assigns a[*];
                  public void c2() {}
                  //@ assigns a[2 .. ];
                  public void c3() {}
                }
                """,
                "/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Assert) in method m3a", 9);
    }

    @Test
    public void testFinal() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static final int fa = 13;
                  public static int a = 15;
                  //@ assigns \\everything;
                  public void z() {
                  }
                  //@ assigns \\everything;
                  public void m1() {
                    //@ assume a == 15 && fa == 13;
                    z();
                    //@ assert fa == 13; // Should be OK
                    //@ assert a == 15; // Should fail
                  }
                }
                """, "/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assert) in method m1",
                9);
    }

    @Test
    public void testFinal2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static final int fsa = 13;
                  public final int fa = 15;
                  public final int fb;
                  public int a = 17;
                  public TestJava() {
                    //@ assert fsa == 13; // OK
                    //@ assert fa == 15; // OK
                    fb = 16;
                  }
                  //@ assigns \\everything;
                  public void m1() {
                    //@ assert fsa == 13; // Should be OK
                    //@ assert fa == 15; // Should be OK
                  }
                  //@ assigns \\everything;
                  public void m2() {
                    //@ assert a == 17; // Not necessarily OK
                  }
                  //@ assigns \\everything;
                  public void m3() {
                    //@ assert fb == 16; // Not necessarily OK
                  }
                }
                """, "/tt/TestJava.java:19: verify: The prover cannot establish an assertion (Assert) in method m2",
                9, "/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Assert) in method m3", 9);
    }

    @Test
    public void testMethodCallsWithExceptions() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_bigint_math*/  public class TestJava {
                  public static int k;
                  //@ requires i >= 0;
                  //@ assigns k;
                  //@ ensures k == 10;
                  //@ signals (Exception e) k<0; signals_only Exception;
                  public void m1(int i) throws RuntimeException {
                    m(i);
                    k = 10;
                  }
                  //@ requires i >= 0;
                  //@ assigns k;
                  //@ ensures k == 10;
                  //@ signals (Exception e) k==-11;
                  //@ signals_only Exception;
                  public void m2(int i) {
                    m(1);
                    m(2);
                    k = 10; // Line 20
                  }
                  //@ requires i >= 0;
                  //@ assigns k;
                  //@ ensures k == 10;
                  //@ signals (Exception e) k==-12;
                  //@ signals_only Exception;
                  public void m3(int i) {
                    m(0);
                    m(2);
                    k = 10;
                  }
                  //@ requires i >= 0;
                  //@ assigns k;
                  //@ ensures k == 10;
                  //@ signals (Exception e) k==-13; // FAILS
                  //@ signals_only Exception;
                  public void m3a(int i) {
                    m(0);
                    m(2); // FAILS
                    k = 10; // Line 40
                  }
                  //@ requires i >= 0;
                  //@ assigns k;
                  //@ ensures \\result == 12;
                  //@ signals (Exception e) false;
                  public int m4(int i) {
                    return 10+m(0)+m(0);
                  }
                  //@ requires i >= 0;
                  //@ assigns k; // Line 50
                  //@ ensures false;
                  //@ signals (Exception e) k == -11;
                  //@ signals_only Exception;
                  public int m5(int i) {
                    return 10+m(1)+m(0);
                  }
                  //@ requires i >= 0;
                  //@ assigns k;
                  //@ ensures false;
                  //@ signals (Exception e) k == -12; // Line 60
                  //@ signals_only Exception;
                  public int m6(int i) {
                    return 10+m(0)+m(2);
                  }
                  //@ requires i == 0;
                  //@ assigns k;
                  //@ ensures k>0 && \\result == i+1;
                  //@ signals (Exception e) false;
                  //@ also
                  //@ requires i > 0; // Line 70
                  //@ assigns k;
                  //@ ensures false;
                  //@ signals (Exception e) k == -10-i;
                  //@ signals_only Exception;
                  public int m(int i) {
                    if (i > 0) {
                      k = -10-i;
                      throw new RuntimeException();
                    }
                    k = 1;
                    return i+1;
                  }
                }
                """,
                "/tt/TestJava.java:39: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m3a",
                6, "/tt/TestJava.java:35: verify: Associated declaration", 7);
    }

    @Test
    public void testStrings() {
        helpEsc("tt.TestJava",
                """
                package tt; //@ code_bigint_math
                public class TestJava {
                  String s;
                  String ss = "abcde";
                  public boolean m(String sss) {
                    return sss == ("abcde");
                  }
                  public boolean m1(/*@ non_null*/ String sss) {
                    return sss.equals("abcde");
                  }
                }
                """);
    }

    @Test
    public void testRequiresClause() {
        addOptions("--check-feasibility=precondition");
        helpEsc("tt.TestJava", // static invariant is assumed true at start of constructor; remains true at end
                """
                package tt;
                public class TestJava {
                  TestJava() { }
                  public TestJava(int i) {}
                  //@ requires false;
                  public static boolean bf(boolean bb) { return true; }
                  //@ requires true;
                  public static boolean bt(boolean bb) { return true; }
                  static public boolean b = true;
                  //@ static public invariant b;
                  //@ requires !b;
                  public static boolean bq(boolean bb) { return true; }
                }
                """,
                
                "/tt/TestJava.java:6: verify: Invariants+Preconditions appear to be contradictory in method tt.TestJava.bf(boolean)",
                25,
                "/tt/TestJava.java:12: verify: Invariants+Preconditions appear to be contradictory in method tt.TestJava.bq(boolean)",
                25);
    }

    @Test
    public void testJava() {
        addOptions("--check-feasibility=precondition");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static boolean bstatic;
                  public boolean binstance;
                  public boolean binstance2;
                  /*@ non_null */ Object o;
                  //@ ghost nullable Object oo;
                  //@ public static invariant bstatic;  // FIXME - static initialization should fail
                  //@ public invariant binstance;
                  //@ public initially binstance2;  // Line 10
                  //@ public constraint binstance2 == \\old(binstance2);
                  //@ public static constraint bstatic == \\old(bstatic);
                  public static void main(/*@ non_null*/ String[] args) {  } // OK
                  //@ requires true;
                  //@ ensures \\result;
                  public static boolean b(boolean bb) { return true; } // OK
                  //@ requires false;
                  //@ ensures true;
                  public static int i(int ii) { return 0; } // ERROR: precondition not feasible
                  //@ requires ii == 10;  // Line 20
                  //@ ensures true;
                  public Object inst(int ii) { binstance = ii == 0; o = null; /*@ set oo = null;*/ return null; } // ERROR: null assignments
                  //@ requires ii == 10;\
                  //@ ensures true;
                  public /*@ nullable */ Object insx(int ii) { binstance = true;           /*@ set oo = null;*/ return null; }
                  //@ requires ii == 10;
                  //@ ensures true;
                  public Object insy(int ii) { binstance = ii == 0;            return null; }
                  //@ requires ii == 10;
                  //@ ensures true;
                  public Object insz(int ii) { binstance = ii == 0;            return o; }
                  public TestJava() { o = new Object(); binstance = true; } // ERROR: binstance2 not true
                  public TestJava(int i) { o = new Object(); binstance2 = true; } // ERROR: binstance not true
                  public TestJava(double d) { binstance = binstance2 = true; } // ERROR: o is null
                }
                """
                ,"/tt/TestJava.java:19: verify: Invariants+Preconditions appear to be contradictory in method tt.TestJava.i(int)",21 // precondition is false
                ,"/tt/TestJava.java:22: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method inst",55
                ,"/tt/TestJava.java:27: verify: The prover cannot establish an assertion (InvariantExit) in method insy",64 // binstance is false
                ,"/tt/TestJava.java:9: verify: Associated declaration", 14
                ,"/tt/TestJava.java:30: verify: The prover cannot establish an assertion (InvariantExit) in method insz",64 // binstance is false
                ,"/tt/TestJava.java:9: verify: Associated declaration", 14
                ,"/tt/TestJava.java:31: verify: The prover cannot establish an assertion (Initially) in method TestJava",10 // nothing sets binstance2 true
                ,"/tt/TestJava.java:10: verify: Associated declaration", 14
                ,"/tt/TestJava.java:32: verify: The prover cannot establish an assertion (InvariantExit) in method TestJava",10 // nothing sets binstance true
                ,"/tt/TestJava.java:9: verify: Associated declaration", 14
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (NullField) in method TestJava", 26
                );
    }

    @Test
    public void testAssert() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires bb;
                  //@ ensures true;
                  public static void bassert(boolean bb, boolean b) { /*@ assume b; */ /*@ assert false;*/   } // Should fail because of the explicit assert false
                  //@ requires bb;
                  //@ ensures true;
                  public static void bassert2(boolean bb, boolean b) { /*@ assume b; */ /*@ assert !bb;*/   } // Should fail because of the tautologically false assert
                  //@ requires bb;
                  //@ ensures true;
                  public static void bassert3(boolean bb, boolean b) { /*@ assume bb; */ /*@ assert b;*/   } // Should fail because of the unprovable assert
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method bassert", 76
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method bassert2",77
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method bassert3",78
                );
    }


    @Test   // FIXME - bassumeCHAIN1 times out 
    public void testAssume() {
        addOptions("--check-feasibility=basic");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { public static final int z = 0;
                  //@ requires bb;
                  //@ ensures true;
                  public static void bassumeBADASSUMP(boolean bb) { /*@assume z==1 ;*/  /*@ assert false; */ } // Should succeed despite the false assert
                  //@ requires bbb;
                  public static void bifOK(boolean bb,boolean b, boolean bbb) { /*@assume true;*/ if (bb) { /*@assume !b;*/ /*@ assert !bb; */ }  }
                  //@ requires b;
                  public static void bifBAD(boolean bb,boolean b) { /*@assume true;*/ if (bb) { /*@assume !b;*/ /*@ assert !bb; */ }  }
                  //@ requires bb;
                  //@ ensures true;
                  public static void bassumeBADASSUMP2(boolean bb) { int x = 1; /*@assume 0==x ;*/  /*@ assert true; */ } // Should succeed despite the false assert

                  public static void bassumeCHAIN2(boolean bb, boolean b) { if (bb) { /*@assume bb; assume !bb; */ b = true; /* @ assert false; */ } }
                  public static void bassumeMULT(boolean bb, boolean b) { if (bb) { /*@assume bb; assume !bb; */ b = true; /* @ assert false; */ } else { /*@assume bb; assume !bb; */ b = true; /* @ assert false; */} }
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeBADASSUMP(boolean)",56
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.bassumeBADASSUMP(boolean)",77
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point at program exit in method tt.TestJava.bassumeBADASSUMP(boolean)",94
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method bifOK",113
                ,"/tt/TestJava.java:9: verify: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bifBAD(boolean,boolean)",84
                ,"/tt/TestJava.java:9: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.bifBAD(boolean,boolean)",101
                ,"/tt/TestJava.java:12: verify: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeBADASSUMP2(boolean)",68
                ,"/tt/TestJava.java:12: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.bassumeBADASSUMP2(boolean)",89
                ,"/tt/TestJava.java:12: verify: There is no feasible path to program point at program exit in method tt.TestJava.bassumeBADASSUMP2(boolean)",105
                // The following error is required, but can occur before or
                // after the error on the same line
//                ,anyorder(
//                seq("/tt/TestJava.java:13: verify: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeCHAIN1(boolean,boolean)",87)
//                ,seq("/tt/TestJava.java:13: verify: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeCHAIN1(boolean,boolean)",75)
//                )
                ,"/tt/TestJava.java:14: verify: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeCHAIN2(boolean,boolean)",85
                // The following error is required, but can occur before or
                // after the error on the same line
                ,anyorder(
                seq("/tt/TestJava.java:15: verify: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeMULT(boolean,boolean)",83)
                ,seq("/tt/TestJava.java:15: verify: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeMULT(boolean,boolean)",142)
                )
                ,"/tt/TestJava.java:15: verify: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeMULT(boolean,boolean)",153
                ,"/tt/TestJava.java:15: verify: There is no feasible path to program point at program exit in method tt.TestJava.bassumeMULT(boolean,boolean)",201
                );
    }

    @Ignore // FIXME - rejuvenate dead branch detection some time
    @Test
    public void testDeadBranch() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //static int ii;
                  public static void bok(boolean b, int i) { if (b) i = 7; else i = 9; }
                  public static void bok2(boolean b, int i, int ii) { if (b) i = 7; else i = 9; if (b) ii = 7; else ii = 9; }
                  public static void bdead(boolean b, int i) { /*@ assume b; */ if (b) i = 7; else i = 9; }
                  public static void bdeadelse(boolean b, int i) { /*@ assume !b; */ if (b) i = 7; else i = 9; }
                }
                """,
                "/tt/TestJava.java:6: verify: else branch apparently never taken in method tt.TestJava.bdead(boolean,int)",
                69,
                "/tt/TestJava.java:7: verify: then branch apparently never taken in method tt.TestJava.bdeadelse(boolean,int)",
                73);
    }

    @Test
    public void testDecl() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void bok() { int k = 0; /*@ assert k == 0; */ }
                  public static void bfalse() { int k = 0; /*@ assert k != 0; */ }
                }
                """,
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method bfalse", 48);
    }

    // FIXME - rejuvenate dead branch detection
    @Test
    public void testIncarnations() {
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void bnotok() { int k = 10; int i = 0; i = 1; i = k; k = 5; k = i+k; /*@ assert i == 10; assert k == 16; */} // We want to be sure it fails
                  public static void bifok(boolean b) { int k = 10; if (b) { k = k+1; if (b) k = k-1; else k = k+1; } else { k=k-1; if (b) k=k-1; else k=k+1; } /*@ assert k == 10; */}
                  public static void bifbad(boolean b) { int k = 10; if (b) { k = k+1; if (b) k = k-1; else k = k+1; } else { k=k-1; if (b) k=k-1; else k=k+1; } /*@ assert k == 11; */} // We want to be sure it fails
                  public static void bifbad2(boolean b) { int k = 10; if (b) { k = k+1; if (!b) k = k+1; } else { k=k-1; if (b) {k=k-1; b = false; } } /*@ assert k == 11; */} // We want to be sure it fails
                }
                """,
                "/tt/TestJava.java:3: verify: The prover cannot establish an assertion (Assert) in method bnotok", 106,
                // The following error is required, but the order is arbitrary
                // "/tt/TestJava.java:4: verify: else branch apparently never
                // taken in method tt.TestJava.bifok(boolean)", -75,
                // "/tt/TestJava.java:4: verify: then branch apparently never
                // taken in method tt.TestJava.bifok(boolean)", 120,
                // "/tt/TestJava.java:4: verify: else branch apparently never
                // taken in method tt.TestJava.bifok(boolean)", -75,
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method bifbad", 150,
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method bifbad2",
                140);
    }

    


    @Test
    public void testNewCompares() { // Just checks parsing
        expectedExit = 0;
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_java_math spec_java_math*/ public class TestJava {
                  public static void bok1(int i) { /*@ assert i <<< i || true; */ }
                  public static void bok2(int i) { /*@ assert i <<<= i || true; */ }
                }
                """
                );
    }

    @Test
    public void testReturn() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires 0<=ii && ii <=3;
                  //@ ensures ii<=0 ==> \\result ==-ii;
                  public static int bok(int ii) { if (ii==1) return -1; else if (ii==2) return -2; else if (ii==3) return -3; return 0; }
                  //@ requires ii > -2147483648; // Not using system specs
                  //@ ensures \\result == -ii;
                  public static int bbad(int ii) { if (ii==1) return -1; else if (ii==2) return -2; else if (ii==3) return -3; return 0; }
                }
                """,
                "/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Postcondition) in method bbad",
                112, "/tt/TestJava.java:7: verify: Associated declaration", 7);
    }

    @Test
    public void testThrow() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void bok(int i) { if (i == 0) throw new RuntimeException(); /*@ assert i!=0; */ }
                  public static void bbad(int i) { if (i == 0) throw new RuntimeException(); /*@ assert i==0; */ }
                }
                """,
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method bbad", 82);
    }

    @Test
    public void testNonNull() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ requires ii == 10;
                  //@ ensures true;
                  public /*@ non_null */Object inst(int ii) { return null; }
                  //@ requires ii == 10;
                  //@ ensures true;
                  public @NonNull Object inst2(int ii) {  return null; }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method inst",25
                ,"/tt/TestJava.java:5: verify: Associated declaration",32
                , "/tt/TestJava.java:5: verify: Associated method exit", 47
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method inst2",19
                ,"/tt/TestJava.java:8: verify: Associated declaration",26
                , "/tt/TestJava.java:8: verify: Associated method exit", 43
                );
    }

    @Test
    public void testNonNull2() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ requires ii == 10;
                  //@ ensures true;
                  public Object inst(int ii) { return null; }
                  //@ requires ii == 10;
                  //@ ensures true;
                  public Object inst2(int ii) { return null; }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method inst",10
                ,"/tt/TestJava.java:5: verify: Associated declaration",17
                , "/tt/TestJava.java:5: verify: Associated method exit", 32
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method inst2",10
                ,"/tt/TestJava.java:8: verify: Associated declaration", 17
                , "/tt/TestJava.java:8: verify: Associated method exit", 33
                );
    }

    @Test
    public void testNonNull3() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @NonNullByDefault public class TestJava {
                  //@ requires ii == 10;
                  //@ ensures true;
                  public Object inst(int ii) { return null; }
                  //@ requires ii == 10;
                  //@ ensures true;
                  public Object inst2(int ii) {  return null; }
                }
                """
                        ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method inst",10
                        ,"/tt/TestJava.java:5: verify: Associated declaration", 17
                        ,"/tt/TestJava.java:5: verify: Associated method exit", 32
                        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method inst2",10
                        ,"/tt/TestJava.java:8: verify: Associated declaration", 17
                        ,"/tt/TestJava.java:8: verify: Associated method exit", 34
                        );
    }

    // FIXME - the non-null return postcondition error message is not very clear
    // (it is actually assigning null to a nonnull return value)

    @Test
    public void testNonNull4() {
        addOptions("--nullable-by-default=false");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ requires ii == 10;
                  //@ ensures true;
                  public Object inst(int ii) { return null; }
                  //@ requires ii == 10;
                  //@ ensures true;
                  public Object inst2(int ii) {  return null; }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method inst",10
                ,"/tt/TestJava.java:5: verify: Associated declaration", 17
                ,"/tt/TestJava.java:5: verify: Associated method exit", 32
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method inst2",10
                ,"/tt/TestJava.java:8: verify: Associated declaration", 17
                ,"/tt/TestJava.java:8: verify: Associated method exit", 34
                );
    }

    // Tests that a cast is nonnull if the argument is
    @Test
    public void testNonNull5() {
        addOptions("--nullable-by-default=false");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public Integer inst() {
                    @NonNull Object o = Integer.valueOf(0);
                    @NonNull Integer i = (Integer)o;
                    return i;
                  }
                  public Integer inst1() {
                    @Nullable Object o = Integer.valueOf(0);
                    @NonNull Integer i = (Integer)o;
                    return i;
                  }
                  public Integer inst2() {
                    @Nullable Object o = null;
                    @NonNull Integer i = (Integer)o;
                    return i;
                  }
                }
                """
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (PossiblyNullInitialization) in method inst2: i",22
                );
    }

    @Test
    public void testNonNullParam() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public /*@ non_null*/Object inst(boolean b, /*@ non_null */Object i, Object ii) { return i; }
                  public /*@ non_null*/Object instbad(boolean b, /*@ non_null */Object i, Object ii) { return ii; }
                  public /*@ non_null*/Object inst2(boolean b, @NonNull Object i, Object ii) { return i; }
                  public /*@ non_null*/Object inst2bad(boolean b, @NonNull Object i, Object ii) { return ii; }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method instbad",24
                ,"/tt/TestJava.java:6: verify: Associated declaration",31
                , "/tt/TestJava.java:6: verify: Associated method exit", 88
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyNullReturn) in method inst2bad",24
                ,"/tt/TestJava.java:10: verify: Associated declaration",31
                , "/tt/TestJava.java:10: verify: Associated method exit", 83
                );
    }

    @Test
    public void testNonNullParamNL() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ ensures \\result != null;
                  public Object inst(boolean b, /*@ non_null */Object i, Object ii) { return i; }
                  //@ ensures \\result != null;
                  public Object instbad(boolean b, /*@ non_null */Object i, Object ii) { return ii; }
                  //@ ensures \\result != null;
                  public Object inst2(boolean b, @NonNull Object i, Object ii) { return i; }
                  //@ ensures \\result != null;
                  public Object inst2bad(boolean b, @NonNull Object i, Object ii) { return ii; }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method instbad",74
                ,"/tt/TestJava.java:5: verify: Associated declaration", 7
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Postcondition) in method inst2bad",69
                ,"/tt/TestJava.java:9: verify: Associated declaration", 7

        );
    }

    @Test
    public void testNonNullParamNL2() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public Object inst(boolean b, /*@ non_null */Object i, Object ii) { return i; }
                  public Object instbad(boolean b, /*@ non_null */Object i, Object ii) { return ii; }
                  public Object inst2(boolean b, @NonNull Object i, Object ii) { return i; }
                  public Object inst2bad(boolean b, @NonNull Object i, Object ii) { return ii; }
                }
                """

        );
    }

    @Test
    public void testNonNullParam2() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                    //@ ensures \\result != null;
                    public /*@ nullable*/Object inst(boolean b, Object i, /*@ nullable*/Object ii) { return i; }
                    //@ ensures \\result != null;
                    public /*@ nullable*/Object instbad(boolean b, Object i, /*@ nullable*/Object ii) { return ii; }
                    //@ ensures \\result != null;
                    public /*@ nullable*/Object inst2(boolean b, Object i, /*@ nullable*/Object ii) { return i; }
                    //@ ensures \\result != null;
                    public /*@ nullable*/Object inst2bad(boolean b, Object i, /*@ nullable*/Object ii) { return ii; }
                }
                """
                , "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method instbad", 89
                , "/tt/TestJava.java:5: verify: Associated declaration", 9
                , "/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Postcondition) in method inst2bad",90
                , "/tt/TestJava.java:9: verify: Associated declaration", 9
                );
    }

    @Test
    public void testNonNullParam3() {
        addOptions("--nullable-by-default=false");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                @NonNullByDefault public class TestJava {
                  //@ ensures \\result != null;
                  public /*@ nullable*/Object inst(boolean b,                Object i, /*@ nullable*/Object ii) { return i; }
                  //@ ensures \\result != null;
                  public /*@ nullable*/Object instbad(boolean b,                Object i, /*@ nullable*/Object ii) { return ii; }
                  //@ ensures \\result != null;
                  public /*@ nullable*/Object inst2(boolean b,          Object i, /*@ nullable*/Object ii) { return i; }
                  //@ ensures \\result != null;
                  public /*@ nullable*/Object inst2bad(boolean b,          Object i, /*@ nullable*/Object ii) { return ii; }
                }
                """,
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method instbad",
                102, "/tt/TestJava.java:5: verify: Associated declaration", 7,
                "/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Postcondition) in method inst2bad",
                97, "/tt/TestJava.java:9: verify: Associated declaration", 7);
    }

    @Test
    public void testNonNullParam4() {
        addOptions("--nullable-by-default=false");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ ensures \\result != null;
                  public /*@ nullable*/Object inst(boolean b,                Object i, /*@ nullable*/Object ii) { return i; }
                  //@ ensures \\result != null;
                  public /*@ nullable*/Object instbad(boolean b,                Object i, /*@ nullable*/Object ii) { return ii; }
                  //@ ensures \\result != null;
                  public /*@ nullable*/Object inst2(boolean b,          Object i, /*@ nullable*/Object ii) { return i; }
                  //@ ensures \\result != null;
                  public /*@ nullable*/Object inst2bad(boolean b,          Object i, /*@ nullable*/Object ii) { return ii; }
                }
                """,
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method instbad",
                102, "/tt/TestJava.java:5: verify: Associated declaration", 7,
                "/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Postcondition) in method inst2bad",
                97, "/tt/TestJava.java:9: verify: Associated declaration", 7);
    }

    @Test
    public void testMethodCall() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  static public int j;
                  //@ requires i>0;
                  //@ assigns j;
                  //@ ensures j == -i;
                  static public void m(int i) { j = -i; }
                  //@ requires i>1;
                  //@ assigns j;
                  //@ ensures \\result == -i;
                  public int inst(boolean b, int i) { m(i); return j; }
                  //@ assigns j;
                  //@ ensures \\result == j;
                  public int instbad(boolean b, int i) { m(i); return j; }
                  //@ assigns j;
                  //@ ensures \\result == i;
                  public int instbad2(boolean b, int i) { m(1); return j; }
                }
                """
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Precondition) in method instbad",43
                ,"/tt/TestJava.java:7: verify: Associated declaration", 22
                ,"/tt/TestJava.java:4: verify: Precondition conjunct is false: i > 0",17
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Postcondition) in method instbad2",49
                , "/tt/TestJava.java:16: verify: Associated declaration", 7
                );
    }

    @Test
    public void testMethodCall2() { // Had problems with static and non-static
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public int j;
                  //@ requires i>0;
                  //@ assigns j;
                  //@ ensures j == -i;
                  public void m(int i) { j = -i; }
                  //@ requires i>1;
                  //@ assigns j;
                  //@ ensures \\result == -i;
                  public int inst(boolean b, int i) { m(i); return j; }
                  //@ assigns j;
                  //@ ensures \\result == j;
                  public int instbad(boolean b, int i) { m(i); return j; }
                  //@ assigns j;
                  //@ ensures \\result == i;
                  public int instbad2(boolean b, int i) { m(1); return j; }
                }
                """
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Precondition) in method instbad",43
                , "/tt/TestJava.java:7: verify: Associated declaration",15
                ,"/tt/TestJava.java:4: verify: Precondition conjunct is false: i > 0",17
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Postcondition) in method instbad2",49
                , "/tt/TestJava.java:16: verify: Associated declaration", 7);
    }

    @Test
    public void testMethodCallRet() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                /*@ code_bigint_math*/ public class TestJava {
                  static public int j;
                  //@ requires i>0;
                  //@ assigns j;
                  //@ ensures j == i+1 && \\result == j;
                  static public int m(int i) { j = i+1; return j; }
                  //@ requires i>1;
                  //@ assigns j;
                  //@ ensures \\result == \\old(i)+1;
                  public int inst(boolean b, int i) { m(i); m(i); m(i); return j; }
                  //@ requires i>1;
                  //@ assigns j;
                  //@ ensures \\result == \\old(i)+3;
                  public int inst2(boolean b, int i) { m(m(m(i))); return j; }
                  //@ requires i>1;
                  //@ assigns j;
                  //@ ensures \\result == 3*i+4;
                  //@ ensures j == i + 1;
                  public int inst3(boolean b, int i) { return m(m(i) + m(i)) + m(i); }
                  //@ requires i>1;
                  //@ assigns j;
                  //@ ensures \\result == \\old(i);
                  public int instx(boolean b, int i) { m(i); m(i); m(i); return j; }
                  //@ requires i>1;
                  //@ assigns j;
                  //@ ensures \\result == \\old(i)+4;
                  public int instx2(boolean b, int i) { m(m(m(i))); return j; }
                  //@ requires i>1;
                  //@ assigns j; // Line 30
                  //@ ensures \\result == 3*i+4;
                  //@ ensures j == i + 2;
                  public int instx3(boolean b, int i) { return m(m(i) + m(i)) + m(i); }
                }
                """
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Postcondition) in method instx",58
                ,"/tt/TestJava.java:23: verify: Associated declaration", 7
                ,"/tt/TestJava.java:28: verify: The prover cannot establish an assertion (Postcondition) in method instx2",53
                ,"/tt/TestJava.java:27: verify: Associated declaration", 7
                ,"/tt/TestJava.java:33: verify: The prover cannot establish an assertion (Postcondition) in method instx3",41
                ,"/tt/TestJava.java:32: verify: Associated declaration", 7
        );
    }

    @Test // FIXME - problem with maintaining result of j
    public void testMethodCallThis() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                /*@ code_java_math*/ public class TestJava {
                  public static TestJava o;
                  public static TestJava p;
                  public int j; static public int sj;
                  //@ assignable \\nothing; ensures \\result == j;
                  public int m() { return j; }
                  //@ assigns j,sj;
                  //@ ensures \\result == \\old(j);
                  public int nold() { return j; }
                  //@ assigns j,sj;
                  //@ ensures \\result == j;
                  public int n() { return j; }
                  //@ assigns j,sj;
                  //@ ensures \\result == sj;
                  public int sn() { return sj; }
                  //@ requires o!=null && p != null && o.j == 1 && p.j == 2 && j == 3;
                  //@ assigns j,sj,o.j,o.sj,p.j,p.sj;
                  //@ ensures \\result == 6;
                  public int inst() { return o.m() + p.m() + j; } // Line 20
                  //@ requires o!=null && p != null && o.j == 1 && p.j == 2 && j == 3 && o!=this && p!= this;
                  //@ assigns j,sj,o.j,o.sj,p.j,p.sj;
                  //@ ensures \\result == 6;
                  public int instok() { int jj = j; /*@ assert (\\lbl OJ o.j) + (\\lbl PJ p.j) + (\\lbl JJ j) == 6; */ return o.nold() + p.nold() + jj; } // o.n and p.n modify o.j and p.j, returned value is before mod
                  //@ requires o!=null && p != null && o.j == 1 && p.j == 2 && j == 3;
                  //@ assigns j,sj,o.j,o.sj,p.j,p.sj;
                  //@ ensures \\result == 6;
                  public int instbadx() { return o.n() + p.n() + j; } // returned value is after modification
                  //@ assigns j,sj;
                  //@ ensures \\result == 6;
                  public int instbad() { return n() + j; } // n() assigns this.j
                  //@ requires o!=null && p != null && sj == 3;
                  //@ assigns j,sj,o.j,o.sj,p.j,p.sj;
                  //@ ensures \\result == 9;
                  public int instbad2() { return o.sn() + p.sn() + sj; }
                }
                """
                ,"/tt/TestJava.java:28: verify: The prover cannot establish an assertion (Postcondition) in method instbadx",27
                ,"/tt/TestJava.java:27: verify: Associated declaration", 7
                ,"/tt/TestJava.java:31: verify: The prover cannot establish an assertion (Postcondition) in method instbad",26
                ,"/tt/TestJava.java:30: verify: Associated declaration", 7
                ,"/tt/TestJava.java:35: verify: The prover cannot establish an assertion (Postcondition) in method instbad2",27
                ,"/tt/TestJava.java:34: verify: Associated declaration", 7
                );
    }

    // TODO need tests for for loops
    // TODO need tests for do loops

    // TODO - more tests needed, and with specs

    @Test
    public void testForeachSpecs() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ requires \\nonnullelements(a);
                  public void inst(int[] a) {
                    boolean b = false;
                    //@ assume a != null && a.length > 2 && a[1] == 1;
                    //@ loop_invariant b == \\exists int k; 0 <= k < \\count; a[k] > 0;
                    for(int i: a) if (i > 0) b = true;
                    //@ assert b ==> a[1] > 0;
                  }
                }
                """);
    }

    @Test
    public void testForLoopSpecs() { // FIXME - want error position at the end
                                        // of the statement that is the loop
                                        // body
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst() { int n = 0; /*@ loop_invariant 0<=i && i<=5 && n==i; decreases 5-i; */ for (int i=0; i<5; i++) n++; /*@ assert n == 5; */ }
                  public void instb() { int n = 0; /*@ loop_invariant 0<=i && i<=5 && n==i; decreases 3-i; */ for (int i=0; i<5; i++) n++; /*@ assert n == 5; */ }
                  public void instc() { int n = 0; /*@ loop_invariant 0<=i && i<5 && n==i; decreases 5-i; */ for (int i=0; i<5; i++) n++; /*@ assert n == 5; */ }
                  public void instd() { int n = 0; /*@ loop_invariant 0<=i && i<=5 && n==i-1; decreases 5-i; */ for (int i=0; i<5; i++) n++;  }
                }
                """,
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (LoopDecreasesNonNegative) in method instb",
                77// 119
                // ,"/tt/TestJava.java:4: verify: Associated declaration",77
                ,
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (LoopInvariant) in method instc",
                40// 118
                // ,"/tt/TestJava.java:5: verify: Associated declaration",40
                ,
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (LoopInvariantBeforeLoop) in method instd",
                40// 97
        // ,"/tt/TestJava.java:6: verify: Associated declaration",40
        // FIXME - fix references
        );
    }
    
    @Test
    public void testForInits() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    //@ loop_assigns i;
                    for (int i=0, j=0; i<5; i++) {
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:5: warning: Loop variable j is not modified in the loop",19
                );
    }

    @Test
    public void testDoWhileSpecs() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                 public class TestJava {
                  public void inst() { int i = 5; /*@ loop_invariant i>0; decreases i; */ do { i = i-1; } while (i>0); /*@ reachable; */ }
                  public void instb() { int i = 5; /*@ loop_invariant i>=0; decreases i-2; */ do  i = i+1;  while (i>0); /*@ assert i == 0; */ }
                  public void instc() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ do { i = i+1; } while (i>0); /*@ assert i == 0; */ }
                }
                """,
                anyorder(
                        seq("/tt/TestJava.java:3: verify: The prover cannot establish an assertion (LoopInvariantAfterLoop) in method inst", 39),
                        seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (LoopDecreasesNonNegative) in method instb",
                                61),
                        seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (LoopDecreases) in method instb",
                                61),
                        seq("/tt/TestJava.java:5: verify: The prover cannot establish an assertion (LoopDecreases) in method instc",
                                61)));
    }

    @Test
    public void testDoWhileSpecsJava() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                /*@ code_java_math */ public class TestJava {
                  public void inst() { int i = 5; /*@ loop_invariant  i>0; decreases i; */ do { i = i-1; } while (i>0); /*@ assert i == 0; */ }
                  /*@ code_bigint_math */public void instb() { int i = 5; /*@ loop_invariant i>=0; decreases i-2; */ do  i = i+1;  while (i>0); /*@ assert i == 0; */ }
                  /*@ code_bigint_math */public void instc() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ do { i = i+1; } while (i>0); /*@ assert i == 0; */ }
                }
                """,
                anyorder(
                        seq("/tt/TestJava.java:3: verify: The prover cannot establish an assertion (LoopInvariantAfterLoop) in method inst", 39),
                        seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (LoopDecreasesNonNegative) in method instb",
                                84),
                        seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (LoopDecreases) in method instb",
                                84),
                        seq("/tt/TestJava.java:5: verify: The prover cannot establish an assertion (LoopDecreases) in method instc",
                                84)));
    }
    
    @Test
    public void testShift() {
        addOptions("--code-math=safe");
        helpEsc("tt.TestJava", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class TestJava {
                    //@ ensures k == 1 ==> \\result == 256;
                    public int inst1(int k) { return k << 40; }
                    //@ ensures k == 1 ==> \\result == 0x8000_0000L; // CAUTION: No negative int value
                    public int inst2(int k) { return k << -1; }
                    //@ ensures k == 1 ==> \\result == 64;
                    public long inst3(long k) { return k << 6; }
                    //@ ensures k == 1 ==> \\result == 64;
                    public long inst3a(long k) { return k << 70; }
                    //@ ensures k == 1 ==> \\result == 65; // ERROR
                    public long inst3b(long k) { return k << 6; }
                    //@ ensures k == 1 ==> \\result == 65; // ERROR
                    public long inst3c(long k) { return k << 70; }
                    //@ ensures k == 1 ==> \\result == 2 * 0x4000_0000_0000_0000L; // CAUTION: Avoid negative value
                    public long inst4(long k) { return k << -1; }
                    public void inst5(long k) { /*@ assert 0 == (\\bigint)27 << -1; */} // ERROR
                    public void inst6(long k) { /*@ assert 13 == (\\bigint)27 << -1; */} // OK
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyLargeShift) in method inst1",40
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyLargeShift) in method inst2",40
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (PossiblyLargeShift) in method inst3a",43
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Postcondition) in method inst3b",34
                ,"/tt/TestJava.java:12: verify: Associated declaration",9
                ,anyorder(
                    seq("/tt/TestJava.java:15: verify: The prover cannot establish an assertion (PossiblyLargeShift) in method inst3c",43)
                    ,seq(
                            "/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Postcondition) in method inst3c",34
                            ,"/tt/TestJava.java:14: verify: Associated declaration",9
                    ))
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (PossiblyLargeShift) in method inst4",42
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Assert) in method inst5",37
                );
    }



    @Test
    public void testAssignOp() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst1() { int i = 5; i+=7; /*@ assert i == 12; */ }
                  public void inst1b() { int i = 5; i+=7; /*@ assert i == 5; */ }
                  public void inst1c() { int i = 5; int j = (i+=7); /*@ assert i == 12 && i == j; */ }
                  public void inst1d() { int i = 5; int j = (i+=7); /*@ assert i == 5; */ }
                  public void inst2() { int i = 5; i-=7; /*@ assert i == -2; */ }
                  public void inst2b() { int i = 5; i-=7; /*@ assert i == 5; */ }
                  public void inst2c() { int i = 5; int j = (i-=7); /*@ assert i == -2 && i == j; */ }
                  public void inst2d() { int i = 5; int j = (i-=7); /*@ assert i == 5; */ }
                  public void inst3() { int i = 5; i*=7; /*@ assert i == 5*7; */ }
                  public void inst3b() { int i = 5; i*=7; /*@ assert i == 5; */ }
                  public void inst3c() { int i = 5; int j = (i*=7); /*@ assert i == 5*7 && i == j; */ }
                  public void inst3d() { int i = 5; int j = (i*=7); /*@ assert i == 5; */ }
                  public void inst4() { int i = 5; i/=7; /*@ assert i == 5/7; */ }
                  public void inst4b() { int i = 5; i/=7; /*@ assert i == 5; */ }
                  public void inst4c() { int i = 5; int j = (i/=7); /*@ assert i == 5/7 && i == j; */ }
                  public void inst4d() { int i = 5; int j = (i/=7); /*@ assert i == 5; */ }
                }
                """,
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method inst1b", 47,
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method inst1d", 57,
                "/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method inst2b", 47,
                "/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method inst2d", 57,
                "/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method inst3b", 47,
                "/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Assert) in method inst3d", 57,
                "/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Assert) in method inst4b", 47,
                "/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Assert) in method inst4d",
                57); // TODO - need %= <<= >>= >>>= &= |= ^=
    }

    @Test
    public void testConditional() {
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ requires i > -2147483648;
                  public void inst1(int i) { int j = i<0?-i:i; /*@ assert j >= 0; */ }
                  //@ requires i > -2147483648;
                  public void inst1a(int i) { int j = i<0?-i:i; /*@ assert j == -1; */ }
                }
                """,
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method inst1a", 53);
    }

    @Test
    public void testLblx() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst1(int i) { /*@ assume i > 0; */ /*@ assert (\\lblpos ISP i>0); */} // no report
                  public void inst1a(int i) { /*@ assume i > 0; */ /*@ assert (\\lblneg ISN i<0); */} // reported
                  public void inst1b(int i) { /*@ assume i > 0; */ /*@ assert !(\\lblneg ISN2 i>0); */} // no report
                  public void inst1c(int i) { /*@ assume i > 0; */ /*@ assert (\\lblpos ISP i<0); */} // no report
                  public void inst1d(int i) { /*@ assume i > 0; */ /*@ assert !(\\lblpos ISP2 i>0); */} // reported
                }
                """,
                "/tt/TestJava.java:4: verify: Label ISN has value false", 72,
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method inst1a", 56,
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method inst1b", 56,
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method inst1c", 56,
                "/tt/TestJava.java:7: verify: Label ISP2 has value true", 73,
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method inst1d", 56);
    }

    @Test
    public void testNewObject() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst1() { Object o = new Object(); Object oo = new Object(); /*@ assert o != oo;*/ }
                  public void inst1a() { Object o = new Object(); Object oo = new Object(); /*@ assert o == oo;*/ }
                  public void inst2() { Object o = new Object(); /*@ assert o != null;*/ }
                  public void inst2a() { Object o = new Object(); /*@ assert o == null;*/ }
                }
                """,
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method inst1a", 81,
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method inst2a", 55);
    }

    @Test
    public void testNewArray() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst1() { Object o = new int[5]; Object oo = new int[5]; /*@ assert o != oo;*/ }
                  public void inst1a() { Object o = new int[5]; Object oo = new int[5]; /*@ assert o == oo;*/ } // FALSE
                  public void inst2() { int[] o = new int[5]; /*@ assert o != null; assert o.length == 5; */ }
                  public void inst2a() { int[] o = new int[5]; /*@ assert o.length == 6;*/ } // FALSE
                  public void inst3(int/*@non_null*/[] a) { /*@ assert a.length >= 0;*/ }
                  public void inst5() { Object o = new boolean[5]; Object oo = new boolean[5]; /*@ assert o != oo;*/ }
                  public void inst5a() { Object o = new boolean[5]; Object oo = new boolean[5]; /*@ assert o == oo;*/ } // FALSE
                }
                """,
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method inst1a", 77,
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method inst2a", 52,
                "/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method inst5a", 85);
    }

    @Test
    public void testNewArrayInit() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst4() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 3; assert o[1] == 11;*/ }
                  public void inst4a() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 4; */ }
                  public void inst4b() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 3; assert o[1] == 10;*/ }
                  public void inst6() { int[] o = {10,11,12}; /*@ assert o != null; assert o.length == 3; assert o[1] == 11;*/ }
                }
                """,
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method inst4a", 61,
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method inst4b", 83);
    }

    @Test
    public void testNewArrayInit2() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst4() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o.length == 3; assert o[1] != null; assert o[1].length == 3; assert o[1][2] == 14; assert o[0] != null; assert o[0].length == 2; assert o[0][1] == 11; */ }
                  public void inst5() { int[][] o = {{10,11},{12,13,14},{15}}; /*@ assert o.length == 3; assert o[1] != null; assert o[1].length == 3; assert o[1][2] == 14; assert o[0] != null; assert o[0].length == 2; assert o[0][1] == 11; */ }
                  public void inst6() { int[][] o = {{10,11},null,{15}}; /*@ assert o.length == 3; assert o[1] == null; assert o[2] != null; assert o[2].length == 1; assert o[2][0] == 15; */ }
                }
                """);
    }

    @Test
    public void testNewArrayMD1() {
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst0() { Object o = new int[2][3]; o = new int[2][]; o = new int[][] {{2}, {3,4,5}}; int[][] oo = {{1},{2,3}}; /*@ assert oo[0] != oo[1]; */}
                  public void inst1() { Object o = new int[5][3]; Object oo = new int[5][3]; /*@ assert o != oo;*/ }
                  public void inst1a() { Object o = new int[5][3]; Object oo = new int[5][3]; /*@ assert o == oo;*/ } // FALSE
                  public void inst2() { int[][] o = new int[5][3]; /*@ assert o.length == 5; assert o[1].length == 3; */ }
                  public void inst2a() { int[][] o = new int[5][3]; /*@ assert o.length == 6;*/ } // FALSE
                  public void inst2b() { int[][] o = new int[5][3]; /*@ assert o[1].length == 4;*/ } // FALSE
                }
                """,
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method inst1a", 83,
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method inst2a", 57,
                "/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method inst2b", 57);
    }

    @Test
    public void testNewArrayMD2() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst3(int/*@non_null*/[][] a) { /*@ assert a.length >= 0;*/ }
                  public void inst4() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o.length == 3; */ }
                  public void inst4a() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o.length == 2; */ } // FALSE
                  public void inst5() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[1][2] == 14; */ }
                  public void inst6() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[2].length == 1; */ }
                  public void inst7() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[0].length == 2; */ }
                  public void inst8() { int[][] o = new int[5][]; /*@ assert o != null; assert o.length == 5; assert o[1] == null; */ }
                }
                """,
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method inst4a", 80);
    }

    @Test
    public void testArrays() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst2(int/*@non_null*/[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  /*@ assert a[1] == 2; */ } // OK
                  public void inst2a(int/*@non_null*/[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  /*@ assert a[1] == 3; */ } // BAD
                  public void inst3(int/*@non_null*/[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */ } // OK
                  public void inst3a(int/*@non_null*/[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 4; */ } // BAD
                  public void inst4(int/*@non_null*/[] a) { /*@assume a.length == 10;*//*@ assume a[0] == 2; */  a[1] = 3; /*@ assert a[0] == 2; */ } // OK
                  public void inst4a(int/*@non_null*/[] a) { /*@assume a.length == 10;*//*@ assume a[0] == 2; */  a[1] = 3; /*@ assert a[0] == 4; */ } // BAD
                  public void inst5(int/*@non_null*/[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */  a[1] = 4; /*@ assert a[1] == 4; */} // OK
                  public void inst5a(int/*@non_null*/[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */  a[1] = 4; /*@ assert a[1] == 5; */} // BAD
                  public void inst6(int/*@non_null*/[] a, int/*@non_null*/[] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] == b[0]; */} // OK
                  public void inst6a(int/*@non_null*/[] a, int/*@non_null*/[] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] != b[0]; */} // BAD
                  public void inst7(int/*@non_null*/[] a, int/*@non_null*/[] b) { /*@ assume b.length == 10 && a.length == 10;*/ b[0] = 0; b = a; a[0] = 7; /*@ assert b[0] == 7; */} // OK
                  public void inst7a(int/*@non_null*/[] a, int/*@non_null*/[] b) { /*@ assume b.length == 10 && a.length == 10;*/  b[0] = 0; b = a; a[0] = 7; /*@ assert b[0] == 8; */} // BAD
                  public void inst8(int/*@non_null*/[] a, int/*@non_null*/[] b) { /*@ assume b.length == 10 && a.length == 12;*/ b = a; a[0] = 5; /*@ assert b != null; assert a != null; assert b.length == 12; assert a.length == 12; */} // BAD
                }
                """,
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method inst2a", 103,
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method inst3a", 113,
                "/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method inst4a", 113,
                "/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method inst5a",
                149,
                "/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method inst6a",
                106,
                "/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Assert) in method inst7a",
                147);
    }

    @Test
    public void testArraysMD1() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst2(boolean/*@non_null*/[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  /*@ assert a[1][2]; */ } // OK
                  public void inst2a(boolean/*@non_null*/[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  /*@ assert !a[1][2]; */ } // BAD
                  public void inst3(boolean/*@non_null*/[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  a[1][2] = false; /*@ assert !a[1][2]; */ } // OK
                }
                """,
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method inst2a",
                154);
    }

    @Test
    public void testArraysMD4() { // In this test, the non_null says that 'a' is non_null; as the default is nullable a[0] might be null
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst3a(boolean/*@non_null*/[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  a[1][2] = true ; /*@ assert a[1][3]; */ } // BAD
                  public void inst3b(boolean/*@non_null*/[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  a[1][2] = true ; /*@ assert a[0][2]; */ } // BAD - a[0] might be null; even if it isn't a[0][2] is not necessarily true
                  public void inst3c(boolean/*@non_null*/[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; assume a[0] != null; */  a[1][2] = false; /*@ assert a[0][2]; */ } // BAD
                }
                """,
                "/tt/TestJava.java:3: verify: The prover cannot establish an assertion (Assert) in method inst3a", 171,
                anyorder(
                        seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method inst3b",
                                171),
                        seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method inst3b",
                                182),
                        seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method inst3b",
                                182)),
                anyorder(
                        seq("/tt/TestJava.java:5: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method inst3c",
                                203),
                        seq("/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method inst3c",
                                192)));
    }

    @Test
    public void testArraysMD5() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst3d(boolean/*@non_null*/[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; assume a[0] != null; assume a[0].length > 5; */  a[1][2] = false; /*@ assert a[0][2]; */ } // BAD
                  public void inst4(boolean/*@non_null*/[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[0] != null; assume a[1].length == 5; assume a[0].length == 3; *//*@ assume a[0][0]; */  a[1][0] = false; /*@ assert a[0][0]; */ } // OK
                  public void inst4a(boolean/*@non_null*/[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[0] != null; assume a[1].length == 5; assume a[0].length == 3; *//*@ assume a[0][0]; */  a[1][0] = false; /*@ assert !a[0][0]; */ } // BAD
                }
                """,
                "/tt/TestJava.java:3: verify: The prover cannot establish an assertion (Assert) in method inst3d", 216,
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method inst4a",
                217);
    }

    @Test
    public void testArraysMD2() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst5x(boolean/*@non_null*/[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; */  a[0] = a[1]; /*@ assert a[0][3] == a[1][3]; */} // OK
                  public void inst5a(boolean/*@non_null*/[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; */ a[0] = a[1]; /*@ assert a[0][3] != a[1][3]; ; */} // BAD
                  public void inst6(boolean/*@non_null*/[][] a, boolean/*@non_null*/[][] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] == b[0]; */} // OK
                  public void inst6a(boolean/*@non_null*/[][] a, boolean/*@non_null*/[][] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] != b[0]; */} // BAD
                }
                """,
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method inst5a", 144,
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method inst6a",
                118);
    }

    @Test
    public void testArraysMD3() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst7(boolean/*@non_null*/[][] a, boolean/*@non_null*/[][] b) { /*@ assume b.length == 10 && a.length == 10 && b[0] != null && a[0] != null && b[0].length == 5 && a[0].length==6;*/ b[0][0] = true; b = a; a[0][0] = false; /*@ assert !b[0][0]; */} // OK
                  public void inst7a(boolean/*@non_null*/[][] a, boolean/*@non_null*/[][] b) { /*@ assume b.length == 10 && a.length == 10 && b[0] != null && a[0] != null && b[0].length == 5 && a[0].length==6;*/  b[0][0] = true; b = a; a[0][0] = false; /*@ assert b[0][0]; */} // BAD
                  public void inst8(boolean/*@non_null*/[][] a, boolean/*@non_null*/[][] b) { /*@ assume b.length == 10 && a.length == 12;*/ b = a; a[0] = null; /*@ assert b != null; assert a != null; assert b.length == 12; assert a.length == 12; */} // OK
                }
                """,
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method inst7a",
                242);
    }
    
    // THESE WERE ALL COMMENTED OUT



    // FIXME - move to typechecking?
    
    @Test
    public void testdatagroup1() {
        helpEsc("tt.C",
                """
                package tt; /*@ non_null_by_default */ public class C {
                    //@ public model \\datagroup g;
                }
                """
                );
    }

    @Test
    public void testdatagroup2() {
        expectedExit = 1;
        helpEsc("tt.C",
                """
                package tt; /*@ non_null_by_default */ public class C {
                    //@ public model \\datagroup g;
                    public void m() {
                        //@ assert g != null;
                    }
                }
                """
                ,"/tt/C.java:4: error: No operator for \\datagroup != <nulltype>", 22
                );
    }

    @Test
    public void testdatagroup3() {
        expectedExit = 1;
        helpEsc("tt.C",
                """
                package tt; /*@ non_null_by_default */ public class C {
                    //@ public model \\datagroup g;
                    //@ public model \\datagroup gg;
                    public void m() {
                        //@ assert g == gg;
                    }
                }
                """
                ,"/tt/C.java:5: error: No operator for \\datagroup == \\datagroup", 22);
    }

    @Test
    public void testdatagroup4() {
        expectedExit = 1;
        helpEsc("tt.C",
                """
                package tt; /*@ non_null_by_default */ public class C {
                    //@ public model \\datagroup g;
                    //@ public model \\datagroup gg;
                    public void m() {
                        //@ assert !g == 0;
                        //@ assert g + gg == 0;
                    }
                }
                """
                ,"/tt/C.java:5: error: No operator for ! \\datagroup", 20
                ,"/tt/C.java:6: error: No operator for \\datagroup + \\datagroup", 22
                );
    }

    @Test
    public void testStaticInvariant1() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                    public static int i;
                    //@ public static invariant i == 0;
                    public static void m(boolean b) {
                        i = 1;
                        if (b) throw new RuntimeException();
                        i = 0;
                    }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (InvariantExit) in method m",16
                ,"/tt/TestJava.java:4: verify: Associated declaration",23
                );
    }
}
