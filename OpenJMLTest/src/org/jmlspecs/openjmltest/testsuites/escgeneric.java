package org.jmlspecs.openjmltest.testsuites;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** This class of JUnit tests checks various uses of generic types.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escgeneric extends EscBase {

    @Override
    public void setUp() throws Exception {
        //print = true;
        //noCollectDiagnostics = true;
        super.setUp();
        addOptions("--nullable-by-default"); // Because the tests were written this way
        //JmlEsc.escdebug = false;
        addOptions("--timeout=30");
    }
    
    @Test
    public void testConstructor() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void mx(Integer i) {\n"
                +"    Object oo = new TestG<Integer>(i);\n"
                +"  }\n"
                +"  public void ma(Object o) {\n"
                +"    Object oo = new TestG<Object>(o);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"  //@ requires \\type(E) != \\type(Integer) ; pure\n"
                +"  public TestG(E i) {}\n"
                +"}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method mx",17
                ,"/tt/TestJava.java:12: verify: Associated declaration",10
                ,"/tt/TestJava.java:11: verify: Precondition conjunct is false: \\type(E) != \\type(Integer)",25
                );
    }
    
    /** Tests that we can reason about the result of \\typeof */
    @Test
    public void testTypeOf() {
    	addOptions("--check-feasibility=all");  // Part of test
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m(Integer i) {\n"
                +"    //@ assert \\typeof(this) <:= \\type(TestJava);\n"
                +"  }\n"
                +"  public void ma(Object o) {\n"
                +"    //@ assume \\typeof(this) == \\type(Object);\n"
                +"    //@ assert false;\n" // should not trigger
                +"  }\n"
                +"  public void mb(Object o) {\n"
                +"    //@ assert \\typeof(this) == \\type(Object);\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:7: verify: There is no feasible path to program point after explicit assume statement in method tt.TestJava.ma(java.lang.Object)",9
                ,"/tt/TestJava.java:8: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.ma(java.lang.Object)",9
                ,"/tt/TestJava.java:6: verify: There is no feasible path to program point at program exit in method tt.TestJava.ma(java.lang.Object)",15
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method mb",9
                );
    }

    @Test
    public void testGenericType() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava<T> extends B<T> { \n"
                +"  public void ma(T i) {\n"
                +"  }\n"
                +"}\n"
                +"class A<T> extends TestJava<B<T>> { \n"
                +"  public void mb(T i) {\n"
                +"  }\n"
                +"}\n"
                +"class B<E> {}\n"
                +"class C<F> extends java.util.LinkedList<B<F>> {}\n"
        );
    }
    
    @Test
    public void testGenericType2() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava<T extends B> { \n"
                
                +"  public void m(T i) {\n"
                +"    //@ assume i != null;\n"
                +"    //@ check  i instanceof Object;\n"
                +"    //@ check  \\typeof(i) <:= \\type(Object);\n" // Line 6
                +"    //@ check  \\erasure(\\typeof(i)) <:= \\erasure(\\type(Object));\n"
                +"    //@ check  \\typeof(i) <:= \\type(T);\n"
                +"    //@ check  i instanceof B;\n"
                +"    //@ check  \\erasure(\\typeof(i)) <:= \\erasure(\\type(B));\n"
                +"    //@ check  \\typeof(i) <:= \\type(B);\n" // Line 11
                +"    //@ check  \\erasure(\\typeof(i)) <:= \\erasure(\\type(C));\n" // false
                +"  }\n"
                +"  /*@ public normal_behavior ensures true; pure */ public TestJava() {}\n"
                +"}\n"
                +"class B {}\n"
                +"class C extends TestJava<B> {}\n"
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method m",9
        );
    }
    
    @Test
    public void testGenericType2a() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava<T extends B> { \n"
                
                +"  public void m(T i) {\n"
                +"    //@ assume i != null;\n"
                +"    //@ assert i instanceof Object;\n"
                +"    //@ assert \\typeof(i) <:= \\type(C);\n" // false
                +"  }\n"
                +"  /*@ public normal_behavior ensures true; pure */ public TestJava() {}\n"
                +"}\n"
                +"class B {}\n"
                +"class C extends TestJava<B> {}\n"
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m",9
        );
    }
    
    @Test
    public void testGenericType2b() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava<T extends B> { \n"
                
                +"  public void m(T i) {\n"
                +"    //@ assume i != null;\n"
                +"    //@ assert i instanceof Object;\n"
                +"    //@ assert \\type(T) <:= \\type(B);\n" // true
                +"    //@ assert \\type(T) <:= \\type(C);\n" // false
                +"  }\n"
                +"  /*@ public normal_behavior ensures true; pure */ public TestJava() {}\n"
                +"}\n"
                +"class B {}\n"
                +"class C extends TestJava<B> {}\n"
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m",9
        );
    }
    
    @Test
    public void testGenericType1() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava<T extends B> { \n"
                
                +"  public void m(Integer i) {\n"
                +"    //@ assert Object.class == java.lang.Object.class;\n"
                +"    //@ assert \\type(TestJava<Integer>) != \\type(Object);\n"
                +"    //@ assert \\type(TestJava<Integer>) != \\type(TestJava<Object>);\n"
                +"  }\n"
                +"  public void mz(Object o) {\n"
                +"    //@ assert Object.class == \\erasure(\\type(T));\n" // NO
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
                +"    //@ assert Object.class != \\erasure(\\type(T));\n"  // OK because T extends B so can't be Object
                +"  }\n"
                +"  public TestJava() {}\n"
                +"}\n"
                +"class B {}\n"
                +"class C {}\n"
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method mz",9
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method ma",9
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Assert) in method mb",9
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Assert) in method mc",9
        );
    }

    @Test
    public void testStatic() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  public void ma(Integer i) {\n"
                +"    TestG.<Integer>mm(i);\n"
                +"  }\n"
                +"  public void mb(Object o) {\n"
                +"    TestG.<Object>mm(o);\n"
                +"  }\n"
                +"}\n"
                +"class TestG {\n"
                +"  //@ requires \\type(E) != \\type(Integer) ; pure \n"
                +"  public static <E> void mm(E t) {}\n"
                +"}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method ma",22
                ,"/tt/TestJava.java:12: verify: Associated declaration",26
                ,"/tt/TestJava.java:11: verify: Precondition conjunct is false: \\type(E) != \\type(Integer)",25
        );
    }

    @Test
    public void testStaticB() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  public void ma(Integer i) {\n"
                +"    TestG.mm(i);\n"
                +"  }\n"
                +"  public void mb(Object o) {\n"
                +"    TestG.mm(o);\n"
                +"  }\n"
                +"}\n"
                +"class TestG {\n"
                +"  //@ requires \\type(E) != \\type(Integer) ; pure\n"
                +"  public static <E> void mm(E t) {}\n"
                +"}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method ma",13
                ,"/tt/TestJava.java:12: verify: Associated declaration",26
                ,"/tt/TestJava.java:11: verify: Precondition conjunct is false: \\type(E) != \\type(Integer)",25
        );
    }

    @Test
    public void testStatic2() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  public void ma(Integer i) {\n"
                +"    TestG.<Integer>mm(i);\n"
                +"  }\n"
                +"  public void mb(Object o) {\n"
                +"    TestG.<Object>mm(o);\n"
                +"  }\n"
                +"}\n"
                +"class TestG {\n"
                +"  //@ requires \\type(E) == \\type(Integer) ; pure\n"
                +"  public static <E> void mm(E t) {}\n"
                +"}"
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Precondition) in method mb",21
                ,"/tt/TestJava.java:12: verify: Associated declaration",26
                ,"/tt/TestJava.java:11: verify: Precondition conjunct is false: \\type(E) == \\type(Integer)",25
        );
    }

    @Test
    public void testStatic2B() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  public void ma(Integer i) {\n"
                +"    TestG.mm(i);\n"
                +"  }\n"
                +"  public void mb(Object o) {\n"
                +"    TestG.mm(o);\n"
                +"  }\n"
                +"}\n"
                +"class TestG {\n"
                +"  //@ requires \\type(E) == \\type(Integer) ; pure\n"
                +"  public static <E> void mm(E t) {}\n"
                +"}"
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Precondition) in method mb",13
                ,"/tt/TestJava.java:12: verify: Associated declaration",26
                ,"/tt/TestJava.java:11: verify: Precondition conjunct is false: \\type(E) == \\type(Integer)",25
        );
    }

    @Test
    public void testTypeParameter() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void ma(/*@ non_null*/ TestG<Integer> i, Integer j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"  public void mb(/*@ non_null*/ TestG<Object> i, Object j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"    //@ requires \\type(E) != \\type(Integer); pure\n"
                +"    public void mm(E t) {}\n"
                +"}\n"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method ma",9
                ,"/tt/TestJava.java:12: verify: Associated declaration",17
                ,"/tt/TestJava.java:11: verify: Precondition conjunct is false: \\type(E) != \\type(Integer)",27
                );
    }
    
    @Test
    public void testTypeParameter2a() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void ma(TestG<Integer>./*@ non_null*/TestH i, Integer j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"  public void mb(TestG<Object>./*@ non_null*/TestH i, Object j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"  public void mc(TestG<String>./*@ non_null*/TestH i, String j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"  class TestH  {\n"
                +"    //@ requires \\type(E) != \\type(Integer); pure\n"
                +"    public void mm(E t) {}\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method ma",9
                ,"/tt/TestJava.java:16: verify: Associated declaration",17
                ,"/tt/TestJava.java:15: verify: Precondition conjunct is false: \\type(E) != \\type(Integer)",27
                );
    }
    
    @Test
    public void testTypeParameter2b() {
        helpEsc("tt.TestJava","package tt;import org.jmlspecs.annotation.*;\n"
                +"public class TestJava { \n"
                
                +"  public void ma(TestG<Integer>.@NonNull TestH i, Integer j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"  public void mb(TestG<Object>.@NonNull TestH i, Object j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"  public void mc(TestG<String>.@NonNull TestH i, String j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"  class TestH  {\n"
                +"    //@ requires \\type(E) != \\type(Integer); pure\n"
                +"    public void mm(E t) {}\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method ma",9
                ,"/tt/TestJava.java:16: verify: Associated declaration",17
                ,"/tt/TestJava.java:15: verify: Precondition conjunct is false: \\type(E) != \\type(Integer)",27
                );
    }
    
    @Test
    public void testTypeParameter2c() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void ma(/*@ non_null*/TestG<Integer>.TestH i, Integer j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"  public void mb(/*@ non_null*/TestG<Object>.TestH i, Object j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"  public void mc(/*@ non_null*/TestG<String>.TestH i, String j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"  class TestH  {\n"
                +"    //@ requires \\type(E) != \\type(Integer); pure\n"
                +"    public void mm(E t) {}\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method ma",9
                ,"/tt/TestJava.java:16: verify: Associated declaration",17
                ,"/tt/TestJava.java:15: verify: Precondition conjunct is false: \\type(E) != \\type(Integer)",27
                );
    }
    
    @Test
    public void testTypeParameter2d() {
        helpEsc("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  public void ma(@NonNull TestG<Integer>.TestH i, Integer j) {\n" // FIXME: i is nullable by default, or is the NonNull pushed to the nested class
                +"    i.mm(j);\n"
                +"  }\n"
                +"  public void mb(TestG<Object>.@Nullable TestH i, Object j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"  public void mc(TestG<String>.@NonNull TestH i, String j) {\n"  // OK
                +"    i.mm(j);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"  class TestH  {\n"
                +"    //@ requires \\type(E) != \\type(Integer); pure\n"
                +"    public void mm(E t) {}\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method ma",9
                ,"/tt/TestJava.java:16: verify: Associated declaration",17
                ,"/tt/TestJava.java:15: verify: Precondition conjunct is false: \\type(E) != \\type(Integer)",27
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method ma",6
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method mb",6
                );
    }
        
    @Test
    public void testTypeParameter2e() {
        expectedExit = 1;
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void ma(TestG<Integer>./*@ qqq*/TestH i, Integer j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"  class TestH  {\n"
                +"    //@ requires \\type(E) != \\type(Integer); pure\n"
                +"    public void mm(E t) {}\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:3: error: Expected an identifier, found end of JML comment instead", 40
                ,"/tt/TestJava.java:3: error: Did not expect an identifier following this formal parameter; perhaps a modifier is misspelled and thought to be a type: TestG<Integer>.qqq", 40
                );
    }
    
    @Test
    public void testTypeParameter2f() {
        expectedExit = 1;
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void ma(TestG<Integer>./*@ final */TestH i, Integer j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"  class TestH  {\n"
                +"    //@ requires \\type(E) != \\type(Integer); pure\n"
                +"    public void mm(E t) {}\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:3: error: <identifier> expected", 36
                ,"/tt/TestJava.java:3: error: ',', ')', or '[' expected", 42
                );
    }
    
    @Test
    public void testTypeParameter2g() {
        expectedExit = 1;
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void ma(TestG<Integer>./*@ pure */TestH i, Integer j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"  class TestH  {\n"
                +"    //@ requires \\type(E) != \\type(Integer); pure\n"
                +"    public void mm(E t) {}\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:3: error: A pure modifier is not allowed where type annotations are expected", 37
                );
    }
    
    @Test
    public void testTypeParameter2h() {
        expectedExit = 1;
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void ma(TestG<Integer>./*@ public */TestH i, Integer j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"  class TestH  {\n"
                +"    public void mm(E t) {}\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:3: error: <identifier> expected", 36
                ,"/tt/TestJava.java:3: error: ',', ')', or '[' expected", 43
                );
    }
    
    @Test
    public void testTypeParameter2k1() {
        expectedExit = 1;
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void ma(/*@ public */Object i) { }\n"
                +"}\n"
                ,"/tt/TestJava.java:3: error: modifier public not allowed here", 31
                );
    }
    
    @Test
    public void testTypeParameter2k2() {
        expectedExit = 1;
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void mb(/*@ pure */Object i) { }\n"
                +"}\n"
                ,"/tt/TestJava.java:3: error: This JML modifier is not allowed for a formal parameter", 22
                );
    }
    
    @Test
    public void testTypeParameter2k3() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void mc(/*@ final */Object i) { }\n"
                +"  public void md(/*@ non_null */Object i) { }\n"
                +"}\n"
                );
    }
    
    @Test
    public void testTypeParameter2k4() {
        expectedExit = 1;
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void me(/*@ qqq */Object i) { }\n"
                +"}\n"
                ,"/tt/TestJava.java:3: error: Expected an identifier, found end of JML comment instead", 26
                ,"/tt/TestJava.java:3: error: Did not expect an identifier following this formal parameter; perhaps a modifier is misspelled and thought to be a type: qqq", 26
                );
    }
        
    @Test
    public void testUnboxing() {
        addOptions("--method=m");  // Just test method m
        helpEsc("tt.TestJava"," class A { void m(/*@non_null*/ Integer ooo) { \n "
                +"int sum = 0; \n"
                +"{ /*@ assume ooo >= 0; */ sum += ooo; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                );
    }

    @Test
    public void testForEach3() {
        helpEsc("tt.TestJava"," class A {  /*@ spec_bigint_math */ void m(java.util./*@ non_null*/ List<Integer> list) { \n "
                +"int sum = 0; \n"
                +"//@ assert sum == 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (Integer o: list) { /*@ assume o != null && o >= 0 && sum + o <= Integer.MAX_VALUE; */ sum += o; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                );
    }

    @Test
    public void testForEach3c() {
    	//addOptions("-show","-method=m");
    	// nullable by default so list might be null
        helpEsc("tt.TestJava"," class A {  /*@ spec_bigint_math */ void m(java.util.List<Integer> list) { \n "
                +"int sum = 0; \n"
                +"//@ assert sum == 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (Integer o: list) { /*@ assume o != null && o >= 0 && sum + o <= Integer.MAX_VALUE; */ sum += o; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",17
                );
    }

    @Test
    public void testForEach3a() {
        helpEsc("tt.TestJava"," class A { /*@ code_bigint_math spec_bigint_math */ void m(java.util./*@ non_null*/ List</*@ non_null*/ Integer> list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) { /*@ assume o >= 0; */ sum += o; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                );
    }

    @Test
    public void testForEach3bad() {
        helpEsc("tt.TestJava"," class A { /*@ code_bigint_math spec_bigint_math */ void m(java.util./*@ non_null*/ List<Integer> list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) { /*@ assume o >= 0; */ sum += o; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method m",10
                );
    }

    @Test
    public void testElemType() {
        helpEsc("tt.TestJava"," class A { void m(char/*@ non_null */ [] a) { \n"
                +"//@ assert \\elemtype(\\typeof(a)) == \\type(char); \n"
                +"}}"
                );
    }

    @Test
    public void testElemType2() {
        helpEsc("tt.TestJava"," class A { void m(char /*@ non_null */ [] a) { \n"
                +"//@ assert \\elemtype(\\typeof(a)) == \\type(int); \n"
                +"}}"
                ,"/tt/TestJava.java:2: verify: The prover cannot establish an assertion (Assert) in method m",5
                );
    }

    @Test
    public void testElemType3() {
        expectedExit = 1;
        helpEsc("tt.TestJava"," class A { void m(/*@ non_null */ char[] a) { \n"
                +"//@ assert \\elemtype(\\typeof(a)) == \\type(int); \n"
                +"}}"
                ,"/tt/TestJava.java:1: error: the type modifier/annotation is not permitted on a primitive type: char", 23
                );
    }

    @Test
    public void testElemType4() {
        helpEsc("tt.TestJava"," class A { void m(char /*@ non_null */ [] a) { \n"
                +"//@ assert \\elemtype(\\typeof(a)) == \\type(int); \n"
                +"}}"
                ,"/tt/TestJava.java:2: verify: The prover cannot establish an assertion (Assert) in method m",5
                );
    }

    @Test
    public void testGenericThrow() {
        addOptions("--method=rt"); // Just test method rt
        helpEsc("tt.TestJava",
                 "public class TestJava { \n"
                +" //@ public exceptional_behavior \n"
                +" //@   requires true; \n"  // FIXME - should be t instanceof T
                // Can't say signals_only T; because JML only deals with Exception, not Throwable
                +" public static <T extends Throwable> RuntimeException rt(/*@ non_null*/ Throwable t) throws T { throw (T)t; } \n"
                +"}"
                );
    }
}