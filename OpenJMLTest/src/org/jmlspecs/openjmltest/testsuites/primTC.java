package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.*;
import org.junit.Test;

/** Thgis file contains type-checking tests of JML value types. They mostly check that improper uses give error messages. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class primTC extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }
    
    // bigint tests

    @Test public void jmlbigint() {
        helpTC(
            """
            class A {
              public void test1() {
                //@ ghost \\bigint b = "0";
                //@ set b = \\bigint.of("345");
                //@ set b = b.add(true);
                //@ set b = b.subtract(true);
                //@ set b = b.multiply(true);
                //@ set b = b.divide(true);
                //@ set b = b.mod(true);
                //@ check (b+true) == \\bigint.zero; // Line 10
                //@ check (b-true) == \\bigint.zero;
                //@ check (b*true) == \\bigint.zero;
                //@ check (b/true) == \\bigint.zero;
                //@ check (b%true) == \\bigint.zero;
                //@ check b.and("s") == \\bigint.zero;
                //@ check b.or("s") == \\bigint.zero;
                //@ check b.xor("s") == \\bigint.zero;
                //@ check b.shiftLeft("s") == \\bigint.zero;
                //@ check b.shiftRight("s") == \\bigint.zero;
                //@ check b.equals("s"); // Line 20
                //@ check b.compareTo("s") == 0;
                //@ ghost \\bigint br = (\\real)0;
                //@ set br = (\\bigint)\\real.empty(); // OK
                //@ check b == true;
                //@ check b != true;
                //@ check b <= true;
                //@ check b >= true;
                //@ check true < b;
                //@ check true > b;
              }
              void test2 () {
                //@ ghost \\bigint a = 0;
                //@ ghost \\real r = 0;
                //@ ghost float k = a; // ERROR
                //@ ghost double d = a; // ERROR
                //@ set k = (float)a; // ERROR
                //@ set d = (double)a; // ERROR
                //@ set a = r; // ERROR
                //@ ghost int j = a; // ERROR
                //@ set j = (int)a; // OK
                //@ check a != null; // ERROR
                //@ check a.compareTo(null) == 0; // ERROR
                //@ set a = (\\bigint)null; // ERROR
              }
            }
            """
            ,"/TEST.java:3: error: incompatible types: java.lang.String cannot be converted to \\bigint",27
            ,"""
             /TEST.java:4: error: no suitable method found for of(java.lang.String)
                 method org.jmlspecs.lang.internal.bigint.of(java.math.BigInteger) is not applicable
                   (argument mismatch; java.lang.String cannot be converted to java.math.BigInteger)
                 method org.jmlspecs.lang.internal.bigint.of(\\bigint) is not applicable
                   (argument mismatch; java.lang.String cannot be converted to \\bigint)
                 method org.jmlspecs.lang.internal.bigint.of(long) is not applicable
                   (argument mismatch; java.lang.String cannot be converted to long)
                 method org.jmlspecs.lang.internal.bigint.of(int) is not applicable
                   (argument mismatch; java.lang.String cannot be converted to int)
                 method org.jmlspecs.lang.internal.bigint.of(short) is not applicable
                   (argument mismatch; java.lang.String cannot be converted to short)
                 method org.jmlspecs.lang.internal.bigint.of(char) is not applicable
                   (argument mismatch; java.lang.String cannot be converted to char)
                 method org.jmlspecs.lang.internal.bigint.of(byte) is not applicable
                   (argument mismatch; java.lang.String cannot be converted to byte)""",24
            ,"/TEST.java:5: error: incompatible types: boolean cannot be converted to \\bigint",23
            ,"/TEST.java:6: error: incompatible types: boolean cannot be converted to \\bigint",28
            ,"/TEST.java:7: error: incompatible types: boolean cannot be converted to \\bigint",28
            ,"/TEST.java:8: error: incompatible types: boolean cannot be converted to \\bigint",26
            ,"/TEST.java:9: error: incompatible types: boolean cannot be converted to \\bigint",23
            ,"/TEST.java:10: error: No allowed implicit conversion permits this operation on JML types: \\bigint + boolean", 17
            ,"/TEST.java:11: error: No allowed implicit conversion permits this operation on JML types: \\bigint - boolean", 17
            ,"/TEST.java:12: error: No allowed implicit conversion permits this operation on JML types: \\bigint * boolean", 17
            ,"/TEST.java:13: error: No allowed implicit conversion permits this operation on JML types: \\bigint / boolean", 17
            ,"/TEST.java:14: error: No allowed implicit conversion permits this operation on JML types: \\bigint % boolean", 17
            ,"/TEST.java:15: error: incompatible types: java.lang.String cannot be converted to \\bigint",21
            ,"/TEST.java:16: error: incompatible types: java.lang.String cannot be converted to \\bigint",20
            ,"/TEST.java:17: error: incompatible types: java.lang.String cannot be converted to \\bigint",21
            ,"/TEST.java:18: error: incompatible types: java.lang.String cannot be converted to \\bigint",27
            ,"/TEST.java:19: error: incompatible types: java.lang.String cannot be converted to \\bigint",28
            ,"/TEST.java:21: error: incompatible types: java.lang.String cannot be converted to \\bigint",27
            ,"/TEST.java:22: error: incompatible types: \\real cannot be converted to \\bigint",28
            ,"/TEST.java:24: error: No allowed implicit conversion permits this operation on JML types: \\bigint == boolean", 17
            ,"/TEST.java:25: error: No allowed implicit conversion permits this operation on JML types: \\bigint != boolean", 17
            ,"/TEST.java:26: error: No allowed implicit conversion permits this operation on JML types: \\bigint <= boolean", 17
            ,"/TEST.java:27: error: No allowed implicit conversion permits this operation on JML types: \\bigint >= boolean", 17
            ,"/TEST.java:28: error: No allowed implicit conversion permits this operation on JML types: boolean < \\bigint", 20
            ,"/TEST.java:29: error: No allowed implicit conversion permits this operation on JML types: boolean > \\bigint", 20

            ,"/TEST.java:34: error: incompatible types: \\bigint cannot be converted to float", 25
            ,"/TEST.java:35: error: incompatible types: \\bigint cannot be converted to double", 26
            ,"/TEST.java:36: error: A \\bigint may not be cast to a float", 24
            ,"/TEST.java:37: error: A \\bigint may not be cast to a double", 25
            ,"/TEST.java:38: error: incompatible types: \\real cannot be converted to \\bigint", 17
            ,"/TEST.java:39: error: incompatible types: \\bigint cannot be converted to int", 23
            ,"/TEST.java:41: error: JML primitive types may not be compared to null", 17
            ,"/TEST.java:41: error: No allowed implicit conversion permits this operation on JML types: \\bigint != <nulltype>", 17
            ,"/TEST.java:42: error: incompatible types: <nulltype> cannot be converted to \\bigint", 27
            ,"/TEST.java:43: error: A <nulltype> may not be cast to a \\bigint", 26

        );
    }

    // real tests
    
    @Test public void jmlreal() {
        helpTC(
                """
                class A {
                  public void test1() {
                    //@ ghost \\real b = "0";
                    //@ set b = \\real.of("345");
                    //@ set b = b.add(true);
                    //@ set b = b.subtract(true);
                    //@ set b = b.multiply(true);
                    //@ set b = b.divide(true);
                    //@ set b = b.mod(true);
                    //@ check (b+true) == (\\real)0; // Line 10
                    //@ check (b-true) == (\\real)0;
                    //@ check (b*true) == (\\real)0;
                    //@ check (b/true) == (\\real)0;
                    //@ check (b%true) == (\\real)0;
                    //@ check b.equals("s"); // Line 15
                    //@ check b.compareTo("s") == 0;
                    //@ check b == true;
                    //@ check b != true;
                    //@ check b <= true;
                    //@ check b >= true;
                    //@ check true < b;
                    //@ check true > b;
                  }
                }
                """
                ,"/TEST.java:3: error: incompatible types: java.lang.String cannot be converted to \\real",25
                ,"""
                 /TEST.java:4: error: no suitable method found for of(java.lang.String)
                     method org.jmlspecs.lang.internal.real.of(double) is not applicable
                       (argument mismatch; java.lang.String cannot be converted to double)
                     method org.jmlspecs.lang.internal.real.of(float) is not applicable
                       (argument mismatch; java.lang.String cannot be converted to float)
                     method org.jmlspecs.lang.internal.real.of(long) is not applicable
                       (argument mismatch; java.lang.String cannot be converted to long)
                     method org.jmlspecs.lang.internal.real.of(int) is not applicable
                       (argument mismatch; java.lang.String cannot be converted to int)
                     method org.jmlspecs.lang.internal.real.of(char) is not applicable
                       (argument mismatch; java.lang.String cannot be converted to char)
                     method org.jmlspecs.lang.internal.real.of(short) is not applicable
                       (argument mismatch; java.lang.String cannot be converted to short)
                     method org.jmlspecs.lang.internal.real.of(byte) is not applicable
                       (argument mismatch; java.lang.String cannot be converted to byte)
                     method org.jmlspecs.lang.internal.real.of(\\bigint) is not applicable
                       (argument mismatch; java.lang.String cannot be converted to \\bigint)
                     method org.jmlspecs.lang.internal.real.of(java.math.BigInteger) is not applicable
                       (argument mismatch; java.lang.String cannot be converted to java.math.BigInteger)""",22
                ,"/TEST.java:5: error: incompatible types: boolean cannot be converted to \\real",23
                ,"/TEST.java:6: error: incompatible types: boolean cannot be converted to \\real",28
                ,"/TEST.java:7: error: incompatible types: boolean cannot be converted to \\real",28
                ,"/TEST.java:8: error: incompatible types: boolean cannot be converted to \\real",26
                ,"/TEST.java:9: error: incompatible types: boolean cannot be converted to \\real",23
                ,"/TEST.java:10: error: No allowed implicit conversion permits this operation on JML types: \\real + boolean", 17
                ,"/TEST.java:11: error: No allowed implicit conversion permits this operation on JML types: \\real - boolean", 17
                ,"/TEST.java:12: error: No allowed implicit conversion permits this operation on JML types: \\real * boolean", 17
                ,"/TEST.java:13: error: No allowed implicit conversion permits this operation on JML types: \\real / boolean", 17
                ,"/TEST.java:14: error: No allowed implicit conversion permits this operation on JML types: \\real % boolean", 17
                ,"/TEST.java:16: error: incompatible types: java.lang.String cannot be converted to \\real",27
                ,"/TEST.java:17: error: No allowed implicit conversion permits this operation on JML types: \\real == boolean", 17
                ,"/TEST.java:18: error: No allowed implicit conversion permits this operation on JML types: \\real != boolean", 17
                ,"/TEST.java:19: error: No allowed implicit conversion permits this operation on JML types: \\real <= boolean", 17
                ,"/TEST.java:20: error: No allowed implicit conversion permits this operation on JML types: \\real >= boolean", 17
                ,"/TEST.java:21: error: No allowed implicit conversion permits this operation on JML types: boolean < \\real", 20
                ,"/TEST.java:22: error: No allowed implicit conversion permits this operation on JML types: boolean > \\real", 20
        );
    }

    // TYPE tests
    
    @Test public void jmlTYPE() {
        helpTC(" class A { //@ ghost \\TYPE b ; \n}");
    }
    
    // string tests
    
    @Test public void jmlstring() {
        helpTC(
                """
                class A {
                  void m() {
                    Object o = new Object();
                    //@ ghost \\string b;
                    //@ ghost boolean z = \\string.of("ABC");
                    //@ ghost boolean zz = \\string.of(0);
                    //@ ghost var cc = b.get(o);
                    //@ ghost var ccc = b.getUnchecked(o);
                    //@ set b = b.put(o,0);
                    //@ set b = b.remove(o); // Line 10
                    //@ set b = b.insert(o,42);
                    //@ set b = b.append(123);
                    //@
                    //@ set b = b + o;
                    //@ ghost boolean x = b.head();
                    //@ ghost char c = b.head(1);
                    //@ ghost char cz = b.head(o);
                    //@ ghost var cy = b.tail(o);
                    //@ ghost char cx = b.tail();
                    //@ ghost boolean w = b.compareTo("zz"); // OK
                    //@ ghost boolean y = b.compareTo(o); // NOT OK
                    //@ set b = b.substring(o,o);
                    //@ check b.equals(o); // OK
                    //@ set cc = b[o];
                    //@ ghost boolean cq = b[0];
                    //@ ghost boolean ct = b.get(0);
                  }
                }
                """
                ,"/TEST.java:5: error: incompatible types: \\string cannot be converted to boolean",37  // FIXME - position should be the =
                ,"""
                 /TEST.java:6: error: no suitable method found for of(int)
                     method org.jmlspecs.lang.internal.string.of(java.lang.String) is not applicable
                       (argument mismatch; int cannot be converted to java.lang.String)
                     method org.jmlspecs.lang.internal.string.of(char) is not applicable
                       (argument mismatch; possible lossy conversion from int to char)""", 35
                ,"/TEST.java:7: error: incompatible types: java.lang.Object cannot be converted to \\bigint",30 // FIXME - position should be the =
                ,"/TEST.java:8: error: incompatible types: java.lang.Object cannot be converted to \\bigint",40
                ,"/TEST.java:9: error: incompatible types: java.lang.Object cannot be converted to \\bigint",23
                ,"/TEST.java:10: error: incompatible types: java.lang.Object cannot be converted to \\bigint",26
                ,"/TEST.java:11: error: incompatible types: java.lang.Object cannot be converted to \\bigint",26
                ,"""
                 /TEST.java:12: error: no suitable method found for append(int)
                     method org.jmlspecs.lang.internal.string.append(char) is not applicable
                       (argument mismatch; possible lossy conversion from int to char)
                     method org.jmlspecs.lang.internal.string.append(java.lang.String) is not applicable
                       (argument mismatch; int cannot be converted to java.lang.String)
                     method org.jmlspecs.lang.internal.string.append(\\string) is not applicable
                       (argument mismatch; int cannot be converted to \\string)""",18
                ,"/TEST.java:14: error: No operator for \\string + java.lang.Object",19
                ,"/TEST.java:15: error: incompatible types: char cannot be converted to boolean",33
                ,"/TEST.java:16: error: incompatible types: \\string cannot be converted to char",30
                ,"/TEST.java:17: error: incompatible types: java.lang.Object cannot be converted to \\bigint",32
                ,"/TEST.java:18: error: incompatible types: java.lang.Object cannot be converted to \\bigint",31
                ,"/TEST.java:19: error: incompatible types: \\string cannot be converted to char",31
                ,"/TEST.java:20: error: incompatible types: int cannot be converted to boolean",38
                ,"/TEST.java:21: error: incompatible types: java.lang.Object cannot be converted to \\string",39
                ,"/TEST.java:22: error: incompatible types: java.lang.Object cannot be converted to \\bigint",29
                ,"/TEST.java:24: error: Expected an integral type as an index, not java.lang.Object, for indexable type \\string",20
                ,"/TEST.java:25: error: incompatible types: char cannot be converted to boolean",29
                ,"/TEST.java:26: error: incompatible types: char cannot be converted to boolean",33
                );
    }

    // array tests

    @Test public void jmlarray() {
        helpTC(
                """
                class A {
                  void m() {
                    Object o = new Object();
                    //@ ghost \\array<Integer> b;
                    //@ ghost \\array<Boolean> bb;
                    //@ check b != bb;
                    //@ check !(b == bb);
                    //@ check b.ne(bb);
                    //@ check !b.eq(bb);
                    //@ var cc = b.get(o); // Line 10
                    //@ set b = b.put(o,true);
                    //@ set b = \\array.<Integer>of(true);
                    //@ set bb = b;
                    //@ ghost boolean z = b.get(0);
                    //@ ghost boolean y = b[0];
                    //@ ghost var w = b + bb;
                    //@ check \\array.<Integer>empty().equals(\\array.<Boolean>empty());
                  }
                }
                """
                ,"/TEST.java:6: error: No allowed implicit conversion permits this operation on JML types: \\array<java.lang.@org.jmlspecs.annotation.NonNull Integer> != \\array<java.lang.@org.jmlspecs.annotation.NonNull Boolean>", 17
                ,"/TEST.java:7: error: No allowed implicit conversion permits this operation on JML types: \\array<java.lang.@org.jmlspecs.annotation.NonNull Integer> == \\array<java.lang.@org.jmlspecs.annotation.NonNull Boolean>", 19
                ,"/TEST.java:8: error: incompatible types: \\array<@org.jmlspecs.annotation.NonNull java.lang.Boolean> cannot be converted to \\array<@org.jmlspecs.annotation.NonNull java.lang.Integer>",20
                ,"/TEST.java:9: error: incompatible types: \\array<@org.jmlspecs.annotation.NonNull java.lang.Boolean> cannot be converted to \\array<@org.jmlspecs.annotation.NonNull java.lang.Integer>",21
                ,"/TEST.java:10: error: incompatible types: java.lang.Object cannot be converted to \\bigint",24
                ,"/TEST.java:11: error: incompatible types: java.lang.Object cannot be converted to \\bigint",23
                ,"""
                 /TEST.java:12: error: method of in class \\array<T> cannot be applied to given types;
                   required: TT[]
                   found:    boolean
                   reason: varargs mismatch; boolean cannot be converted to java.lang.Integer""",23
                ,"/TEST.java:13: error: incompatible types: \\array<@org.jmlspecs.annotation.NonNull java.lang.Integer> cannot be converted to \\array<@org.jmlspecs.annotation.NonNull java.lang.Boolean>",18
                ,"/TEST.java:14: error: incompatible types: @org.jmlspecs.annotation.NonNull java.lang.Integer cannot be converted to boolean",32
                ,"/TEST.java:15: error: incompatible types: @org.jmlspecs.annotation.NonNull java.lang.Integer cannot be converted to boolean",28
                ,"/TEST.java:16: error: No operator for \\array<java.lang.@org.jmlspecs.annotation.NonNull Integer> + \\array<java.lang.@org.jmlspecs.annotation.NonNull Boolean>",25
                ,"""
                 /TEST.java:17: error: no suitable method found for equals(\\array<java.lang.Boolean>)
                     method org.jmlspecs.lang.internal.array.equals(\\array<java.lang.Integer>) is not applicable
                       (argument mismatch; \\array<java.lang.Boolean> cannot be converted to \\array<java.lang.Integer>)
                     method org.jmlspecs.lang.internal.array.equals(java.lang.Object) is not applicable
                       (argument mismatch; \\array<java.lang.Boolean> cannot be converted to java.lang.Object)""",38
                );
    }
    // Seq tests

    @Test public void jmlseq() {
        helpTC(
                """
                class A {
                  void m() {
                    Object o = new Object();
                    //@ ghost \\seq<Integer> b;
                    //@ ghost \\seq<Boolean> bb;
                    //@ var cc = b.get(o);
                    //@ set b = b.append(true);
                    //@ set b = b.prepend(true);
                    //@ set b = b.put(o,0);
                    //@ set b = b.remove(o); // Line 10
                    //@ set b = b.insert(o,42);
                    //@ set b = b.append(bb);
                    //@ set b = b.prepend(bb);
                    //@ check b == bb && b.eq(bb); check b != bb && b.ne(bb);
                    //@ ghost Boolean x = b.head();
                    //@ ghost char c = b.head(1);
                    //@ ghost char cc = b.tail();
                    //@ ghost char ccc = b.tail(o);
                    //@ set b = \\seq.<Integer>of(true);
                    //@ set bb = b;                  // Line 20
                    //@ ghost boolean z = b.get(0);
                    //@ ghost boolean y = b[0];
                    //@ ghost var w = b + bb;
                    //@ set bb = b.subseq(0,0);
                    //@ set bb = b.subseq(o,o);
                    //@ check seq.<Integer>empty().equals(seq.<Boolean>empty());
                  }
                }
                """
                ,"/TEST.java:6: error: incompatible types: java.lang.Object cannot be converted to \\bigint",24
                ,"""
                 /TEST.java:7: error: no suitable method found for append(boolean)
                     method org.jmlspecs.lang.internal.seq.append(\\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer>) is not applicable
                       (argument mismatch; boolean cannot be converted to \\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer>)
                     method org.jmlspecs.lang.internal.seq.append(@org.jmlspecs.annotation.NonNull java.lang.Integer) is not applicable
                       (argument mismatch; boolean cannot be converted to @org.jmlspecs.annotation.NonNull java.lang.Integer)""",18
                ,"""
                 /TEST.java:8: error: no suitable method found for prepend(boolean)
                     method org.jmlspecs.lang.internal.seq.prepend(@org.jmlspecs.annotation.NonNull java.lang.Integer) is not applicable
                       (argument mismatch; boolean cannot be converted to @org.jmlspecs.annotation.NonNull java.lang.Integer)
                     method org.jmlspecs.lang.internal.seq.prepend(\\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer>) is not applicable
                       (argument mismatch; boolean cannot be converted to \\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer>)""",18
                ,"/TEST.java:9: error: incompatible types: java.lang.Object cannot be converted to \\bigint",23
                ,"/TEST.java:10: error: incompatible types: java.lang.Object cannot be converted to \\bigint",26
                ,"/TEST.java:11: error: incompatible types: java.lang.Object cannot be converted to \\bigint",26
                ,"""
                 /TEST.java:12: error: no suitable method found for append(\\seq<@org.jmlspecs.annotation.NonNull java.lang.Boolean>)
                     method org.jmlspecs.lang.internal.seq.append(\\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer>) is not applicable
                       (argument mismatch; \\seq<@org.jmlspecs.annotation.NonNull java.lang.Boolean> cannot be converted to \\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer>)
                     method org.jmlspecs.lang.internal.seq.append(@org.jmlspecs.annotation.NonNull java.lang.Integer) is not applicable
                       (argument mismatch; \\seq<@org.jmlspecs.annotation.NonNull java.lang.Boolean> cannot be converted to @org.jmlspecs.annotation.NonNull java.lang.Integer)""",18
                ,"""
                 /TEST.java:13: error: no suitable method found for prepend(\\seq<@org.jmlspecs.annotation.NonNull java.lang.Boolean>)
                     method org.jmlspecs.lang.internal.seq.prepend(@org.jmlspecs.annotation.NonNull java.lang.Integer) is not applicable
                       (argument mismatch; \\seq<@org.jmlspecs.annotation.NonNull java.lang.Boolean> cannot be converted to @org.jmlspecs.annotation.NonNull java.lang.Integer)
                     method org.jmlspecs.lang.internal.seq.prepend(\\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer>) is not applicable
                       (argument mismatch; \\seq<@org.jmlspecs.annotation.NonNull java.lang.Boolean> cannot be converted to \\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer>)""",18
                ,"/TEST.java:14: error: No allowed implicit conversion permits this operation on JML types: \\seq<java.lang.@org.jmlspecs.annotation.NonNull Integer> == \\seq<java.lang.@org.jmlspecs.annotation.NonNull Boolean>", 17
                ,"/TEST.java:14: error: incompatible types: \\seq<@org.jmlspecs.annotation.NonNull java.lang.Boolean> cannot be converted to \\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer>",31
                ,"/TEST.java:14: error: No allowed implicit conversion permits this operation on JML types: \\seq<java.lang.@org.jmlspecs.annotation.NonNull Integer> != \\seq<java.lang.@org.jmlspecs.annotation.NonNull Boolean>", 44
                ,"/TEST.java:14: error: incompatible types: \\seq<@org.jmlspecs.annotation.NonNull java.lang.Boolean> cannot be converted to \\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer>",58
                ,"/TEST.java:15: error: incompatible types: @org.jmlspecs.annotation.NonNull java.lang.Integer cannot be converted to java.lang.Boolean",33
                ,"/TEST.java:16: error: incompatible types: \\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer> cannot be converted to char",30
                ,"/TEST.java:17: error: incompatible types: \\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer> cannot be converted to char",31
                ,"/TEST.java:18: error: incompatible types: java.lang.Object cannot be converted to \\bigint",33
                ,"""
                 /TEST.java:19: error: no suitable method found for of(boolean)
                     method org.jmlspecs.lang.internal.seq.of(int[]) is not applicable
                       (argument mismatch; boolean cannot be converted to int[])
                     method org.jmlspecs.lang.internal.seq.<T>of(T...) is not applicable
                       (varargs mismatch; boolean cannot be converted to java.lang.Integer)""",21
                ,"/TEST.java:20: error: incompatible types: \\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer> cannot be converted to \\seq<@org.jmlspecs.annotation.NonNull java.lang.Boolean>",18
                ,"/TEST.java:21: error: incompatible types: @org.jmlspecs.annotation.NonNull java.lang.Integer cannot be converted to boolean",32
                ,"/TEST.java:22: error: incompatible types: @org.jmlspecs.annotation.NonNull java.lang.Integer cannot be converted to boolean", 28
                ,"/TEST.java:23: error: No allowed implicit conversion permits this operation on JML types: \\seq<java.lang.@org.jmlspecs.annotation.NonNull Integer> + \\seq<java.lang.@org.jmlspecs.annotation.NonNull Boolean>",25
                ,"/TEST.java:24: error: incompatible types: \\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer> cannot be converted to \\seq<@org.jmlspecs.annotation.NonNull java.lang.Boolean>",26
                ,"/TEST.java:25: error: incompatible types: java.lang.Object cannot be converted to \\bigint",27
                ,"""
                 /TEST.java:26: error: cannot find symbol
                   symbol:   variable seq
                   location: class A""",43
                ,"""
                 /TEST.java:26: error: cannot find symbol
                   symbol:   variable seq
                   location: class A""",15

    );
    }
    
    // Set tests
    
    @Test public void jmlset() {
        helpTC(
                """
                class A {
                    void test() {
                        //@ ghost \\set<\\string> m = 7; // ERROR
                        //@ ghost \\string s = "";
                        Object o = new Object();
                        //@ ghost int x = m[o]; // ERROR
                        //@ ghost int xx = m[s]; // ERROR
                        //@ ghost var z = \\set.<Boolean>of(o, 5); // ERROR
                        //@ check m.contains(o);
                        //@ ghost var s1 = m.add(o); // ERROR
                        //@ ghost var s2 = m.remove(o); // ERROR
                        //@ ghost \\set<\\bigint> mb;
                        //@ check m.isSubsetOf(mb);// ERROR
                        //@ check m.isProperSubsetOf(mb);// ERROR
                        //@ check m.union(mb).isEmpty();// ERROR
                        //@ check m.intersect(mb).isEmpty();// ERROR
                        //@ check m.subtract(mb).isEmpty();// ERROR
                        //@ check m.eq(mb); // ERROR
                        //@ check m.ne(mb); // ERROR
                        //@ check m == mb; // ERROR
                        //@ check m != mb; // ERROR
                        //@ ghost var w1 = m | o; // ERROR
                        //@ ghost var w2 = o & m; // ERROR
                        //@ ghost var w3 = o - m; // ERROR
                        //@ ghost var w4 = m < \\set.<Boolean>empty(); // ERROR
                        //@ ghost var w5 = m <= \\set.<Boolean>empty(); // ERROR
                    }
                }
                """
                ,"/TEST.java:3: error: incompatible types: int cannot be converted to \\set<@org.jmlspecs.annotation.NonNull \\string>",37
                ,"/TEST.java:6: error: Expected an index type of \\@org.jmlspecs.annotation.NonNull string, not java.lang.Object",29
                ,"/TEST.java:6: error: incompatible types: boolean cannot be converted to int",28
                ,"/TEST.java:7: error: incompatible types: boolean cannot be converted to int",29
                ,"""
                 /TEST.java:8: error: no suitable method found for of(java.lang.Object,int)
                     method org.jmlspecs.lang.internal.set.<X>of(X...) is not applicable
                       (varargs mismatch; java.lang.Object cannot be converted to java.lang.Boolean)
                     method org.jmlspecs.lang.internal.set.<X>of(X,X) is not applicable
                       (argument mismatch; java.lang.Object cannot be converted to java.lang.Boolean)""", 31
                ,"/TEST.java:9: error: incompatible types: java.lang.Object cannot be converted to @org.jmlspecs.annotation.NonNull \\string", 30
                ,"/TEST.java:10: error: incompatible types: java.lang.Object cannot be converted to @org.jmlspecs.annotation.NonNull \\string", 34
                ,"/TEST.java:11: error: incompatible types: java.lang.Object cannot be converted to @org.jmlspecs.annotation.NonNull \\string", 37
                ,"/TEST.java:13: error: incompatible types: \\set<@org.jmlspecs.annotation.NonNull \\bigint> cannot be converted to \\set<@org.jmlspecs.annotation.NonNull \\string>", 32
                ,"/TEST.java:14: error: incompatible types: \\set<@org.jmlspecs.annotation.NonNull \\bigint> cannot be converted to \\set<@org.jmlspecs.annotation.NonNull \\string>", 38
                ,"/TEST.java:15: error: incompatible types: \\set<@org.jmlspecs.annotation.NonNull \\bigint> cannot be converted to \\set<@org.jmlspecs.annotation.NonNull \\string>", 27
                ,"/TEST.java:16: error: incompatible types: \\set<@org.jmlspecs.annotation.NonNull \\bigint> cannot be converted to \\set<@org.jmlspecs.annotation.NonNull \\string>", 31
                ,"/TEST.java:17: error: incompatible types: \\set<@org.jmlspecs.annotation.NonNull \\bigint> cannot be converted to \\set<@org.jmlspecs.annotation.NonNull \\string>", 30
                ,"/TEST.java:18: error: incompatible types: \\set<@org.jmlspecs.annotation.NonNull \\bigint> cannot be converted to \\set<@org.jmlspecs.annotation.NonNull \\string>", 24
                ,"/TEST.java:19: error: incompatible types: \\set<@org.jmlspecs.annotation.NonNull \\bigint> cannot be converted to \\set<@org.jmlspecs.annotation.NonNull \\string>", 24
                ,"/TEST.java:20: error: No allowed implicit conversion permits this operation on JML types: \\set<\\@org.jmlspecs.annotation.NonNull string> == \\set<\\@org.jmlspecs.annotation.NonNull bigint>", 21
                ,"/TEST.java:21: error: No allowed implicit conversion permits this operation on JML types: \\set<\\@org.jmlspecs.annotation.NonNull string> != \\set<\\@org.jmlspecs.annotation.NonNull bigint>", 21
                ,"/TEST.java:22: error: No operator for \\set<\\@org.jmlspecs.annotation.NonNull string> | java.lang.Object", 30
                ,"/TEST.java:23: error: No operator for java.lang.Object & \\set<\\@org.jmlspecs.annotation.NonNull string>", 30
                ,"/TEST.java:24: error: No operator for java.lang.Object - \\set<\\@org.jmlspecs.annotation.NonNull string>", 30
                ,"/TEST.java:25: error: No allowed implicit conversion permits this operation on JML types: \\set<\\@org.jmlspecs.annotation.NonNull string> < \\set<java.lang.Boolean>", 30
                ,"/TEST.java:26: error: No allowed implicit conversion permits this operation on JML types: \\set<\\@org.jmlspecs.annotation.NonNull string> <= \\set<java.lang.Boolean>", 30

                );
    }

    

    // Map tests

    @Test public void jmlmap() {
        helpTC(
            """
            class A {
                void test() {
                    //@ ghost \\map<\\string,\\string> m = 7; // ERROR
                    //@ ghost \\string s = "";
                    Object o = new Object();
                    //@ ghost \\bigint bb = m[o]; // ERROR
                    //@ ghost \\map<Number,\\string> mm;
                    //@ ghost \\string ss = mm[o]; // ERROR
                    //@ set ss = mm.get(o); // ERROR
                    //@ ghost var sss = mm[Integer.valueOf(4)]; // OK
                    //@ set ss = m.put(o,""); // ERROR
                    //@ set ss = m.put("",o); // ERROR
                    //@ set m = m.putAll(mm); // ERROR
                    //@ set m = m.remove(o); // ERROR
                }
            }
            """
            ,"/TEST.java:3: error: incompatible types: int cannot be converted to \\map<@org.jmlspecs.annotation.NonNull \\string,@org.jmlspecs.annotation.NonNull \\string>", 45
            ,"/TEST.java:6: error: Expected an index type of \\@org.jmlspecs.annotation.NonNull string, not java.lang.Object", 34
            ,"/TEST.java:6: error: incompatible types: @org.jmlspecs.annotation.NonNull \\string cannot be converted to \\bigint", 33
            ,"/TEST.java:8: error: Expected an index type of java.lang.@org.jmlspecs.annotation.NonNull Number, not java.lang.Object", 35
            ,"/TEST.java:9: error: incompatible types: java.lang.Object cannot be converted to @org.jmlspecs.annotation.NonNull java.lang.Number", 29
            ,"/TEST.java:11: error: incompatible types: java.lang.Object cannot be converted to @org.jmlspecs.annotation.NonNull \\string", 28 
            ,"/TEST.java:12: error: incompatible types: java.lang.Object cannot be converted to @org.jmlspecs.annotation.NonNull \\string", 31 
            ,"/TEST.java:13: error: incompatible types: \\map<@org.jmlspecs.annotation.NonNull java.lang.Number,@org.jmlspecs.annotation.NonNull \\string> cannot be converted to \\map<@org.jmlspecs.annotation.NonNull \\string,@org.jmlspecs.annotation.NonNull \\string>",30
            ,"/TEST.java:14: error: incompatible types: java.lang.Object cannot be converted to @org.jmlspecs.annotation.NonNull \\string", 30
        );
    }


    // TODO: Review the following

     // FIXME - do we allow direct assignment?
//    @Test public void testArrayType() {
//        helpTC(" class A { void m() { //@ ghost \\array<Object> b; ghost \\bigint i = 0; ghost Object o = b[i]; set b[i] = o; \n}}"
//                );
//    }

    @Test public void testIntsetType() {
        helpTC(" class A { void m() { //@ ghost \\intset b; ghost \\bigint i = 0; ghost boolean o = b[i];  set b[i] = true; \n}}");
    }

    @Test public void testIntmapType() {
        helpTC(" class A { void m() { //@ ghost \\intmap<Object> b ; ghost \\bigint i = 0; ghost Object o = b[i]; set b[i] = o; \n}}");
    }

   // FIXME - need to be able to initialize JML types
    

    
}
