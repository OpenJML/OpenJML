package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.*;
import org.junit.Test;

/** This file contains type-checking tests of JML value types. They mostly check that improper uses give error messages. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class primTC extends TCBase {

    // bigint tests

    @Test public void jmlbigint() {
        helpTCText(null, 
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
            ,"""
             /TEST.java:18: error: no suitable method found for shiftLeft(java.lang.String)
                 method org.jmlspecs.lang.internal.bigint.shiftLeft(\\bigint) is not applicable
                   (argument mismatch; java.lang.String cannot be converted to \\bigint)
                 method org.jmlspecs.lang.internal.bigint.shiftLeft(int) is not applicable
                   (argument mismatch; java.lang.String cannot be converted to int)""", 16
            ,"""
             /TEST.java:19: error: no suitable method found for shiftRight(java.lang.String)
                 method org.jmlspecs.lang.internal.bigint.shiftRight(\\bigint) is not applicable
                   (argument mismatch; java.lang.String cannot be converted to \\bigint)
                 method org.jmlspecs.lang.internal.bigint.shiftRight(int) is not applicable
                   (argument mismatch; java.lang.String cannot be converted to int)""", 16
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

    @Test public void jmlbigintFlow() {// Flow tests (won't be detected if there are typechecking errors)
        helpTCText(null, 
        """
        class A {
          void m() {
             Object o = new Object();
            //@ ghost \\bigint s; ghost var ss = s;
            //@ ghost \\bigint a; check a == 0;
         }
        }
        """
        ,"/TEST.java:4: error: variable s might not have been initialized", 41
        ,"/TEST.java:5: error: variable a might not have been initialized", 32
        );
    }


    // real tests
    
    @Test public void jmlreal() {
        helpTCText(null, 
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
                       (argument mismatch; java.lang.String cannot be converted to java.math.BigInteger)
                     method org.jmlspecs.lang.internal.real.of(java.math.BigDecimal) is not applicable
                       (argument mismatch; java.lang.String cannot be converted to java.math.BigDecimal)""",22
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

    @Test public void jmlrealFlow() {// Flow tests (won't be detected if there are typechecking errors)
        helpTCText(null, 
        """
        class A {
          void m() {
             Object o = new Object();
            //@ ghost \\real s; ghost var ss = s;
            //@ ghost \\real a; check a == 0;
         }
        }
        """
        ,"/TEST.java:4: error: variable s might not have been initialized", 39
        ,"/TEST.java:5: error: variable a might not have been initialized", 30
        );
    }


    // TYPE tests
    
    @Test public void jmlTYPE() {
        helpTCText(null, 
            """
            class A {
              public static void m() {
                //@ ghost \\TYPE t = Boolean.class;
                //@ set t = \\TYPE.of(Boolean.class, Integer.class);
                //@ set t = \\TYPE.of(Boolean.class, null, Integer.class);
                //@ set t = \\TYPE.of(null, Integer.class);
                //@ set t = \\TYPE.of(Boolean.class, null);
              }
            }
            """
            ,"/TEST.java:3: error: incompatible types: java.lang.Class<java.lang.Boolean> cannot be converted to \\TYPE",32
            ,"""
             /TEST.java:4: error: no suitable method found for of(java.lang.Class<java.lang.Boolean>,java.lang.Class<java.lang.Integer>)
                 method org.jmlspecs.lang.internal.TYPE.of(java.lang.Class<?>,\\TYPE) is not applicable
                   (argument mismatch; java.lang.Class<java.lang.Integer> cannot be converted to \\TYPE)
                 method org.jmlspecs.lang.internal.TYPE.of(java.lang.Class<?>,\\TYPE...) is not applicable
                   (varargs mismatch; java.lang.Class<java.lang.Integer> cannot be converted to \\TYPE)""", 22
            ,"""
             /TEST.java:5: error: no suitable method found for of(java.lang.Class<java.lang.Boolean>,<nulltype>,java.lang.Class<java.lang.Integer>)
                 method org.jmlspecs.lang.internal.TYPE.of(java.lang.Class<?>,\\TYPE,\\TYPE) is not applicable
                   (argument mismatch; <nulltype> cannot be converted to \\TYPE)
                 method org.jmlspecs.lang.internal.TYPE.of(java.lang.Class<?>,\\TYPE...) is not applicable
                   (varargs mismatch; <nulltype> cannot be converted to \\TYPE)""", 22
            ,"""
             /TEST.java:6: error: no suitable method found for of(<nulltype>,java.lang.Class<java.lang.Integer>)
                 method org.jmlspecs.lang.internal.TYPE.of(java.lang.Class<?>,\\TYPE) is not applicable
                   (argument mismatch; java.lang.Class<java.lang.Integer> cannot be converted to \\TYPE)
                 method org.jmlspecs.lang.internal.TYPE.of(java.lang.Class<?>,\\TYPE...) is not applicable
                   (varargs mismatch; java.lang.Class<java.lang.Integer> cannot be converted to \\TYPE)""", 22
            ,"/TEST.java:7: error: the value for a varargs array may not be null", 41
        );
    }
    
    @Test public void jmlTYPEFlow() {
        helpTCText(null, 
            """
            class A {
              //@ ghost \\TYPE b ;
              public void m() {
                //@ ghost \\TYPE bb;
                //@ ghost \\TYPE bbb = b;
                //@ set bbb = bb;
              }
            }
            """
            ,"/TEST.java:6: error: variable bb might not have been initialized", 19
        );
    }
    
    // string tests
    
    @Test public void jmlstring() {
        helpTCText(null, 
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
    
    @Test public void jmlstringFlow() {// Flow tests (won't be detected if there are typechecking errors)
        helpTCText(null, 
        """
        class A {
          void m() {
             Object o = new Object();
            //@ ghost \\string s; ghost var ss = s;
            //@ ghost \\string a; check a.put(0,' ') == a;
         }
        }
        """
        ,"/TEST.java:4: error: variable s might not have been initialized", 41
        ,"/TEST.java:5: error: variable a might not have been initialized", 32
        );
    }


    // array tests

    @Test public void jmlarray() {
        helpTCText(null, 
                """
                class A {
                  void m() {
                    Object o = new Object();
                    //@ ghost \\array<Integer> b; havoc b;
                    //@ ghost \\array<Boolean> bb; havoc bb;
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

    @Test public void jmlarrayFlow() {// Flow tests (won't be detected if there are typechecking errors)
        helpTCText(null, 
        """
        class A {
          void m() {
             Object o = new Object();
            //@ ghost \\array<Short> s; ghost var ss = s;
            //@ ghost \\array<Object> a; set a[3] = o;
         }
        }
        """
        ,"/TEST.java:4: error: variable s might not have been initialized", 47
        ,"/TEST.java:5: error: variable a might not have been initialized", 37
        );
    }

    // Seq tests

    @Test public void jmlseq() {
        helpTCText(null, 
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

    @Test public void jmlseqFlow() {// Flow tests (won't be detected if there are typechecking errors)
        helpTCText(null, 
        """
        class A {
          void m() {
             Object o = new Object();
            //@ ghost \\seq<Short> s; ghost var ss = s;
            //@ ghost \\seq<Object> a; set a[3] = o;
         }
        }
        """
        ,"/TEST.java:4: error: variable s might not have been initialized", 45
        ,"/TEST.java:5: error: variable a might not have been initialized", 35
        );
    }


    // Set tests
    
    @Test public void jmlset() {
        helpTCText(null, 
                """
                class A {
                    void test() {
                        //@ ghost \\set<\\string> m = 7; // ERROR
                        //@ ghost \\string s = "";
                        Object o = new Object();
                        //@ ghost int x = m[o]; // ERROR
                        //@ ghost int xx = m[s]; // ERROR
                        //@ ghost var z = \\set.<Boolean>of(o, 5); // ERROR
                        //@ check m.contains(o); // ERROR
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
                ,"/TEST.java:3: error: incompatible types: int cannot be converted to \\set<\\string>",37
                ,"/TEST.java:6: error: Expected an index type of \\string, not java.lang.Object",29
                ,"/TEST.java:6: error: incompatible types: boolean cannot be converted to int",28
                ,"/TEST.java:7: error: incompatible types: boolean cannot be converted to int",29
                ,"""
                 /TEST.java:8: error: no suitable method found for of(java.lang.Object,int)
                     method org.jmlspecs.lang.internal.set.<X>of(X...) is not applicable
                       (varargs mismatch; java.lang.Object cannot be converted to java.lang.Boolean)
                     method org.jmlspecs.lang.internal.set.<X>of(X,X) is not applicable
                       (argument mismatch; java.lang.Object cannot be converted to java.lang.Boolean)""", 31
                ,"/TEST.java:9: error: incompatible types: java.lang.Object cannot be converted to \\string", 30
                ,"/TEST.java:10: error: incompatible types: java.lang.Object cannot be converted to \\string", 34
                ,"/TEST.java:11: error: incompatible types: java.lang.Object cannot be converted to \\string", 37
                ,"/TEST.java:13: error: incompatible types: \\set<\\bigint> cannot be converted to \\set<\\string>", 32
                ,"/TEST.java:14: error: incompatible types: \\set<\\bigint> cannot be converted to \\set<\\string>", 38
                ,"/TEST.java:15: error: incompatible types: \\set<\\bigint> cannot be converted to \\set<\\string>", 27
                ,"/TEST.java:16: error: incompatible types: \\set<\\bigint> cannot be converted to \\set<\\string>", 31
                ,"/TEST.java:17: error: incompatible types: \\set<\\bigint> cannot be converted to \\set<\\string>", 30
                ,"/TEST.java:18: error: incompatible types: \\set<\\bigint> cannot be converted to \\set<\\string>", 24
                ,"/TEST.java:19: error: incompatible types: \\set<\\bigint> cannot be converted to \\set<\\string>", 24
                ,"/TEST.java:20: error: No allowed implicit conversion permits this operation on JML types: \\set<\\string> == \\set<\\bigint>", 21
                ,"/TEST.java:21: error: No allowed implicit conversion permits this operation on JML types: \\set<\\string> != \\set<\\bigint>", 21
                ,"/TEST.java:22: error: No operator for \\set<\\string> | java.lang.Object", 30
                ,"/TEST.java:23: error: No operator for java.lang.Object & \\set<\\string>", 30
                ,"/TEST.java:24: error: No operator for java.lang.Object - \\set<\\string>", 30
                ,"/TEST.java:25: error: No allowed implicit conversion permits this operation on JML types: \\set<\\string> < \\set<java.lang.Boolean>", 30
                ,"/TEST.java:26: error: No allowed implicit conversion permits this operation on JML types: \\set<\\string> <= \\set<java.lang.Boolean>", 30

                );
    }

    @Test public void jmlsetFlow() {// Flow tests (won't be detected if there are typechecking errors)
        helpTCText(null, 
        """
        class A {
          void m() {
             Object o = new Object();
            //@ ghost \\set<Short> s; ghost var ss = s;
            //@ ghost \\set<Object> a; set a.add(o);
         }
        }
        """
        ,"/TEST.java:4: error: variable s might not have been initialized", 45
        ,"/TEST.java:5: error: variable a might not have been initialized", 35
        );
    }

    // Map tests

    @Test public void jmlmap() {
        helpTCText(null, 
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
            ,"/TEST.java:3: error: incompatible types: int cannot be converted to \\map<\\string,\\string>", 45
            ,"/TEST.java:6: error: Expected an index type of \\string, not java.lang.Object", 34
            ,"/TEST.java:6: error: incompatible types: \\string cannot be converted to \\bigint", 33
            ,"/TEST.java:8: error: Expected an index type of java.lang.@org.jmlspecs.annotation.NonNull Number, not java.lang.Object", 35
            ,"/TEST.java:9: error: incompatible types: java.lang.Object cannot be converted to @org.jmlspecs.annotation.NonNull java.lang.Number", 29
            ,"/TEST.java:11: error: incompatible types: java.lang.Object cannot be converted to \\string", 28 
            ,"/TEST.java:12: error: incompatible types: java.lang.Object cannot be converted to \\string", 31 
            ,"/TEST.java:13: error: incompatible types: \\map<@org.jmlspecs.annotation.NonNull java.lang.Number,\\string> cannot be converted to \\map<\\string,\\string>",30
            ,"/TEST.java:14: error: incompatible types: java.lang.Object cannot be converted to \\string", 30
        );
    }

    @Test public void jmlmapFlow() {// Flow tests (won't be detected if there are typechecking errors)
        helpTCText(null, 
        """
        class A {
          void m() {
             Object o = new Object();
            //@ ghost \\map<Short,Integer> s; ghost var ss = s;
            //@ ghost \\map<Object,Integer> a; set a.put(o,2);
         }
        }
        """
        ,"/TEST.java:4: error: variable s might not have been initialized", 53
        ,"/TEST.java:5: error: variable a might not have been initialized", 43
        );
    }
    
    @Test public void jmlrangeFlow() {// Flow tests (won't be detected if there are typechecking errors)
        helpTCText(null, 
        """
        class A {
          void m() {
             Object o = new Object();
            //@ ghost \\range s; ghost var ss = s;
            //@ ghost \\range a; check a.isEmpty();
         }
        }
        """
        ,"/TEST.java:4: error: variable s might not have been initialized", 40
        ,"/TEST.java:5: error: variable a might not have been initialized", 31
        );
    }
    
    @Test public void jmlrangeFinal() {
        helpTCText(null, 
        """
          class A {
          //@ ghost public static \\range r = 2 .. 3 ;

          //@ writes a[r];
          void m(int[] a) {
            //@ set var rr = r;
            //@ set var k = r.lo;
            //@ set r.lo = 5;
          }
        }
        """
        ,"/TEST.java:4: error: Index ranges are implemented only for explicit range expressions (using ..)", 16
        ,"/TEST.java:8: error: cannot assign a value to final variable lo", 14
        ,"/TEST.java:8: error: Fields of an object with immutable type may not be modified: r.lo (\\range)", 18
        ,"$SPECS/org/jmlspecs/lang/internal/range.jml:4: error: Associated declaration: /TEST.java:8:", 5
        );
    }
    
    @Test public void jmlrangeParse() {
        helpTCText(null, 
        """
        public class R {
          void m() {
            //@ assert 2 .. 3 == 2 .. 3; // Parsing precedence error
          }
        }
        """
        ,"/TEST.java:3: error: Range operators (..) do not chain and have the lowest precedence; perhaps parentheses are needed",28
        ,"/TEST.java:3: error: Incorrectly formed or terminated assert statement near here",28
        );
    }

    @Test public void jmldatagroup() {
        helpTCText(null, 
        """
        class A {
          //@ public model \\datagroup d; // OK
          //@ public ghost \\datagroup dd = d; // ERROR - initialization not permitted
            void m() {
              //@ ghost \\datagroup da; // ERROR - local \\datagroup declarations not allowed
              //@ set mmm(d); // ERROR
              //@ set d = d; // ERROR
              //@ set d += d; // ERROR
              //@ ghost \\set<\\datagroup> ss; // ERROR
              Object o;
              //@ ghost Object oo = (\\datagroup)o;
            }

            //@ model void mm(\\datagroup d);  // ERRORS - no formal \\datagroup arguments
            //@ model \\datagroup mr();  // ERRORS - no \\datagroup return type

            //@ model void mmm(Object o) {}
        }
        """
        ,"/TEST.java:3: error: \\datagroup declarations may not have initializers", 31
        ,"/TEST.java:5: error: \\datagroup declarations are not permitted as local or formal declarations", 28
        ,"/TEST.java:6: error: incompatible types: \\datagroup cannot be converted to java.lang.Object", 19
        ,"/TEST.java:7: error: \\datagroup fields may not be assigned", 17
        ,"/TEST.java:8: error: No operator for \\datagroup + \\datagroup", 17
        ,"/TEST.java:8: error: \\datagroup fields may not be assigned", 17
        ,"/TEST.java:9: error: \\datatype is not allowed as a type argument", 21
        ,"/TEST.java:11: error: A java.lang.Object may not be cast to a \\datagroup", 41
        ,"/TEST.java:14: error: \\datagroup declarations are not permitted as local or formal declarations", 34
        ,"/TEST.java:15: error: a method return type may not be \\datagroup", 26
        );
    }
    


    // TODO: Review the following

     // FIXME - do we allow direct assignment?
//    @Test public void testArrayType() {
//        helpTCFText(null, " class A { void m() { //@ ghost \\array<Object> b; ghost \\bigint i = 0; ghost Object o = b[i]; set b[i] = o; \n}}"
//                );
//    }

    @Test public void testIntsetType() {
        helpTCText(null, " class A { void m() { //@ ghost \\intset b; havoc b; ghost \\bigint i = 0; ghost boolean o = b[i];  set b[i] = true; \n}}");
    }

    @Test public void testIntmapType() {
        helpTCText(null, " class A { void m() { //@ ghost \\intmap<Object> b; havoc b; ghost \\bigint i = 0; ghost Object o = b[i]; set b[i] = o; \n}}");
    }

   // FIXME - need to be able to initialize JML types
    

    
}
