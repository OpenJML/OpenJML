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
        helpTC(" class A { //@ ghost \\bigint b = 0; \n}");
    }

    @Test public void testMinusBigint() {
        helpTC(" class A { //@ ghost \\bigint b = 0; ghost \\bigint bb = -b; \n}");
    }

    @Test public void testBinaryBigint() {
        helpTC(" class A { void m() { //@ ghost \\bigint b = 0; ghost \\bigint bb = b + b; set bb = b-b; set bb = b*b; set bb = b/b; \n}}");
    }
    
    // real tests
    
    @Test public void jmlreal() {
        helpTC(" class A { //@ ghost \\real b = 0; \n}");
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
                    //@ var cc = b.get(o);
                    //@ set b = b.add(0);
                    //@ set b = b.put(o,0);
                    //@ set b = b.remove(o);
                    //@ set b = b.insert(o,42);
                    //@ set b = b.append(123);
                    //@ set b = \\string.concat(o,o);
                    //@ ghost \\string x = b.head();
                    //@ ghost char c = b.head(1);
                    //@ set b = \\string.of(123);
                    //@ ghost boolean z = b.compareTo("zz"); // OK
                    //@ ghost boolean y = b.compareTo(o); // OK
                    //@ set b = b.substring(o,o);
                  }
                }
                """
                ,"/TEST.java:5: error: incompatible types: java.lang.Object cannot be converted to \\bigint",24
                ,"/TEST.java:6: error: incompatible types: possible lossy conversion from int to char",23
                ,"/TEST.java:7: error: incompatible types: java.lang.Object cannot be converted to \\bigint",23
                ,"/TEST.java:8: error: incompatible types: java.lang.Object cannot be converted to \\bigint",26
                ,"/TEST.java:9: error: incompatible types: java.lang.Object cannot be converted to \\bigint",26
                ,"/TEST.java:10: error: incompatible types: int cannot be converted to \\string",26
                ,"/TEST.java:11: error: incompatible types: java.lang.Object cannot be converted to \\string",32
                ,"/TEST.java:12: error: incompatible types: char cannot be converted to \\string",33
                ,"/TEST.java:13: error: incompatible types: \\string cannot be converted to char",30
                ,"/TEST.java:14: error: incompatible types: int cannot be converted to java.lang.String",28
                ,"/TEST.java:15: error: incompatible types: int cannot be converted to boolean",38
                ,"/TEST.java:16: error: incompatible types: java.lang.Object cannot be converted to \\string",39
                ,"/TEST.java:17: error: incompatible types: java.lang.Object cannot be converted to \\bigint",29
                );
    }

    // array tests

    @Test public void jmlarray() {
        helpTC(" class A { void m() { //@ ghost \\array<Object> b; ghost \\bigint i = 0; ghost Object o = b[i]; set var bb = b.put(i,o); \n}}"
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
                    //@ set b = b.remove(o);
                    //@ set b = b.insert(o,42);
                    //@ set b = b.append(bb);
                    //@ set b = b.prepend(bb);
                    //@ check b == bb && b.eq(bb); check b != bb && b.ne(bb);
                    //@ ghost Boolean x = b.head();
                    //@ ghost char c = b.head(1);
                    //@ ghost char cc = b.tail();
                    //@ ghost char ccc = b.tail(o);
                    //@ set b = \\seq.<Integer>of(true);
                    //@ set bb = b;
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
                ,"/TEST.java:14: error: incompatible types: \\seq<@org.jmlspecs.annotation.NonNull java.lang.Boolean> cannot be converted to \\seq<@org.jmlspecs.annotation.NonNull java.lang.Integer>",31
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
        helpTC(" class A {"
                + "void m() {  //@ ghost \\set<Object> b ; ghost Object o = new Object(); set b[o] = true; ghost boolean bb = b[o]; \n}}");
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
                    //@ set m = m.putAll(mm); // ERROR ------------- FIXME
                    //@ set m = m.remove(o); // ERROR
                }
            }
            """
            ,"/TEST.java:3: error: incompatible types: int cannot be converted to \\map<@org.jmlspecs.annotation.NonNull \\string,@org.jmlspecs.annotation.NonNull \\string>", 45
            ,"/TEST.java:6: error: Expected an index type of \\@org.jmlspecs.annotation.NonNull string, not java.lang.Object", 34
            ,"/TEST.java:8: error: Expected an index type of java.lang.@org.jmlspecs.annotation.NonNull Number, not java.lang.Object", 35
            ,"/TEST.java:9: error: incompatible types: java.lang.Object cannot be converted to @org.jmlspecs.annotation.NonNull java.lang.Number", 29
            ,"/TEST.java:11: error: incompatible types: java.lang.Object cannot be converted to @org.jmlspecs.annotation.NonNull \\string", 28 
            ,"/TEST.java:12: error: incompatible types: java.lang.Object cannot be converted to @org.jmlspecs.annotation.NonNull \\string", 31 
            ,"/TEST.java:13: error: incompatible types: \\map<@org.jmlspecs.annotation.NonNull java.lang.Number,@org.jmlspecs.annotation.NonNull \\string> cannot be converted to \\map<@org.jmlspecs.annotation.NonNull \\string,@org.jmlspecs.annotation.NonNull \\string>",30
            ,"/TEST.java:14: error: incompatible types: java.lang.Object cannot be converted to @org.jmlspecs.annotation.NonNull \\string", 30
        );
    }


    // TOOD: Review the following

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
