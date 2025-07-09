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
        helpTC(" class A { void m() {  //@ ghost \\string b; ghost char c = 'a'; set b[c] = 'b'; ghost char bb = b[c]; \n}}");
    }

    // array tests

    @Test public void jmlarray() {
        helpTC(" class A { void m() { //@ ghost \\array<Object> b; ghost \\bigint i = 0; ghost Object o = b[i]; set var bb = b.put(i,o); \n}}"
                );
    }
    // Seq tests

    @Test public void jmlseq() {
        helpTC(" class A { void m() { //@ ghost \\seq<Object> b ; ghost \\bigint i = 0; ghost Object o = b[i]; set b[i] = o; \n}}");
    }
    
    // Set tests
    
    @Test public void jmlset() {
        helpTC(" class A { void m() {  //@ ghost \\set<Object> b ; ghost Object o = new Object(); set b[o] = true; ghost boolean bb = b[o]; \n}}");
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
