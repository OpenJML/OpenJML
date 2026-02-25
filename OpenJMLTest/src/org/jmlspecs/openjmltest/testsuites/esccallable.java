package org.jmlspecs.openjmltest.testsuites;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class esccallable extends EscBase {

    @Test
    public void testBasicCallable() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable \\nothing;\n"
                +"  public void m() {}\n"
                +"}"
                );
    }

    @Test
    public void testBasicCallable2() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n;\n"
                +"  void m() { n(); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testBasicCallable3() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable \\nothing;\n"
                +"  public void m() { n(); }\n"
                +"  void n() {}\n"
                +"}"
                ,anyorder(seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.n() is not callable",22
                                ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                         ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",22
                                 ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                                 )
                );
    }

    @Test
    public void testBasicCallable4() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n;\n"
                +"  void m() { p(); }\n"
                +"  void n() {}\n"
                +"  void p() {}\n"
                +"}"
                ,anyorder(seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.p() is not callable",15
                                ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                                ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",15
                                        ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                          )
                );
    }

    @Test
    public void testBasicCallable5() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n;\n"
                +"  void m() { B.n(); }\n"
                +"  void n() {}\n"
                +"  void p() {}\n"
                +"}\n"
                +"class B { public static void n() {} };\n"
                ,anyorder(seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: tt.B.n() is not callable",17
                                ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                         ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",17
                                 ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                         )
                );
    }

    @Test
    public void testBasicCallable6() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable TestJava.n;\n"
                +"  void m() { B.n(); }\n"
                +"  static void n() {}\n"
                +"  void p() {}\n"
                +"}\n"
                +"class B { public static void n() {} };\n"
                ,anyorder(seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: tt.B.n() is not callable",17
                                ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                         ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",17
                                 ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                        )
                );
    }

    @Test
    public void testBasicCallable7() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable B.n;\n"
                +"  void m() { B.n(); }\n"
                +"  void n() {}\n"
                +"  void p() {}\n"
                +"}\n"
                +"class B { \n"
                +"  //@ callable \\nothing;\n"
                +"  public static void n() {} };\n"
                );
    }

    @Test
    public void testBasicCallable8() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(int);\n"
                +"  void m() { n(1); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(int i) {}\n"
                +"  void n(Object o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable9() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(Object);\n"
                +"  void m() { n(1); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(int i) {}\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(Object o) {}\n"
                +"}\n"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.n(int) is not callable",15
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable10() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(int);\n"
                +"  void m() { n(1); }\n"
                +"  //@ callable n(Object);\n"
                +"  void n(int i) {}\n"
                +"  void n(Object o) {}\n"
                +"}\n"
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.n(Object) is not callable",16
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable11() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(int),n(Object);\n"
                +"  void m() { n(1); }\n"
                +"  //@ callable n(Object);\n"
                +"  void n(int i) {}\n"
                +"  void n(Object o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable11a() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(int),n(Object);\n"
                +"  void m() { n(1); }\n"
                +"  //@ callable \\everything;\n"
                +"  void n(int i) {}\n"
                +"  void n(Object o) {}\n"
                +"}\n"
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",16
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable11b() { // OK
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable \\everything;\n"
                +"  void m() { n(1); }\n"
                +"  //@ callable \\everything;\n"
                +"  void n(int i) {}\n"
                +"  void n(Object o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable11c() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable \\nothing;\n"
                +"  void m() { n(1); }\n"
                +"  //@ callable \\everything;\n"
                +"  void n(int i) {}\n"
                +"  void n(Object o) {}\n"
                +"}\n"
                ,anyorder(seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.n(int) is not callable",15
                                ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                         ,seq("/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",16
                                 ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                        )
                );
    }

    @Test
    public void testBasicCallable11d() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable \\nothing;\n"
                +"  void m() { n(1); }\n"
                +"  void n(int i) {}\n" // default callable everything
                +"  void n(Object o) {}\n"
                +"}\n"
                ,anyorder(seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.n(int) is not callable",15
                            ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                          ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",15
                                    ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                           )
                );
    }

    @Test
    public void testBasicCallable11e() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(int);\n"
                +"  void m() { n(1); }\n"
                +"  void n(int i) {}\n" // default callable everything
                +"  void n(Object o) {}\n"
                +"}\n"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",15
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable11f() { // OK
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable \\everything;\n"
                +"  void m() { n(1); }\n"
                +"  void n(int i) {}\n" // default callable everything
                +"  void n(Object o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable12() {  // OK
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n();\n"
                +"  void m(Object o) { n(o); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(Object ... o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable12a() { // OK
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(Object,Object);\n"
                +"  void m(Object o) { n(o); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(Object ... o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable13() { // OK
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(Object[]);\n"
                +"  void m() { n(); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(Object ... o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable14() { // OK
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(Object[]);\n"
                +"  void m(Object o) { n(o); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(Object ... o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable15() { // OK
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(Object[]);\n"
                +"  void m(Object[] o) { n(o); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(Object ... o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable16() { // OK
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(Object[]);\n"
                +"  void m(Object o) { n(o,o); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(Object ... o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable20() { // OK
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ callable n();\n"
                +"  //@ also requires !b;\n"
                +"  //@ callable \\nothing;\n"
                +"  void m(boolean b) { if (b) n(); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n() {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable21() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ callable n();\n"
                +"  //@ also requires !b;\n"
                +"  //@ callable \\nothing;\n"
                +"  void m(boolean b) { if (!b) n(); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n() {}\n"
                +"}\n"
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.n() is not callable",32
                ,"/tt/TestJava.java:6: verify: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable21a() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ callable n();\n"
                +"  //@ also requires !b;\n"
                +"  //@ callable \\nothing;\n"
                +"  void m(boolean b) { if (!b) n(); }\n"
                +"  void n() {}\n" // default callable everything
                +"}\n"
                ,anyorder(seq("/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.n() is not callable",32
                                ,"/tt/TestJava.java:6: verify: Associated declaration",7)
                            ,seq("/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",32
                                    ,"/tt/TestJava.java:6: verify: Associated declaration",7)
                        )
                );
    }

    @Test
    public void testBasicCallable21c() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ callable n();\n"
                +"  //@ also requires !b;\n"
                +"  //@ callable \\nothing;\n"
                +"  void m(boolean b) { if (b) n(); }\n"
                +"  void n() {}\n" // default callable everything
                +"}\n"
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",31
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable21b() { // OK
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ callable n();\n"
                +"  //@ also requires !b;\n"
                +"  //@ callable \\everything;\n"
                +"  void m(boolean b) { if (!b) n(); }\n"
                +"  void n() {}\n" // default callable everything
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable22() { // OK
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ callable n(boolean);\n"
                +"  //@ also requires !b;\n"
                +"  //@ callable \\nothing;\n"
                +"  void m(boolean b) { if (b) n(!b); }\n"
                +"  //@ requires q; callable p();\n"
                +"  //@ also requires !q; callable \\nothing;\n"
                +"  void n(boolean q) {}\n"
                +"  void p() {}\n"
                +"}\n"
                );
    }
}
