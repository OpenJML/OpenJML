package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.*;

/** These tests do typechecking on all the aspects of JML types.
 * <BR> \TYPE - the type of types in JML, somewhat like, but not equivalent to Class<?>
 * <BR> \type - (type \TYPE) type literal in JML, similar to T.class
 * <BR> \typeof - (type \TYPE) dynamic type in JML, similar to getClass()
 * <BR> \elemtype - element type of array type
 * <BR> <:= - is subtype of - similar to isAssignableFrom
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class jmltypes extends TCBase {

    @Test
    public void testUninitGhost() {
        helpTCText("A.java",
                "import java.util.Vector; public class A { \n" +
                        " void m() {\n" +
                        "  Class<?> c = Object.class; Object o = c; \n" +
                        "  //@ ghost \\TYPE t;\n" +
                        "  //@ ghost \\TYPE tt = \\type(Object);\n" +
                        "  //@ set tt = \\type(int);\n" +
                        "  //@ set tt = \\type(Vector<Integer>);\n" +
                        "  //@ ghost \\TYPE ttt = \\typeof(o);\n" +
                        "  //@ ghost boolean b = \\type(Object) == tt;\n" +
                        "  //@ set b = \\typeof(o) == tt;\n" +
                        "  //@ set b = (\\TYPE)c == t; \n" + // Casts allowed
                        "  //@ set t = \\elemtype(t); \n" + // Allow elemtype on TYPE, returning TYPE // flow checks not performed because of other errors
                        "  //@ set c = \\erasure(t); \n" +  // ERROR - not ghost
                        "  //@ set b = tt <:= ttt;\n" +
                        " }\n" +
                        "}\n"
                        ,"/A.java:13: error: The LHS in a set statement must be a ghost variable",11
                );
    }

    @Test
    public void testUninitGhostA() {
        helpTCText("A.java",
                "import java.util.Vector; public class A { \n" +
                        " void m() {\n" +
                        "  Class<?> c = Object.class; Object o = c; \n" +
                        "  //@ ghost \\TYPE t;\n" + // not initialized
                        "  //@ ghost \\TYPE tt = \\type(Object);\n" +
                        "  //@ set tt = \\type(int);\n" +
                        "  //@ set tt = \\type(Vector<Integer>);\n" +
                        "  //@ ghost \\TYPE ttt = \\typeof(o);\n" +
                        "  //@ ghost boolean b = \\type(Object) == tt;\n" +
                        "  //@ set b = \\typeof(o) == tt;\n" +
                        "  //@ set b = (\\TYPE)c == t; \n" + // Casts allowed
                        "  //@ set t = \\elemtype(t); \n" + // Allow elemtype on TYPE, returning TYPE
                        "  //@ set b = tt <:= ttt;\n" +
                        " }\n" +
                        "}\n"
                        ,"/A.java:11: error: variable t might not have been initialized",27
                );
    }

    @Test
    public void testOK1() {
        helpTCText("A.java",
                "public class A { \n" +
                        " void m() {\n" +
                        "  Class<?> c = Object.class; Object o = c; \n" +
                        "  //@ ghost boolean b = org.jmlspecs.lang.JML.erasure(\\typeof(o)) == Object.class;\n" +
                        "  //@ set b = org.jmlspecs.lang.JML.typeargs(\\typeof(o)).length == 0;\n" +
                        "  //@ set b = org.jmlspecs.lang.JML.typeargs(\\typeof(o))[0] != \\typeof(o);\n" +
                        "  //@ set b = org.jmlspecs.lang.JML.isArray(\\typeof(o));\n" +
                        "  boolean jb = c.isArray();\n" +
                        " }\n" +
                        "}\n"
                );
    }

    @Test
    public void testOK2() {
        helpTCText("A.java",
                "public class A { \n" +
                        " void m() {\n" +
                        "  Class<?> c = Object.class; Object o = c; \n" +
                        "  //@ ghost \\TYPE t = \\type(\\real);\n" +
                        "  //@ ghost boolean b = JML.typeargs(\\type(Object)).length == 0;\n" +
                        "  //@ set b = JML.typeargs(\\elemtype(t)).length == 0;\n" +
                        " }\n" +
                        "}\n"
                );
    }

    @Test
    public void testOK2x() {
        helpTCText("A.java",
                "public class A { \n" +
                        " void m() {\n" +
                        "  //@ ghost \\TYPE t = \\real;\n" + // Should be a syntax error
                        " }\n" +
                        "}\n"
                        ,"/A.java:3: error: Expected an expression here, not a type", 23
                );
    }

    @Test
    public void testOK2a() {
        helpTCText("A.java",
                "public class A { \n" +
                        " void m() {\n" +
                        "  Class<?> c = Object.class; Object o = c; \n" +
                        "  //@ ghost \\TYPE t = \\type(Object);\n" +
                        "  //@ ghost boolean b = JML.typeargs(\\type(Object)).length == 0;\n" +
                        "  //@ set b = JML.typeargs(\\elemtype(t)).length == 0;\n" +
                        " }\n" +
                        "}\n"
                );
    }

    @Test
    public void testOK3() {
        helpTCText("A.java",
                "class B<T> {}\n" +
                        "public class A<T>  { \n" +
                        " void m() {\n" +
                        "  Class<?> c = Object.class; Object o = c; \n" +
                        "  //@ ghost \\TYPE w = \\type(B<Integer>);\n" +
                        "  //@ ghost \\TYPE t = \\type(B<T>);\n" +
                        "  //@ ghost \\TYPE v = \\type(T);\n" +
                        " }\n" +
                        "}\n"
                );
    }

    @Test
    public void testBad() {
        helpTCText("A.java",
                "public class A { \n" +
                        " void m() {\n" +
                        "  Class<?> c = Object.class; Object o = c; \n" +
                        "  //@ ghost \\TYPE t = Object.class;\n" + // NO mixing
                        "  //@ ghost Class<?> cc = t;\n" + // NO mixing
                        "  //@ ghost boolean b = \\type(Object) == Object.class;\n" + // No mixing
                        "  //@ ghost Object oo = \\type(Object);\n" +  // \TYPE does not convert
                        "  //@ set b = t <:= Object.class;\n" +  // No mixing
                        "  //@ set b = Object.class <:= t;\n" +  // No mixing 
                        "  //@ set b = c instanceof \\type(Object);\n" +  // No mixing
                        "  //@ set b = t instanceof Object;\n" + // \Type is a primitive
                        "  //@ set t = (\\TYPE)0;\n" + // No casts of ints
                        "  //@ set t = (\\TYPE)o;\n" + // No casts of Object
                        "}}\n"
                        ,"/A.java:4: error: incompatible types: java.lang.Class<java.lang.Object> cannot be converted to \\TYPE",29
                        ,"/A.java:5: error: incompatible types: \\TYPE cannot be converted to java.lang.Class<?>",27
                        ,"/A.java:6: error: No operator for \\TYPE == java.lang.Class<java.lang.Object>",39
                        ,"/A.java:7: error: incompatible types: \\TYPE cannot be converted to java.lang.Object", 30  // FIXME - fix position
                        ,"/A.java:8: error: The arguments to <:= must both be \\TYPE or both be Class: \\TYPE and java.lang.Class<java.lang.Object>",27
                        ,"/A.java:9: error: The arguments to <:= must both be \\TYPE or both be Class: java.lang.Class<java.lang.Object> and \\TYPE",32
    // FIXME                    ,"/A.java:10: error: unexpected type\n  required: class\n  found:    value",33
                        ,"/A.java:11: error: A \\TYPE may not be cast to a java.lang.Object",15
                        ,"/A.java:12: error: A int may not be cast to a \\TYPE",22
                        ,"/A.java:13: error: A java.lang.Object may not be cast to a \\TYPE",22

                );
    }

    @Test
    public void testBadJava() {
        helpTCText("A.java",
                "public class A<T extends java.io.File> { \n" +
                        " void m() {\n" +
                        "  Class<?> c = T.class; \n" +
                        "}}\n"
                        ,"/A.java:3: error: cannot select from a type variable",17
                );
    }

    @Test
    public void testBadJava2() {
        helpTCText("A.java",
                "public class A<T extends java.io.File> { \n" +
                        " void m() {\n" +
                        "  Class<?> c = A<T>.class; \n" +
                        "}}\n"
                        ,"/A.java:3: error: <identifier> expected",21
                        ,"/A.java:3: error: <identifier> expected",26
                );
    }

}
