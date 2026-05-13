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
                """
                import java.util.Vector; public class A {
                 void m() {
                  Class<?> c = Object.class; Object o = c;
                  //@ ghost \\TYPE t;
                  //@ ghost \\TYPE tt = \\type(Object);
                  //@ set tt = \\type(int);
                  //@ set tt = \\type(Vector<Integer>);
                  //@ ghost \\TYPE ttt = \\typeof(o);
                  //@ ghost boolean b = \\type(Object) == tt;
                  //@ set b = \\typeof(o) == tt;
                  //@ set b = (\\TYPE)c == t; // Casts allowed
                  //@ set t = \\elemtype(t); // Allow elemtype on TYPE, returning TYPE // flow checks not performed because of other errors
                  //@ set c = \\erasure(t); // ERROR - not ghost
                  //@ set b = tt <:= ttt;
                 }
                }
                """
                ,"/A.java:13: error: The LHS in a set statement must be a ghost variable",11
                );
    }

    @Test
    public void testUninitGhostA() {
        helpTCText("A.java",
                """
                import java.util.Vector; public class A {
                 void m() {
                  Class<?> c = Object.class; Object o = c;
                  //@ ghost \\TYPE t; // not initialized
                  //@ ghost \\TYPE tt = \\type(Object);
                  //@ set tt = \\type(int);
                  //@ set tt = \\type(Vector<Integer>);
                  //@ ghost \\TYPE ttt = \\typeof(o);
                  //@ ghost boolean b = \\type(Object) == tt;
                  //@ set b = \\typeof(o) == tt;
                  //@ set b = (\\TYPE)c == t; // Casts allowed
                  //@ set t = \\elemtype(t); // Allow elemtype on TYPE, returning TYPE
                  //@ set b = tt <:= ttt;
                 }
                }
                """
                ,"/A.java:11: error: variable t might not have been initialized",27
                );
    }

    @Test
    public void testOK1() {
        helpTCText("A.java",
                """
                public class A {
                 void m() {
                  Class<?> c = Object.class; Object o = c;
                  //@ ghost boolean b = org.jmlspecs.lang.JML.erasure(\\typeof(o)) == Object.class;
                  //@ set b = org.jmlspecs.lang.JML.typeargs(\\typeof(o)).length == 0;
                  //@ set b = org.jmlspecs.lang.JML.typeargs(\\typeof(o))[0] != \\typeof(o);
                  //@ set b = org.jmlspecs.lang.JML.isArray(\\typeof(o));
                  boolean jb = c.isArray();
                 }
                }
                """
                );
    }

    @Test
    public void testOK2() {
        helpTCText("A.java",
                """
                public class A {
                 void m() {
                  Class<?> c = Object.class; Object o = c;
                  //@ ghost \\TYPE t = \\type(\\real);
                  //@ ghost boolean b = JML.typeargs(\\type(Object)).length == 0;
                  //@ set b = JML.typeargs(\\elemtype(t)).length == 0;
                 }
                }
                """
                );
    }

    @Test
    public void testOK2x() {
        helpTCText("A.java",
                """
                public class A {
                 void m() {
                  //@ ghost \\TYPE t = \\real; // Should be a syntax error
                 }
                }
                """
                ,"/A.java:3: error: Expected an expression here, not a type", 23
                );
    }

    @Test
    public void testOK2a() {
        helpTCText("A.java",
                """
                public class A {
                 void m() {
                  Class<?> c = Object.class; Object o = c;
                  //@ ghost \\TYPE t = \\type(Object);
                  //@ ghost boolean b = JML.typeargs(\\type(Object)).length == 0;
                  //@ set b = JML.typeargs(\\elemtype(t)).length == 0;
                 }
                }
                """
                );
    }

    @Test
    public void testOK3() {
        helpTCText("A.java",
                """
                class B<T> {}
                public class A<T>  {
                 void m() {
                  Class<?> c = Object.class; Object o = c;
                  //@ ghost \\TYPE w = \\type(B<Integer>);
                  //@ ghost \\TYPE t = \\type(B<T>);
                  //@ ghost \\TYPE v = \\type(T);
                 }
                }
                """
                );
    }

    @Test
    public void testBad() {
        helpTCText("A.java",
                """
                public class A {
                 void m() {
                  Class<?> c = Object.class; Object o = c;
                  //@ ghost \\TYPE t = Object.class; // NO mixing
                  //@ ghost Class<?> cc = t; // NO mixing
                  //@ ghost boolean b = \\type(Object) == Object.class; // No mixing
                  //@ ghost Object oo = \\type(Object); // \\TYPE does not convert
                  //@ set b = t <:= Object.class; // No mixing
                  //@ set b = Object.class <:= t; // No mixing
                  //@ set b = c instanceof \\type(Object); // No mixing
                  //@ set b = t instanceof Object; // \\Type is a primitive
                  //@ set t = (\\TYPE)0; // No casts of ints
                  //@ set t = (\\TYPE)o; // No casts of Object
                }}
                """
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
                """
                public class A<T extends java.io.File> {
                 void m() {
                  Class<?> c = T.class;
                }}
                """
                ,"/A.java:3: error: cannot select from a type variable",17
                );
    }

    @Test
    public void testBadJava2() {
        helpTCText("A.java",
                """
                public class A<T extends java.io.File> {
                 void m() {
                  Class<?> c = A<T>.class;
                }}
                """
                ,"/A.java:3: error: <identifier> expected",21
                ,"/A.java:3: error: <identifier> expected",26
                );
    }

}
