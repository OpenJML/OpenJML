package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.*;

import java.util.List;

import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjmltest.ParseBase;
import org.junit.Before;
import org.junit.Test;

import com.sun.tools.javac.tree.JCTree;

/**
 * Tests that JmlClassDecl, JmlMethodDecl, and JmlVariableDecl nodes carry the
 * correct {@code namePosition} value pointing at the first character of the
 * declared name identifier token.
 *
 * <p>Each test parses a small source fragment, locates the first node of the
 * relevant type in a depth-first walk, and asserts that
 * {@code node.namePosition == src.indexOf("<name>")}.
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class namePosition extends ParseBase {

    @Override @Before
    public void setUp() throws Exception {
        super.setUp();
        postOptions();
    }

    /** Returns the first node in {@code nodes} whose runtime class is exactly {@code clazz}. */
    @SuppressWarnings("unchecked")
    private <T extends JCTree> T findFirst(List<JCTree> nodes, Class<T> clazz) {
        for (JCTree n : nodes) {
            if (n.getClass() == clazz) return (T) n;
        }
        return null;
    }

    // -----------------------------------------------------------------------
    // Class-like declarations
    // -----------------------------------------------------------------------

    @Test
    public void testClassNamePosition() {
        String src = "class MyClass {}";
        List<JCTree> nodes = parseCompilationUnit(src);
        JmlClassDecl cd = findFirst(nodes, JmlClassDecl.class);
        assertNotNull("JmlClassDecl must be found", cd);
        assertEquals("class namePosition", src.indexOf("MyClass"), cd.namePosition);
    }

    @Test
    public void testInterfaceNamePosition() {
        String src = "interface MyInterface {}";
        List<JCTree> nodes = parseCompilationUnit(src);
        JmlClassDecl cd = findFirst(nodes, JmlClassDecl.class);
        assertNotNull("JmlClassDecl (interface) must be found", cd);
        assertEquals("interface namePosition", src.indexOf("MyInterface"), cd.namePosition);
    }

    @Test
    public void testEnumNamePosition() {
        String src = "enum MyEnum { A }";
        List<JCTree> nodes = parseCompilationUnit(src);
        JmlClassDecl cd = findFirst(nodes, JmlClassDecl.class);
        assertNotNull("JmlClassDecl (enum) must be found", cd);
        assertEquals("enum namePosition", src.indexOf("MyEnum"), cd.namePosition);
    }

    // -----------------------------------------------------------------------
    // Method declarations
    // -----------------------------------------------------------------------

    @Test
    public void testMethodNamePosition() {
        String src = "class A { void myMethod() {} }";
        List<JCTree> nodes = parseCompilationUnit(src);
        JmlMethodDecl md = findFirst(nodes, JmlMethodDecl.class);
        assertNotNull("JmlMethodDecl must be found", md);
        assertEquals("method namePosition", src.indexOf("myMethod"), md.namePosition);
    }

    // -----------------------------------------------------------------------
    // Variable declarations
    // -----------------------------------------------------------------------

    @Test
    public void testFieldNamePosition() {
        String src = "class A { int myField = 0; }";
        List<JCTree> nodes = parseCompilationUnit(src);
        JmlVariableDecl vd = findFirst(nodes, JmlVariableDecl.class);
        assertNotNull("JmlVariableDecl (field) must be found", vd);
        assertEquals("field namePosition", src.indexOf("myField"), vd.namePosition);
    }

    @Test
    public void testLocalVarNamePosition() {
        String src = "class A { void m() { int localVar = 0; } }";
        List<JCTree> nodes = parseCompilationUnit(src);
        JmlVariableDecl vd = findFirst(nodes, JmlVariableDecl.class);
        assertNotNull("JmlVariableDecl (local) must be found", vd);
        assertEquals("local var namePosition", src.indexOf("localVar"), vd.namePosition);
    }

    @Test
    public void testParameterNamePosition() {
        String src = "class A { void m(int myParam) {} }";
        List<JCTree> nodes = parseCompilationUnit(src);
        JmlVariableDecl vd = findFirst(nodes, JmlVariableDecl.class);
        assertNotNull("JmlVariableDecl (param) must be found", vd);
        assertEquals("param namePosition", src.indexOf("myParam"), vd.namePosition);
    }
}
