package org.openjml.lsp.test;

import org.junit.Test;
import org.openjml.lsp.JavaSourceScanner;

import static org.junit.Assert.*;

/**
 * Unit tests for the pure text-scanning methods of {@link JavaSourceScanner}:
 * {@link JavaSourceScanner#findPackage} and {@link JavaSourceScanner#findClassName}.
 *
 * <p>{@link JavaSourceScanner#findMethods} and
 * {@link JavaSourceScanner#findMethodsFromAst} are covered by {@link CodeLensTest}.
 */
public class JavaSourceScannerTest {

    // -----------------------------------------------------------------------
    // findPackage
    // -----------------------------------------------------------------------

    @Test
    public void testFindPackagePresent() {
        String src = "package com.example;\npublic class Foo {}\n";
        assertEquals("com.example", JavaSourceScanner.findPackage(src));
    }

    @Test
    public void testFindPackageAbsent() {
        String src = "public class Foo {}\n";
        assertEquals("", JavaSourceScanner.findPackage(src));
    }

    @Test
    public void testFindPackageNull() {
        assertEquals("", JavaSourceScanner.findPackage(null));
    }

    @Test
    public void testFindPackageMultiSegment() {
        String src = "package org.jmlspecs.openjml;\npublic class Bar {}\n";
        assertEquals("org.jmlspecs.openjml", JavaSourceScanner.findPackage(src));
    }

    @Test
    public void testFindPackageWithLeadingComment() {
        // Block comment before the package declaration must not confuse the regex
        String src = "/* Copyright */\npackage com.example;\npublic class Foo {}\n";
        assertEquals("com.example", JavaSourceScanner.findPackage(src));
    }

    // -----------------------------------------------------------------------
    // findClassName
    // -----------------------------------------------------------------------

    @Test
    public void testFindClassNameSimpleClass() {
        String src = "public class Foo {}\n";
        assertEquals("Foo", JavaSourceScanner.findClassName(src));
    }

    @Test
    public void testFindClassNameInterface() {
        String src = "public interface IFoo {}\n";
        assertEquals("IFoo", JavaSourceScanner.findClassName(src));
    }

    @Test
    public void testFindClassNameEnum() {
        String src = "public enum Color { RED, GREEN, BLUE }\n";
        assertEquals("Color", JavaSourceScanner.findClassName(src));
    }

    @Test
    public void testFindClassNameAbstractClass() {
        String src = "public abstract class Base {}\n";
        assertEquals("Base", JavaSourceScanner.findClassName(src));
    }

    @Test
    public void testFindClassNameAbsent() {
        // No public/protected class declaration — package-private class
        String src = "class PackagePrivate {}\n";
        assertEquals("", JavaSourceScanner.findClassName(src));
    }

    @Test
    public void testFindClassNameNull() {
        assertEquals("", JavaSourceScanner.findClassName(null));
    }

    @Test
    public void testFindClassNameSkipsBlockComment() {
        // A class keyword inside a block comment must NOT be returned
        String src =
                "/* public class Fake {} */\n" +
                "public class Real {}\n";
        assertEquals("Real", JavaSourceScanner.findClassName(src));
    }

    @Test
    public void testFindClassNameSkipsLineComment() {
        // A class keyword in a line comment must NOT be returned
        String src =
                "// public class Fake {}\n" +
                "public class Real {}\n";
        assertEquals("Real", JavaSourceScanner.findClassName(src));
    }

    @Test
    public void testFindClassNameRecord() {
        // Record (Java 16+)
        String src = "public record Point(int x, int y) {}\n";
        assertEquals("Point", JavaSourceScanner.findClassName(src));
    }

    // -----------------------------------------------------------------------
    // methodFqn (integration of findPackage + findClassName)
    // -----------------------------------------------------------------------

    @Test
    public void testMethodFqnWithPackage() {
        String src = "package com.example;\npublic class MyClass {\n    public void go() {}\n}\n";
        assertEquals("com.example.MyClass.go", JavaSourceScanner.methodFqn(src, "go"));
    }

    @Test
    public void testMethodFqnWithoutPackage() {
        String src = "public class MyClass {\n    public void go() {}\n}\n";
        assertEquals("MyClass.go", JavaSourceScanner.methodFqn(src, "go"));
    }

    @Test
    public void testMethodFqnNoClass() {
        // Neither package nor class found — returns just the method name
        String src = "class PackagePrivate { void go() {} }\n";
        assertEquals("go", JavaSourceScanner.methodFqn(src, "go"));
    }
}
