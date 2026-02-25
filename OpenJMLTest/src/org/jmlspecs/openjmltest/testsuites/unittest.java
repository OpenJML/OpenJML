package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.JmlTestSuite;
import org.openjml.*;

import static org.junit.Assert.*;
import org.junit.Test;

/** This suite holds some low-level unit tests (rather than the functional
 * tests in most of the other test suites)
 */
public class unittest extends JmlTestSuite {
    
    @Test
    public void mockfile() {
        var f1 = new MockJavaFileObject("A.java","");
        var f2 = new MockJavaFileObject("B.java","");
        var f3 = new MockJavaFileObject("A.java","abc");
        var f4 = new MockJavaFileObject("A.jml","");
        assertFalse(f1.equals(f2));
        assertTrue(f1.equals(f3));
        assertFalse(f1.equals(f4));
        assertFalse(f1.equals(new Object()));
        assertEquals( "/A.java",f1.toString());
        assertEquals("abc", f3.getCharContent(false));
    }
    
    @Test
    public void mockfileHashcode() {
        var f1 = new MockJavaFileObject("A.java","");
        var f3 = new MockJavaFileObject("A.java","");
        var f4 = new MockJavaFileObject("t/../A.java","");
        assertTrue(f1.hashCode() == f3.hashCode());
        assertTrue(f1.hashCode() == f4.hashCode());
    }
    
    @Test
    public void mockfileMap() {
        var f1 = new MockJavaFileObject("A.java","");
        assertTrue(mockFiles.isEmpty());
        addMockFile("A.java", f1);
        assertTrue(!mockFiles.isEmpty());
        var f2 = mockFiles.get("A.java");
        assertTrue(f1 == f2);
        var f3 = mockFiles.get("B.java");
        assertTrue(f3 == null);
        mockFiles.clear();
        assertTrue(mockFiles.isEmpty());
        
    }
    
    @Test
    public void span() {
        var sp = new org.openjml.IProverResult.Span(3,5, org.openjml.IProverResult.Span.NORMAL);
        String s = sp.toString();
        assertEquals("[3:5 0]", s);
    }
}