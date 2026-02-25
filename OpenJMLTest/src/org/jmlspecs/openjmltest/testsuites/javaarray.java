package org.jmlspecs.openjmltest.testsuites;

//import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class javaarray extends EscBase {

    @Test
    public void testJavaArray() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, boolean[] a) {\n"
                +"    //@ assume a.length > 10 && i > 0 && i < a.length;\n"
                +"    boolean bb = a[i];\n"
                +"    int len = a.length;\n"
                +"    a[0] = false;\n"
                +"    boolean[] b = a;\n"
                +"    a[i] = true;\n"
                +"    //@ assert !b[0] && b[i];\n"
                +"  }\n"
                +"}"
                );
    }

    @Test
    public void testJavaArray1() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, boolean[] a) {\n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2; \n"
                +"    //@ assume 0 <= ii && ii < a.length;\n"
                +"    //@ ghost boolean b = a[ii];\n"
                +"  }\n"
                +"}"
                );
    }

    @Test
    public void testJavaArray1a() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, boolean[] a) {\n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2; \n"
                +"    //@ assume 0 <= ii < 1000;\n"
                +"    //@ ghost boolean b = a[ii];\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m1",28
                );
    }

    @Test
    public void testJavaArray2() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, boolean[] a) {\n"
                +"    //@ assume i < a.length; \n"
                +"    boolean bb = a[i];\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1",19
                );
    }

    @Test
    public void testJavaArray3() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, boolean[] a) {\n"
                +"    //@ assume i >= 0; \n"
                +"    boolean bb = a[i];\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1",19
                );
    }
}
