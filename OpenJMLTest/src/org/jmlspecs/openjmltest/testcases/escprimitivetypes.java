package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.ParameterizedWithNames;
import org.junit.runners.Parameterized.Parameters;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escprimitivetypes extends EscBase {

    public escprimitivetypes(String options, String solver) {
        super(options,solver);
    }
    
    @Test
    public void testIntset() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1(int i) {\n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2;\n"
                +"    //@ ghost intset a;\n"
                +"    //@ ghost intset b = a;\n"
                +"    //@ set a[ii] = true;\n"
                +"    //@ assert a[ii+1] == b[ii+1];\n"
                +"    //@ assert a[ii] == true;\n"
                +"  }\n"
                
               
                 
                +"}"
//                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method m11a",9
                );
    }
    
    @Test
    public void testSet() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires o != oo;\n"
                +"  public void m1(Object o,Object oo) {\n"
                +"    //@ ghost set<Object> a;\n"
                +"    //@ ghost set<Object> b = a;\n"
                +"    //@ set a[o] = true;\n"
                +"    //@ assert a[oo] == b[oo];\n"
                +"    //@ assert a[o] == true;\n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test
    public void testIntmap() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, Object o) {\n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2;\n"
                +"    //@ ghost intmap<Object> a;\n"
                +"    //@ ghost intmap<Object> b = a;\n"
                +"    //@ set a[ii] = o;\n"
                +"    //@ assert a[ii+1] == b[ii+1];\n"
                +"    //@ assert a[ii] == o;\n"
                +"  }\n"
                
               
                 
                +"}"
//                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method m11a",9
                );
    }
    
    @Test
    public void testArray() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, Object o) {\n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2;\n"
                +"    //@ ghost array<Object> a;\n"
                +"    //@ ghost array<Object> b = a;\n"
                +"    //@ set a[ii] = o;\n"
                +"    //@ assert a[ii+1] == b[ii+1];\n"
                +"    //@ assert a[ii] == o;\n"
                +"  }\n"
                +"}"
                );
    }
    

    @Test
    public void testseq() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, Object o) {\n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2; assume ii >= 0; \n"
                +"    //@ ghost seq<Object> a;\n"
                +"    //@ ghost seq<Object> b = a;\n"
                +"    //@ set a[ii] = o;\n"
                +"    //@ assert a[ii+1] == b[ii+1];\n"
                +"    //@ assert a[ii] == o;\n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test
    public void testmap() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(Object o, Object oo, Object ooo) {\n"
                +"    //@ assume oo != ooo;\n"
                +"    //@ ghost map<Object,Object> a;\n"
                +"    //@ assume a.get(oo) == ooo;\n"
                +"    //@ ghost map<Object,Object> b = a;\n"
                +"    //@ assert a.get(ooo) == b.get(ooo);\n"
                +"    //@ set a = a.put(oo,o);\n"
                +"    //@ assert a.get(ooo) == b.get(ooo);\n"
                +"    //@ assert a.get(oo) == o;\n"
                +"    //@ assert b.get(oo) == ooo;\n"
                +"    //@ set a[oo] = o;\n"
                +"    //@ assert a[ooo] == b[ooo];\n"
                +"    //@ assert a[oo] == o;\n"
                +"    //@ assert b[oo] == ooo;\n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test
    public void teststring() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, char c) {\n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2; assume ii >= 0; \n"
                +"    //@ ghost string a;\n"
                +"    //@ ghost string b = a;\n"
                +"    //@ set a[ii] = c;\n"
                +"    //@ assert a[ii+1] == b[ii+1];\n"
                +"    //@ assert a[ii] == c;\n"
                +"  }\n"
                +"}"
                );
    }
    
    
    @Test
    public void testJavaArray() {
        helpTCX("tt.TestJava","package tt; \n"
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
        helpTCX("tt.TestJava","package tt; \n"
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
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, boolean[] a) {\n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2; \n"
                +"    //@ assume 0 <= ii;\n"
                +"    //@ ghost boolean b = a[ii];\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m1",28
                );
    }

    @Test
    public void testJavaArray2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, boolean[] a) {\n"
                +"    //@ assume i < a.length; \n"
                +"    boolean bb = a[i];\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1",19
                );
    }


    @Test
    public void testJavaArray3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, boolean[] a) {\n"
                +"    //@ assume i >= 0; \n"
                +"    boolean bb = a[i];\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1",19
                );
    }

}
