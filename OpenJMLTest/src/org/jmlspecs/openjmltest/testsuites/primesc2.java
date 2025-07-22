package org.jmlspecs.openjmltest.testsuites;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

// FIXME - this file likely duplicates tests in primesc

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class primesc2 extends EscBase {

    @Test
    public void testIntset() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1(int i) {\n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2;\n"
                +"    //@ ghost \\intset a;\n"
                +"    //@ set a[ii] = false;\n"  // Line 7
                +"    //@ ghost \\intset b = a;\n"
                +"    //@ set a[ii] = true;\n"
                +"    //@ check a[ii+1] == b[ii+1];\n" // OK // Line 10
                +"    //@ check a[ii] == true;\n"      // OK
                +"    //@ check b[ii] == false;\n"     // OK
                +"  }\n"
                +"}"
                );
    }
    
    @Test
    public void testSet() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires o != oo;\n"
                +"  public void m1(Object o,Object oo) {\n"
                +"    //@ ghost \\set<Object> a;\n"
                +"    //@ set a[o] = false;\n"
                +"    //@ ghost \\set<Object> b = a;\n"
                +"    //@ set a[o] = true;\n"
                +"    //@ check a[oo] == b[oo];\n"
                +"    //@ check a[o] == true;\n"
                +"    //@ check b[o] == false;\n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test
    public void testIntmap() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, Object o, Object oo) {\n"
                +"    //@ assume o != oo;\n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2;\n"
                +"    //@ ghost \\intmap<Object> a;\n"
                +"    //@ set a[ii] = oo;\n"
                +"    //@ ghost \\intmap<Object> b = a;\n"
                +"    //@ set a[ii] = o;\n"
                +"    //@ check a[ii+1] == b[ii+1];\n"
                +"    //@ check a[ii] == o;\n"
                +"    //@ check b[ii] == oo;\n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test @Ignore // a[i] = o not implemented for \array
    public void testArrayBracket() {
        addOptions("--method=m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, Object o, Object oo) {\n"
                +"    //@ assume o != oo;\n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2;\n"
                +"    //@ ghost \\array<Object> a; havoc a;\n"
                +"    //@ set a[ii] = oo;\n"
                +"    //@ ghost \\array<Object> b = a;\n"
                +"    //@ set a[ii] = o;\n"
                +"    //@ check a[ii+1] == b[ii+1];\n"
                +"    //@ check a[ii] == o;\n"
                +"    //@ check b[ii] == oo;\n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test
    public void testseq() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, Object o, Object oo) {\n"
                +"    //@ assume o != oo;\n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2; assume ii >= 0; \n"
                +"    //@ ghost \\seq<Object> a;\n"
                +"    //@ set a[ii] = oo;\n"
                +"    //@ ghost \\seq<Object> b = a;\n"
                +"    //@ set a[ii] = o;\n"
                +"    //@ check a[ii+1] == b[ii+1];\n"
                +"    //@ check a[ii] == o;\n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test
    public void testseqPut() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, Object o, Object oo) {\n"
                +"    //@ assume o != oo;\n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2; assume ii >= 0; \n"
                +"    //@ ghost \\seq<Object> a;\n"
                +"    //@ set a = a.put(ii,oo);\n"
                +"    //@ ghost \\seq<Object> b = a;\n"
                +"    //@ set a = a.put(ii,o);\n"
                +"    //@ check a[ii+1] == b[ii+1];\n"
                +"    //@ check a[ii] == o;\n"
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
                +"    //@ ghost \\map<Object,Object> a;\n"
                +"    //@ set a[oo] = ooo;\n"
                +"    //@ ghost \\map<Object,Object> b = a;\n"
                +"    //@ check a.get(ooo) == b.get(ooo);\n"
                +"    //@ set a[oo] = o;\n"
                +"    //@ check a.get(ooo) == b.get(ooo);\n"
                +"    //@ check a.get(oo) == o;\n"
                +"    //@ check b.get(oo) == ooo;\n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test
    public void testmapPut() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(Object o, Object oo, Object ooo) {\n"
                +"    //@ assume oo != ooo;\n"
                +"    //@ ghost \\map<Object,Object> a;\n"
                +"    //@ set a = a.put(oo,o);\n"
                +"    //@ ghost \\map<Object,Object> b = a;\n"
                +"    //@ check a.get(ooo) == b.get(ooo);\n"
                +"    //@ set a = a.put(oo,oo);\n"
                +"    //@ check a.get(ooo) == b.get(ooo);\n"
                +"    //@ check a.get(oo) == oo;\n"
                +"    //@ check b.get(oo) == o;\n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test
    public void teststring() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i, char c, char cc) {\n"
                +"    //@ assume c != cc; \n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2; assume ii >= 0; \n"
                +"    //@ ghost \\string a;\n"
                +"    //@ set a[ii] = cc;\n"
                +"    //@ ghost \\string b = a;\n"
                +"    //@ set a[ii] = c;\n"
                +"    //@ check a[ii+1] == b[ii+1];\n"
                +"    //@ check a[ii] == c;\n"
                +"    //@ check b[ii] == cc;\n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test
    public void teststringPut() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(String aa, int i, char c, char cc) {\n"
                +"    //@ assume c != cc; \n"
                +"    //@ ghost \\bigint ii = i; set ii = ii*2; assume ii >= 0; \n"
                +"    //@ ghost \\string a = aa;\n"
                +"    //@ assume 0 <= ii <= a.length();\n"
                +"    //@ set a = a.put(ii,cc);\n"
                +"    //@ ghost \\string b = a;\n"
                +"    //@ set a = a.put(ii,c);\n"
                +"    //@ check a[ii+1] == b[ii+1];\n"
                +"    //@ check a[ii] == c;\n"
                +"    //@ check b[ii] == cc;\n"
                +"  }\n"
                +"}"
                );
    }

}
