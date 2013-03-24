package tests;

import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class escnew2 extends EscBase {

    public escnew2(String option, String solver) {
        super(option,solver);
    }
    
    @Parameters
    static public  Collection<String[]> datax() {
        return noOldData();
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        main.addOptions("-noPurityCheck");
        //options.put("-jmlverbose",   "");
        //options.put("-method",   "m2bad");
        //options.put("-showbb",   "");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //options.put("-showce",   "");
        //options.put("-trace",   "");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }


    @Test
    public void testNullReceiver() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m() {}; \n"
                
                +"  public static void sm() {}; \n"
                
                +"  //@ signals_only Exception; \n"
                +"  public void mm1(/*@ nullable*/TestJava t) throws Exception {\n"
                +"      t.m();\n"
                +"  }\n"
                
                +"  //@ signals_only Exception; \n"
                +"  public void mm2(/*@ nullable*/TestJava t) throws Exception {\n"
                +"      t.sm();\n"
                +"  }\n"
                
                +"  //@ signals_only Exception; \n"
                +"  public void mm3(/*@ nullable*/TestJava t) throws Exception {\n"
                +"      TestJava.sm();\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (PossiblyNullReference) in method mm1",7
                );
    }
    
    
    @Test
    public void testBreak() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures i == 0 ==> \\result == 6; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n"
                +"  public int m1good(int i) throws Exception {\n"
                +"      int k = 0;\n"
                +"       out: {\n"
                +"        in: { if (i ==1) break in;\n"
                +"              if (i ==2) break out;\n"
                +"              k=5;\n"
                +"        } k++; \n"
                +"       } \n"
                +"      return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 7; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n"
                +"  public int m1bad(int i) throws Exception {\n" // Line 19
                +"      int k = 0;\n"
                +"       out: {\n"
                +"        in: { if (i ==1) break in;\n"
                +"              if (i ==2) break out;\n"
                +"              k=5;\n"
                +"        } k++; \n"
                +"       } \n"
                +"      return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 6; \n"
                +"  //@ ensures i == 1 ==> \\result == 2; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n"
                +"  public int m2bad(int i) throws Exception {\n"
                +"      int k = 0;\n"
                +"       out: {\n"
                +"        in: { if (i ==1) break in;\n"
                +"              if (i ==2) break out;\n"
                +"              k=5;\n"
                +"        } k++; \n"
                +"       } \n"
                +"      return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 6; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 9; \n"
                +"  public int m3bad(int i) throws Exception {\n"
                +"      int k = 0;\n"
                +"       out: {\n"
                +"        in: { if (i ==1) break in;\n"
                +"              if (i ==2) break out;\n"
                +"              k=5;\n"
                +"        } k++; \n"
                +"       } \n"
                +"      return k;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",7
                ,"/tt/TestJava.java:16: warning: Associated declaration",7
                ,"/tt/TestJava.java:40: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",7
                ,"/tt/TestJava.java:30: warning: Associated declaration",7
                ,"/tt/TestJava.java:53: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",7
                ,"/tt/TestJava.java:44: warning: Associated declaration",7
                );
    }
    
    @Test
    public void testSwitch2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures i == 0 ==> \\result == 2; \n"
                +"  //@ ensures i == 1 ==> \\result == 3; \n"
                +"  //@ ensures i == 2 ==> \\result == 5; \n"
                +"  public int m1good(int i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 0; \n"
                +"  //@ ensures i == 1 ==> \\result == 3; \n"
                +"  //@ ensures i == 2 ==> \\result == 5; \n"
                +"  public int m1bad(int i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 2; \n"
                +"  //@ ensures i == 1 ==> \\result == 0; \n"
                +"  //@ ensures i == 2 ==> \\result == 5; \n"
                +"  public int m2bad(int i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 2; \n"
                +"  //@ ensures i == 1 ==> \\result == 3; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n"
                +"  public int m3bad(int i) throws Exception {\n"
                +"      int k = 2;\n"
                +"       switch (i) {\n"
                +"        default: if (i==1) { k=3; break;} else break; \n"
                +"        case 2: k = 5; \n"
                +"       } return k;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:21: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",10
                ,"/tt/TestJava.java:13: warning: Associated declaration",7
                ,"/tt/TestJava.java:31: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",10
                ,"/tt/TestJava.java:24: warning: Associated declaration",7
                ,"/tt/TestJava.java:41: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",10
                ,"/tt/TestJava.java:35: warning: Associated declaration",7
                );
    }
    
    @Test
    public void testTryNested() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures i == 0 ==> \\result == 5; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 2; \n"
                +"  //@ ensures i == 3 ==> \\result == 3; \n"
                +"  //@ ensures i == 4 ==> \\result == 3; \n"
                +"  public int m1good(int i) throws Exception {\n" // Line 8
                +"      try {\n"
                +"        try { if (i>=1) return 1; \n"
                +"        } finally { \n"
                +"          if (i==2 || i == 4) return 2; \n"
                +"        }\n"
                +"      } finally { \n"
                +"          if (i>=3) return 3; \n"
                +"      }\n"
                +"      return 5;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 0; \n" // ERROR
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 2; \n"
                +"  //@ ensures i == 3 ==> \\result == 3; \n"
                +"  //@ ensures i == 4 ==> \\result == 3; \n"
                +"  public int m1bad(int i) throws Exception {\n" // Line 24
                +"      try {\n"
                +"        try { if (i>=1) return 1; \n"
                +"        } finally { \n"
                +"          if (i==2 || i == 4) return 2; \n"
                +"        }\n"
                +"      } finally { \n"
                +"          if (i>=3) return 3; \n"
                +"      }\n"
                +"      return 5;\n" // ERROR
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 5; \n"
                +"  //@ ensures i == 1 ==> \\result == 0; \n" // ERROR
                +"  //@ ensures i == 2 ==> \\result == 2; \n"
                +"  //@ ensures i == 3 ==> \\result == 3; \n"
                +"  //@ ensures i == 4 ==> \\result == 3; \n"
                +"  public int m2bad(int i) throws Exception {\n" // Line 40
                +"      try {\n"
                +"        try { if (i>=1) return 1; \n" // ERROR
                +"        } finally { \n"
                +"          if (i==2 || i == 4) return 2; \n"
                +"        }\n"
                +"      } finally { \n"
                +"          if (i>=3) return 3; \n"
                +"      }\n"
                +"      return 5;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 5; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n" // ERROR
                +"  //@ ensures i == 3 ==> \\result == 3; \n"
                +"  //@ ensures i == 4 ==> \\result == 3; \n"
                +"  public int m3bad(int i) throws Exception {\n" // Line 56
                +"      try {\n"
                +"        try { if (i>=1) return 1; \n"
                +"        } finally { \n"
                +"          if (i==2 || i == 4) return 2; \n" // ERROR
                +"        }\n"
                +"      } finally { \n"
                +"          if (i>=3) return 3; \n"
                +"      }\n"
                +"      return 5;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 5; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 2; \n"
                +"  //@ ensures i == 3 ==> \\result == 0; \n" // ERROR
                +"  //@ ensures i == 4 ==> \\result == 3; \n"
                +"  public int m4bad(int i) throws Exception {\n" // Line 72
                +"      try {\n"
                +"        try { if (i>=1) return 1; \n"
                +"        } finally { \n"
                +"          if (i==2 || i == 4) return 2; \n"
                +"        }\n"
                +"      } finally { \n"
                +"          if (i>=3) return 3; \n" // ERROR
                +"      }\n"
                +"      return 5;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 5; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 2; \n"
                +"  //@ ensures i == 3 ==> \\result == 3; \n"
                +"  //@ ensures i == 4 ==> \\result == 0; \n" // ERROR
                +"  public int m5bad(int i) throws Exception {\n" // Line 88
                +"      try {\n"
                +"        try { if (i>=1) return 1; \n"
                +"        } finally { \n"
                +"          if (i==2 || i == 4) return 2; \n"
                +"        }\n"
                +"      } finally { \n"
                +"          if (i>=3) return 3; \n" // ERROR
                +"      }\n"
                +"      return 5;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:33: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",7
                ,"/tt/TestJava.java:19: warning: Associated declaration",7
                ,"/tt/TestJava.java:42: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",25
                ,"/tt/TestJava.java:36: warning: Associated declaration",7
                ,"/tt/TestJava.java:60: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",31
                ,"/tt/TestJava.java:53: warning: Associated declaration",7
                ,"/tt/TestJava.java:79: warning: The prover cannot establish an assertion (Postcondition) in method m4bad",21
                ,"/tt/TestJava.java:70: warning: Associated declaration",7
                ,"/tt/TestJava.java:95: warning: The prover cannot establish an assertion (Postcondition) in method m5bad",21
                ,"/tt/TestJava.java:87: warning: Associated declaration",7
                );
    }
    
    
    

}
