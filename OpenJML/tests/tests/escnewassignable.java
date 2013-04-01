package tests;

import java.util.Collection;

import org.jmlspecs.openjml.esc.JmlEsc;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class escnewassignable extends EscBase {

    // Forms to test: x, this.x, , this.*
    // xx, T.xx, tt.T.x, T.* tt.T.*
    // o.x o.oo.x, m(o).x o.*, o.oo.*, m(o).* 
    // a[i].x a[i].* a[*].x a[*].* a[i .. j].x a[i ..*].x a[*..j].x a[*..*].x a[i .. j].* a[i ..*].* a[*..j].* a[*..*].*
    // a[i] a[i..j] a[*] a[i..*] a[*..j] a[*..*]
    // \everything \nothing \not_specified
    
    public escnewassignable(String option, String solver) {
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
        //options.put("-show",   "");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //options.put("-showce",   "");
        //options.put("-trace",   "");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }

    @Test
    public void testAssignable1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int x,y; \n"

                +"  //@ assignable x; \n"
                +"  public void m1bad(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"  //@ assignable x; \n"
                +"  public void m1good(int i) {\n"
                +"    x = 0 ;\n"
                +"    i = 0; ;\n"
                +"    int k = 0; ;\n"
                +"    k = 0; ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assignable) in method m1bad",7
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignable2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int x; \n"

                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  public void mgood(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  public void m1good(int i) {\n"
                +"    if (i > 0) x = 0 ;\n"  // FIXME - warn about else branch
                +"  }\n"

                +"}"
                );
    }

    @Test
    public void testAssignable3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int x,y; \n"

                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  //@ also \n"
                +"  //@ requires i == 0; \n"
                +"  //@ assignable y; \n"
                +"  public void m1bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  //@ also \n"
                +"  //@ requires i == 0; \n"
                +"  //@ assignable y; \n"
                +"  public void m1good(int i) {\n"
                +"    if (i > 0) x = 0 ;\n"
                +"    if (i == 0) y = 0 ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assignable) in method m1bad",7
                ,"/tt/TestJava.java:8: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignable4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int x,y; \n"

                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  //@ also \n"
                +"  //@ requires i == 0; \n"
                +"  //@ assignable y; \n"
                +"  public void m1bad(int i) {\n"
                +"    i = 0 ;\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assignable) in method m1bad",7
                ,"/tt/TestJava.java:5: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignable5() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int x,xx; static int y,yy; \n"

                +"  //@ assignable this.x; \n"
                +"  public void m1bad(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"  //@ assignable this.x; \n"
                +"  public void m2bad(int i) {\n"
                +"    xx = 0 ;\n"
                +"  }\n"

                +"  //@ assignable TestJava.y; \n"
                +"  public void m3bad(int i) {\n"
                +"    yy = 0 ;\n"
                +"  }\n"

                +"  //@ assignable TestJava.y; \n"
                +"  public void m4bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ assignable tt.TestJava.y; \n"
                +"  public void m5bad(int i) {\n"
                +"    yy = 0 ;\n"
                +"  }\n"

                +"  //@ assignable tt.TestJava.y; \n"
                +"  public void m6bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ assignable this.x; \n"
                +"  public void m1good(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ assignable TestJava.y; \n"
                +"  public void m2good(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"  //@ assignable tt.TestJava.y; \n"
                +"  public void m3good(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assignable) in method m1bad",7
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assignable) in method m2bad",8
                ,"/tt/TestJava.java:8: warning: Associated declaration",7
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assignable) in method m3bad",8
                ,"/tt/TestJava.java:12: warning: Associated declaration",7
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Assignable) in method m4bad",7
                ,"/tt/TestJava.java:16: warning: Associated declaration",7
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (Assignable) in method m5bad",8
                ,"/tt/TestJava.java:20: warning: Associated declaration",7
                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Assignable) in method m6bad",7
                ,"/tt/TestJava.java:24: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignable6() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int x,xx; static int y,yy; \n"

                +"  //@ assignable this.*; \n"
                +"  public void m1bad(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"  //@ assignable TestJava.*; \n"
                +"  public void m2bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ assignable tt.TestJava.*; \n"
                +"  public void m3bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ assignable this.*; \n"
                +"  public void m1good(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ assignable TestJava.*; \n"
                +"  public void m2good(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"  //@ assignable tt.TestJava.*; \n"
                +"  public void m3good(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"  //@ requires true; \n"
                +"  //@ assignable y; \n"
                +"  //@ also requires true; \n"
                +"  //@ assignable this.*; \n"
                +"  public void m0bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ requires true; \n"  // TODO check that the semantics of JML is that assignable clauses may be split like this
                +"  //@ assignable y; \n"
                +"  //@ assignable this.*; \n"
                +"  public void m0good(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ requires true; \n"
                +"  //@ assignable y, this.*; \n"
                +"  public void m00good(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assignable) in method m1bad",7
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assignable) in method m2bad",7
                ,"/tt/TestJava.java:8: warning: Associated declaration",7
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assignable) in method m3bad",7
                ,"/tt/TestJava.java:12: warning: Associated declaration",7
                ,"/tt/TestJava.java:33: warning: The prover cannot establish an assertion (Assignable) in method m0bad",7
                ,"/tt/TestJava.java:29: warning: Associated declaration",7
                );
    }

    @Test // FIXME - can't seem to make this work using @NonNull on A a
    public void testAssignableM1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public class A { int x,y; static int xx,yy; }\n"
                +"  int x,y; static int xx,yy; A a; //@ requires a != null; \n"

                +"  //@ assignable y, A.xx, a.x, this.y, TestJava.yy, tt.TestJava.yy; \n"
                +"  public void m1bad(int i) {\n"
                +"    m();\n"
                +"  }\n"

                +"  //@ assignable x; \n"
                +"  public void m1good(int i) {\n"
                +"    m();\n"
                +"  }\n"

                +"  //@ assignable this.x; \n"
                +"  public void m2good(int i) {\n"
                +"    m();\n"
                +"  }\n"

                +"  //@ assignable y, A.xx, a.xx, a.x, this.y, TestJava.yy, tt.TestJava.yy; //@ requires a != null; \n"
                +"  public void m3bad(int i) {\n"
                +"    ms();\n"
                +"  }\n"  // Line 20

                +"  //@ assignable xx; \n"
                +"  public void m3good(int i) {\n"
                +"    ms();\n"
                +"  }\n"

                +"  //@ assignable TestJava.xx; \n"
                +"  public void m3agood(int i) {\n"
                +"    ms();\n"
                +"  }\n"

                +"  //@ assignable tt.TestJava.xx; \n"
                +"  public void m3bgood(int i) {\n"
                +"    ms();\n"
                +"  }\n"

                +"  //@ assignable this.xx; \n"
                +"  public void m3cgood(int i) {\n"
                +"    ms();\n"
                +"  }\n"

                +"  //@ assignable x; \n"
                +"  public void m() {\n"
                +"  }\n"

                +"  //@ assignable xx; \n"  // Line 40
                +"  public void ms() {\n"
                +"  }\n"

                +"  //@ assignable this.x; \n"
                +"  public void mt() {\n"
                +"  }\n"

                +"  //@ assignable TestJava.xx; \n"
                +"  public void mts() {\n"
                +"  }\n"

                +"  //@ assignable tt.TestJava.xx; \n"
                +"  public void mtts() {\n"
                +"  }\n"

                +"  //@ assignable A.xx; \n"
                +"  public void mas() {\n"
                +"  }\n"

                +"  //@ requires a == this; assignable x; \n"
                +"  public void m1z1(TestJava a) {\n"
                +"    a.m();\n"
                +"  }\n"

                +"  //@ requires a != null; assignable x; \n"
                +"  public void m1z1bad(TestJava a) {\n"
                +"    a.m();\n"
                +"  }\n"

                +"  //@ requires a != null; assignable a.x; \n"
                +"  public void m1z2(TestJava a) {\n"
                +"    a.m();\n"
                +"  }\n"

                +"  //@ requires a == this; assignable a.x; \n"
                +"  public void m1z3(TestJava a) {\n"
                +"    m();\n"
                +"  }\n"

                +"  //@ requires a == this; assignable a.x; \n"
                +"  public void m1z4(TestJava a) {\n"
                +"    this.m();\n"
                +"  }\n"

                +"  //@ requires a != null; assignable a.x; \n"
                +"  public void m1z4bad(TestJava a) {\n"
                +"    this.m();\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:37: warning: The prover cannot establish an assertion (Assignable) in method m1bad",18
                ,"/tt/TestJava.java:4: warning: Associated declaration",39
                ,"/tt/TestJava.java:40: warning: The prover cannot establish an assertion (Assignable) in method m3bad",18
                ,"/tt/TestJava.java:17: warning: Associated declaration",7
                ,"/tt/TestJava.java:37: warning: The prover cannot establish an assertion (Assignable) in method m1z4bad",18
                ,"/tt/TestJava.java:71: warning: Associated declaration",7
                ,"/tt/TestJava.java:37: warning: The prover cannot establish an assertion (Assignable) in method m1z4bad",18
                ,"/tt/TestJava.java:75: warning: Associated declaration",7
                
                );
    }


}
