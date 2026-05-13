package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

//FIXME _ need to test when inline body is in separate file
//FIXME _ need to test when inline body is in separate file that is not parsed on the command-line
// FIXME - need to test when inline is in .jml
// FIXME - need to test when inline is in .jml for a binary class

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escinline extends EscBase {

    @Test // basic test of inlining, checking assignable and ensures and return value
    public void testInline1() {
        addOptions("-defaults=constructor:pure");
        //addOptions("--show","--method=minline");
        helpEsc("tt.TestJava",
                """
                package tt; //@ code_java_math spec_java_math
                public class TestJava {
                  public int j;
                  //+OPENJML@ inline
                  public final int minline(int i) {
                    j = j -1;
                    return i + 1;
                  }
                  //@ ensures j + 1 ==  \\old(j);
                  //@ ensures  \\result == ii + 1;
                  //@ ensures j + \\result == ii + \\old(j);
                  //@ assignable j;
                  public int m1(int ii) {
                    return minline(ii);
                  }
                  //@ assignable j;
                  public int m2(int ii) {
                    return minline(ii);
                  }
                  //@ assignable \\nothing;
                  public int m3(int ii) {
                    return minline(ii);
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assignable) in method m3: j", 7
                ,"/tt/TestJava.java:20: verify: Associated declaration", 7
                );
    }

    @Test // basic test of inlining, checking assignable and ensures, with no return
    public void testInline1a() {
        helpEsc("tt.TestJava",
                """
                package tt; //@ code_java_math spec_java_math
                public class TestJava {
                  public int j;
                  //+OPENJML@ inline
                  public final void minline(int i) {
                    j = j + i;
                  }
                  //@ ensures j ==  \\old(j) + ii;
                  //@ assignable j;
                  public void m1(int ii) {
                    minline(ii);
                  }
                  //@ assignable \\nothing;
                  public void m3(int ii) {
                    minline(ii);
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assignable) in method m3: j", 7
                ,"/tt/TestJava.java:13: verify: Associated declaration", 7
                );
    }

    // This test is OK with bigint math (cf. testInline2a), but not with java math.  FIXME - problem is that m.j does not have a range restriction assumption
    @Test  // inlining from a different class (with a different 'this')
    public void testInline2() {
        addOptions("-defaults=constructor:pure");
        helpEsc("tt.TestJava",
                """
                package tt; //@ code_java_math spec_java_math
                 class M {
                  public int j;
                  //+OPENJML@ inline
                  public int minline(int i) {
                    j = j -1;
                    return i + 1;
                  }
                }
                //@ code_java_math spec_java_math
                public class TestJava {

                  //@ ensures m.j + 1  ==  \\old(m.j) ;
                  //@ ensures  \\result == ii + 1;
                  //@ assignable m.j;
                  public int m1(M m, int ii) {
                    return m.minline(ii);
                  }
                  //@ assignable m.j;
                  public int m2(M m, int ii) {
                    return m.minline(ii);
                  }
                  //@ assignable \\nothing;
                  public int m3(M m, int ii) {
                    return m.minline(ii);
                  }
                }
                """
                ,"/tt/TestJava.java:4: warning: [jml-lint] Inlined methods should be final since overriding methods will be ignored: minline", 15
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assignable) in method m3: j", 7
                ,"/tt/TestJava.java:23: verify: Associated declaration", 7
                );
    }

    @Test  // inlining from a different class (with a different 'this')
    public void testInline2a() {
        helpEsc("tt.TestJava",
                """
                package tt; //@ code_bigint_math spec_bigint_math
                 class M {
                  public int j;
                  //+OPENJML@ inline
                  public int minline(int i) {
                    j = j -1;
                    return i + 1;
                  }
                }
                //@ code_bigint_math spec_bigint_math
                public class TestJava {
                  public int j;
                  //@ ensures m.j + 1 ==  \\old(m.j);
                  //@ ensures  \\result == ii + 1;
                  //@ assignable m.j;
                  public int m1(M m, int ii) {
                    return m.minline(ii);
                  }
                  //@ assignable m.j;
                  public int m2(M m, int ii) {
                    return m.minline(ii);
                  }
                  //@ assignable \\nothing;
                  public int m3(M m, int ii) {
                    return m.minline(ii);
                  }
                }
                """
                ,"/tt/TestJava.java:4: warning: [jml-lint] Inlined methods should be final since overriding methods will be ignored: minline", 15
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assignable) in method m3: j", 7
                ,"/tt/TestJava.java:23: verify: Associated declaration", 7
                );
    }

    @Test // inline is an extension and should be final
    public void testInline3() {
    	addOptions("-lang=jml");
        helpEsc("tt.TestJava",
                """
                package tt; //@ code_java_math spec_java_math
                 class M {
                  public int j;
                  //+OPENJML@ inline
                  public int minline(int i) {
                    j = j -1;
                    return i + 1;
                  }
                }
                """
                ,"/tt/TestJava.java:4: warning: [strict-jml] The inline construct is an OpenJML extension to JML and not allowed under --lang=jml", 15
                ,"/tt/TestJava.java:4: warning: [jml-lint] Inlined methods should be final since overriding methods will be ignored: minline", 15
                );
    }

    @Test // inline not allowed on constructor
    public void testInline4() {
    	expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt; //@ code_java_math spec_java_math
                 class M {
                  public int j;
                  //+OPENJML@ inline
                  public M(int i) {
                    j = i + 1;
                  }
                }
                """
                ,"/tt/TestJava.java:4: error: This JML modifier is not allowed for a constructor declaration", 15
                );
    }
}
