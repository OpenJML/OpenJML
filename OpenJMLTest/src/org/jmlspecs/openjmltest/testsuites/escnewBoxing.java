package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escnewBoxing extends EscBase {

    @Test
    public void testSimple() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default*/ public class TestJava {

                  public void m1good() {
                    Integer i = 5;
                    int k = i;
                    //@ assert k == 5 ;
                  }

                  public void m1bad() {
                    Integer i = 5;
                    int k = i;
                    //@ assert k == 6 ;
                  }

                  public void m1bad2() {
                    Integer i = null;
                    int k = i;
                    //@ assert k == 6 ;
                  }

                  public void m2good() {
                    Integer i = 5;
                    //@ assert i != null ;
                    //@ assert \\typeof(i) == \\type(Integer) ;
                  }
                }
                """
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method m1bad2",13
                );
    }

    @Test
    public void testSimple2Static() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default*/ public class TestJava {
                  static Integer i = 5;
                  static int k = i;
                  static { //@ assert k == 5;
                }
                  static { Integer j = 6; int m = j; //@ assert m == 6;
                }
                  static { Integer j = null; int m = j;
                }
                  //@ ensures true;
                  //@ static_initializer
                }
                """
                );   // FIXME - should generate warnings here
    }

    @Test
    public void testSimple2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default*/ public class TestJava {
                  Integer i = 5;
                  int k = i;
                  { //@ assert k == 5;
                }
                  { Integer j = 6; int m = j; //@ assert m == 6;
                }
                  { Integer j = null; int m = j;
                }
                }"""
                ,
                "/tt/TestJava.java:9: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method TestJava",31
                );
    }

    @Test
    public void testSwitch() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default*/ public class TestJava {
                  public void m(int i) {;
                  Integer k = i ; int m = 0;
                  switch (k) {
                    case 1: m = 1; break;
                    case 2: m = i; break;
                    default: m = i; break;
                  } //@ assert m == i;
                }}
                """
                );
    }

    @Test
    public void testSwitchShort() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default*/ public class TestJava {
                  public void m(short i) {;
                  Short k = i ; int m = 0;
                  switch (k) {
                    case 1: m = 1; break;
                    case 2: m = i; break;
                    default: m = i; break;
                  } //@ assert m == i;
                }}
                """
                );
    }

    @Test
    public void testSwitchByte() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default*/ public class TestJava {
                  public void m(byte i) {;
                  Byte k = i ; int m = 0;
                  switch (k) {
                    case 1: m = 1; break;
                    case 2: m = i; break;
                    default: m = i; break;
                  } //@ assert m == i;
                }}
                """
                );
    }

    @Test
    public void testSwitchNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default*/ public class TestJava {
                  public void m(int i) {;
                  Integer k = null ; int m = 0;
                  switch (k) {
                    case 1: m = 1; break;
                    case 2: m = i; break;
                    default: m = i; break;
                  } //@ assert m == i;
                }}
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method m",11
                );
    }

    @Test
    public void testBinary() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default*/ public class TestJava {
                  public void m(int i) {
                  Integer k = 6 ; int m = 1;
                  int z = m + k;
                  //@ assert z  == 7;
                  z = k + m;
                  //@ assert z == 8;
                  }
                  public void m1bad(int i) {
                  Integer k = null; int m = 1;
                  int z = m + k;
                  }
                  public void m2bad(int i) {
                  Integer k = null; int m = 1;
                  int z = k + m;
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method m",7
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method m1bad",15
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method m2bad",11
                );
    }
}
