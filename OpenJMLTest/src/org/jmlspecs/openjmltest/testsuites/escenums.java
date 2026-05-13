package org.jmlspecs.openjmltest.testsuites;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escenums extends EscBase {

    @Test
    public void testBasicEnum() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public enum TestJava { AA
                }
                """
                );
    }
    
    @Test
    public void testBasicEnum2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public enum TestJava { AA, BB, CC
                }
                """
                );
    }
    
    @Test
    public void testUseEnum() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 enum Z { AA, BB, CC }
                 public class TestJava {
                    public void m() {
                       //@ assert Z.AA != Z.BB;
                    }
                }
                """
                );
    }
    
    @Test
    public void testUseEnum2() {
        addOptions("--warn=missing-measured-by");
        helpEsc("tt.TestJava",
                """
                package tt;
                enum Z { AA, BB, CC }
                public class TestJava {
                    public void mmm() {
                       Z ee = Z.AA;
                       //@ assert Z.AA == ee;
                       mmm(); // to put in a havoc everything
                       //@ assert Z.AA == ee && ee != Z.BB;
                    }
                }
                """
                ,"/tt/TestJava.java:7: warning: [missing-measured-by] Method mmm() is called recursively, but a specification case has no measured_by clause",11
                ,"/tt/TestJava.java:4: warning: Associated declaration: /tt/TestJava.java:7:",17
                );
    }
    
    @Test
    public void testUseEnum2a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 enum Z { AA, BB, CC }
                 public class TestJava {
                    public void m() {
                       //@ assert Z.AA == Z.AA;
                    }
                }
                """
                );
    }
    
    @Test
    public void testUseEnum2b() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 enum Z { AA, BB, CC }
                 public class TestJava {
                    public void m() {
                       //@ assert Z.AA != null;
                    }
                }
                """
                );
    }
    
    @Test
    public void testUseEnum2c() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 enum Z { AA, BB, CC }
                 public class TestJava {
                    public void m() {
                       //@ assert Z.AA instanceof Z;
                    }
                }
                """
                );
    }
    
    @Test
    public void testUseEnum2d() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 enum Z { AA, BB, CC }
                 public class TestJava {
                    public void m() {
                       //@ assert Z.AA != Z.BB;
                    }
                }
                """
                );
    }
    
    @Test
    public void testUseEnum2e() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 enum Z { AA, BB, CC }
                 public class TestJava {
                    public void m(/* nullable */ Z ee) {
                       //@ assert ee == null || ee == Z.AA || ee == Z.BB || ee == Z.CC;
                    }
                }
                """
                );
    }
    
    @Test
    public void testUseEnum2f() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 enum Z { AA, BB, CC }
                 public class TestJava {
                    public void m(/* non_null */ Z ee) {
                       //@ assume ee != Z.AA ;
                       //@ assume ee != Z.CC ;
                       //@ assert ee == Z.BB ;
                    }
                }
                """
                );
    }
    
    @Test
    public void testUseEnum2g() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 enum Z { AA, BB, CC }
                 public class TestJava {
                    public void m(/* non_null */ Z ee) {
                       //@ assume ee != Z.AA ;
                       //@ assume ee != Z.CC ;
                       //@ assert ee != Z.BB ;
                    }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m",12
                );
    }
    
    @Test
    public void testUseEnum2h() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 enum Z { AA, BB, CC }
                 public class TestJava {
                    public void m(/* non_null */ Z ee) {
                       Object o = ee;
                       //@ assert o instanceof Z ;
                       //@ assert o instanceof Integer ;
                    }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m",12
                );
    }
    
    @Test
    public void testUseEnum3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 enum Z { AA, BB, CC }
                 public class TestJava {
                    public void m() {
                       Object o = new Object();
                       //@ assert Z.AA != o;
                    }
                }
                """
                );
    }
    
    @Test
    public void testUseEnum4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 enum Z { AA, BB, CC }
                 public class TestJava {
                    public void m(Object o) {
                       //@ assume !(o instanceof Z) ;
                       //@ assert Z.AA != o;
                    }
                }
                """
                );
    }
    
    @Test
    public void testUseEnum4a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 enum Z { AA, BB, CC }
                 public class TestJava {
                    public void m(Object o) {
                       //@ assume (o instanceof Z) ;
                       //@ assert o == Z.AA || o == Z.CC || o == Z.BB;
                    }
                }
                """
                );
    }
    
    @Test
    public void testUseEnum5() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 enum Z { AA, BB, CC }
                 public class TestJava {
                    public void m(Object o) {
                       //@ assert Z.AA != o;
                    }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m",12
                );
    }
    
    @Test
    public void enumSwitch() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ ensures \\result > 0;
                    //@ ensures the_value == MyEnum.ONE ==> \\result == 2;
                    //@ ensures the_value == MyEnum.TWO ==> \\result == 4;
                    //@ ensures the_value == MyEnum.THREE ==> \\result == 8;
                    //@ ensures \\result == 2 || \\result == 4 || \\result == 8;
                    public int switchStatement(final MyEnum the_value) {
                      int result = 0;
                      switch (the_value) {
                        case ONE:
                          result = 2;
                          break;

                        case TWO:
                          result = 4;
                          break;

                        case THREE:
                          result = 8;
                          break;

                        default:
                          //@ unreachable;
                          result = 1;
                      }
                      return result;
                   }

                   static public enum MyEnum {
                      ONE, TWO, THREE;
                   }
                }
                """
                );
        }
}
