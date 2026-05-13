package org.jmlspecs.openjmltest.testsuites;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escfunction extends EscBase {

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        addOptions("--nullable-by-default"); // Because the tests were written this way
        //addOptions("-trace");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
 
    
    
    @Test // FIXME - for reasons unknown, this test appears to be non-deterministic - sometimes succeeding sometimes failing
    public void testMethodAxioms() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 //@ code_java_math spec_java_math
                public class TestJava  {
                  //@ normal_behavior
                  //@ ensures \\result == (i > 0 && i < 10);
                  //@ pure
                  //@ model public boolean m(int i);
                  public void mm() {
                  //@ assert (\\forall int k; 3<k && k <7; m(k));
                  //@ assert (\\forall int k; 3<k && k <7; m(k-1));
                  //@ assert !(\\forall int k; -3<k && k <7; m(k));
                  }
                }
                """
                );
    }

    
    @Test
    public void testMethodAxioms2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 //@ code_java_math spec_java_math
                public class TestJava  {
                  //@ normal_behavior
                  //@ ensures \\result == (i > 0 && i < 10);
                  //@ pure
                  //@ model public boolean m(int i);
                  //@ pure
                  public void mm() {
                  //@ assert !(\\forall int k; 3<k && k <11; m(k));
                  }
                }
                """
                );
    }

    @Test
    public void testFunction() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.* ;
                public @Immutable class TestJava  {
                  //@ normal_behavior
                  //@ ensures \\result == (i > 0 && i < 10);
                  //@ @NoState
                  //@ model public boolean mfunc(int i);
                  int n;
                  public void mm() {
                  //@ assert mfunc(5);
                  //@ assert !mfunc(0);
                  }
                }
                """
                );
    }

    @Test
    public void testFunctionError3() {
        expectedExit = 1;
        addOptions("-check");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.* ;
                public class TestJava  {
                  //@ normal_behavior
                  //@ assignable n;
                  //@ ensures \\result == (i > 0 && i < 10);
                  //@ @NoState
                  //@ model public boolean mfunc(int i);
                  int n;
                  public void mm() {
                  //@ assert mfunc(5);
                  //@ assert !mfunc(0);
                  }
                }
                """
                //,"/tt/TestJava.java:6: error: A non-static function method must be a member of a Immutable class", 7 // FIXME
                ,"/tt/TestJava.java:4: error: A no_state method may not read class fields: n", 18
                ,"/tt/TestJava.java:4: error: no_state methods are implicitly pure and may not assign to any fields: n",18
                );
    }

    @Test
    public void testFunctionError2() {
    	expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.* ;
                public @Immutable class TestJava  {
                  //@ normal_behavior
                  //@ assignable n;
                  //@ ensures \\result == (i > 0 && i < 10);
                  //@ @NoState
                  //@ model public boolean mfunc(int i);
                  int n;
                  public void mm() {
                  //@ assert mfunc(5);
                  //@ assert !mfunc(0);
                  }
                }
                """
                ,"/tt/TestJava.java:4: error: A no_state method may not read class fields: n", 18
                ,"/tt/TestJava.java:4: error: no_state methods are implicitly pure and may not assign to any fields: n",18
                );
    }

    @Test
    public void testFunctionError() {
    	expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.* ;
                public @Immutable class TestJava  {
                  //@ normal_behavior
                  //@ assignable n;
                  //@ ensures \\result == (i > 0 && i < 10);

                  //@ model no_state public boolean mfunc(int i);
                  int n;
                  public void mm() {
                  //@ assert mfunc(5);
                  n = 0;
                  //@ assert !mfunc(n);
                  }
                }
                """
                ,"/tt/TestJava.java:4: error: A no_state method may not read class fields: n", 18
                ,"/tt/TestJava.java:4: error: no_state methods are implicitly pure and may not assign to any fields: n",18
                );
    }

    
    @Test
    public void testStaticFunction() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.* ;
                public class TestJava  {
                  //@ normal_behavior
                  //@ ensures \\result == (i > 0 && i < 10);
                  //@ @NoState
                  //@ static model public boolean mfunc(int i);
                  int n;
                  public void mm() {
                  //@ assert mfunc(5);
                  n = 0;
                  //@ assert !mfunc(n);
                  }
                }
                """
                );
    }
}

