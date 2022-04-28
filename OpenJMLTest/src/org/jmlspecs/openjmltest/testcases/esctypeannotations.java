package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class esctypeannotations extends EscBase {

    public esctypeannotations(String options, String solver) {
        super(options,solver);
    }
    
    @Before @Override
    public void setUp() throws Exception {
    	//captureOutput = true;
    	super.setUp();
    }
 
    protected void helpTCX(String classname, String s, Object... expectedResults) {
    	super.helpTCX(classname,  s,  expectedResults);
    }

    @Test
    public void testField1() {
        helpTCX("tt.TestJava",
            """
            package tt;
            import org.jmlspecs.annotation.*;
            //@ non_null_by_default
            public class TestJava {
                /*@ nullable */ Object o1;
                @Nullable Object o2;
            }
            //@ nullable_by_default
            class TestJava1 {
                @NonNull Object o3; // ERROR
            }
            //@ nullable_by_default
            class TestJava2 {
                /*@ non_null */ Object o4; // ERROR
            }
            //@ non_null_by_default
            class TestJava3 {
                Object o5; // ERROR
            }
            //@ nullable_by_default
            class TestJava4 {
                /*@ nullable */ Object o1;
                @Nullable Object o2;
                Object o5; // OK
            }
            //@ nullable_by_default
            class TestJava5 {
                Object o4; // OK
            }
            //@ nullable_by_default
            class TestJava6 {
                @NonNull public Object o3; // ERROR
            }
            //@ nullable_by_default
            class TestJava7 {
                /*@ non_null */ public Object o4; // ERROR
            }
            """
            ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (NullField) in method TestJava1",21
            ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (NullField) in method TestJava2",28
            ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (NullField) in method TestJava3",12
            ,"/tt/TestJava.java:32: warning: The prover cannot establish an assertion (NullField) in method TestJava6",28
            ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (NullField) in method TestJava7",35
            );
    }

    @Test
    public void testField2() {
        helpTCX("tt.TestJava",
            """
            package tt;
            import org.jmlspecs.annotation.*;
            //@ non_null_by_default
            public class TestJava {
                java.lang.@Nullable Object o2;
            }
            //@ nullable_by_default
            class TestJava1 {
                java.lang.@NonNull Object o3; // ERROR
            }
            //@ non_null_by_default
            class TestJava3 {
                java.lang.Object o5; // ERROR
            }
            //@ nullable_by_default
            class TestJava4 {
                java.lang.@Nullable Object o2;
                java.lang.Object o5; // OK
            }
            """
            ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (NullField) in method TestJava1",31
            ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (NullField) in method TestJava3",22
            );
    }

    @Test
    public void testField3() {
        helpTCX("tt.TestJava",
            """
            package tt;
            import org.jmlspecs.annotation.*;
            //@ non_null_by_default
            public class TestJava {
                java.lang. /*@ nullable */ Object o1;
            }
            //@ nullable_by_default
            class TestJava2 {
                java.lang./*@ non_null */ Object o4; // ERROR
            }
            //@ nullable_by_default
            class TestJava4 {
                java.lang./*@ nullable */ Object o1;
            }
            """
            ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (NullField) in method TestJava2",38
            );
    }

    @Test
    public void testField4() {
        helpTCX("tt.TestJava",
            """
            package tt;
            import org.jmlspecs.annotation.*;
            //@ non_null_by_default
            public class TestJava {
                /*@ nullable */ java.lang.Object o1;
                @Nullable java.lang.Object o2;
            }
            //@ nullable_by_default
            class TestJava1 {
                @NonNull java.lang.Object o3; // ERROR
            }
            """
            ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (NullField) in method TestJava1",31
            );
    }

    @Test
    public void testLocal1() {
        helpTCX("tt.TestJava",
            """
            package tt;
            import org.jmlspecs.annotation.*;
            //@ non_null_by_default
            public class TestJava {
                public void m() {
                    /*@ nullable */ Object o1 = null;
                    @Nullable Object o2 = null;
                }
            }
            //@ nullable_by_default
            class TestJava1 {
                public void m() {
                    @NonNull Object o3 = null; // ERROR
                }
            }
            //@ nullable_by_default
            class TestJava2 {
                public void m() {
                    /*@ non_null */ Object o4 = null; // ERROR
                }
            }
            //@ non_null_by_default
            class TestJava3 {
                public void m() {
                    Object o5 = null; // ERROR
                }
            }
            //@ nullable_by_default
            class TestJava4 {
                public void m() {
                    /*@ nullable */ Object o1;
                    @Nullable Object o2 = null;
                    Object o5 = null; // OK
                }
            }
            //@ nullable_by_default
            class TestJava5 {
                public void m() {
                    Object o4 = null; // OK
                }
            }
            //@ nullable_by_default
            class TestJava6 {
                public void m() {
                    @NonNull final Object o3 = null; // ERROR
                }
            }
            //@ nullable_by_default
            class TestJava7 {
                public void m() {
                    /*@ non_null */ final Object o4 = null; // ERROR
                }
            }
            """
            ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (PossiblyNullInitialization) in method m: o3",25
            ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (PossiblyNullInitialization) in method m: o4",32
            ,"/tt/TestJava.java:25: warning: The prover cannot establish an assertion (PossiblyNullInitialization) in method m: o5",16
            ,"/tt/TestJava.java:45: warning: The prover cannot establish an assertion (PossiblyNullInitialization) in method m: o3",31
            ,"/tt/TestJava.java:51: warning: The prover cannot establish an assertion (PossiblyNullInitialization) in method m: o4",38
            );
    }

    @Test
    public void testLocal2() {
        helpTCX("tt.TestJava",
            """
            package tt;
            import org.jmlspecs.annotation.*;
            //@ non_null_by_default
            public class TestJava {
                public void m() {
                    java.lang.@Nullable Object o2 = null;
                }
            }
            //@ nullable_by_default
            class TestJava1 {
                public void m() {
                    java.lang.@NonNull Object o3 = null; // ERROR
                }
            }
            //@ non_null_by_default
            class TestJava3 {
                public void m() {
                    java.lang.Object o5 = null; // ERROR
                }
            }
            //@ nullable_by_default
            class TestJava4 {
                public void m() {
                    java.lang.@Nullable Object o2 = null;
                    java.lang.Object o5 = null; // OK
                }
            }
            """
            ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyNullInitialization) in method m: o3",35
            ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (PossiblyNullInitialization) in method m: o5",26
            );
    }

    @Test
    public void testLocal3() {
        helpTCX("tt.TestJava",
            """
            package tt;
            import org.jmlspecs.annotation.*;
            //@ non_null_by_default
            public class TestJava {
                public void m() {
                    java.lang. /*@ nullable */ Object o1 = null;
                }
            }
            //@ nullable_by_default
            class TestJava2 {
                public void m() {
                    java.lang./*@ non_null */ Object o4 = null; // ERROR
                }
            }
            //@ nullable_by_default
            class TestJava4 {
                public void m() {
                    java.lang./*@ nullable */ Object o1 = null;
                }
            }
            """
            ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyNullInitialization) in method m: o4",42
            );
    }

    @Test
    public void testLocal4() {
        expectedExit = 1;
        helpTCX("tt.TestJava",
            """
            package tt;
            import org.jmlspecs.annotation.*;
            //@ non_null_by_default
            public class TestJava {
                public void m() {
                    /*@ nullable */ java.lang.Object o1 = null;
                    @Nullable java.lang.Object o2 = null;
                }
            }
            //@ nullable_by_default
            class TestJava1 {
                public void m() {
                    @NonNull java.lang.Object o3 = null; // ERROR
                }
            }
            """
            ,"/tt/TestJava.java:7: error: cannot find symbol\n  symbol:   class java\n  location: class tt.TestJava",19
            ,"/tt/TestJava.java:13: error: cannot find symbol\n  symbol:   class java\n  location: class tt.TestJava1",18
            //,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (PossiblyNullInitialization) in method m: o3",31
            );
    }
    @Test
    public void testClass1() {
        helpTCX("tt.TestJava",
            """
            package tt;
            import org.jmlspecs.annotation.*;
            //@ non_null_by_default
            public abstract class TestJava extends @NonNull Object implements @NonNull Cloneable {
            }
            """
            );
    }

    @Test
    public void testClass2() {
        expectedExit = 1;
        main.addOptions("--show=ast"); // FIXME
        helpTCX("tt.TestJava",
            """
            package tt;
            import org.jmlspecs.annotation.*;
            //@ non_null_by_default
            public class TestJava extends @NonNull java.lang.Object {
            }
            """
            ,"/tt/TestJava.java:4: error: cannot find symbol\n  symbol: class java",40
            );
    }

    @Test
    public void testClass2a() {
        helpTCX("tt.TestJava",
            """
            package tt;
            import org.jmlspecs.annotation.*;
            //@ non_null_by_default
            public class TestJava extends java.lang.@NonNull Object {
            }
            """
            );
    }

    @Test
    public void testClass3() {
        expectedExit = 1;
        helpTCX("tt.TestJava",
            """
            package tt;
            import org.jmlspecs.annotation.*;
            //@ non_null_by_default
            public class TestJava implements @NonNull java.lang.Cloneable {
            }
            """
            ,"/tt/TestJava.java:4: error: cannot find symbol\n  symbol: class java",43
            );
    }
    @Test
    public void testClass3a() {
        helpTCX("tt.TestJava",
            """
            package tt;
            import org.jmlspecs.annotation.*;
            //@ non_null_by_default
            public class TestJava implements java.lang.@NonNull Cloneable {
            }
            """
            );
    }



    // local declarations
    // formal declarations
    // method return
    // extends, implements
    // throws clause
    // type parameters
    // type arguments
    
    // cast
    // instanceof
    // for statement, enhanced for
    // try with resources
    // throw
    // catch
    // allocate object, array
    // lambda function
    
    // quantified declaration, let declaration
    // old clause
    // signals clause, signals_only
    
    // type checking in assignment, in actual to formal, in initialization, in array initialization
}
