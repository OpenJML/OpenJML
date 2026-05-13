package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class QueryPure extends TCBase {

    // FIXME - missing the 'error' in error mesages

    @Test
    public void testClass1() {
        helpTCText("A.java",
                """
                //@ pure // OK
                public class A { }
                """
        );
    }

    @Test
    public void testClass2() {
        helpTCText("A.java",
                """
                //@ query // OK
                public class A { }
                """
        );
    }

    @Test
    public void testClass3() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                @Query // OK
                public class A { }
                """
        );
    }

    @Test
    public void testClass4() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                @Pure // OK
                public class A { }
                """
        );
    }

    @Test
    public void testClass5() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                @Pure @Query // BAD
                public class A { }
                """
                ,"/A.java:2: A declaration may not be both pure and query",7
        );
    }

    @Test
    public void testClass6() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                //@ pure query // BAD
                public class A { }
                """
                ,"/A.java:2: error: A declaration may not be both pure and query",10
        );
    }

    @Test
    public void testClass7() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                @Pure //@ query // BAD
                public class A { }
                """
                ,"/A.java:2: error: A declaration may not be both pure and query",11
        );
    }

    @Test
    public void testClass8() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                @Pure //@ pure // BAD
                public class A { }
                """
                ,"/A.java:2: org.jmlspecs.annotation.Pure is not a repeatable annotation type",11 // Changed location in Java8
        );
    }

    @Test
    public void testClass9() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                @Query //@ query // BAD
                public class A { }
                """
                ,"/A.java:2: org.jmlspecs.annotation.Query is not a repeatable annotation type",12 // CHanged location in Java8
        );
    }

    @Test
    public void testMethod1() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Query // OK
                  public void v() {}
                }
                """
        );
    }

    @Test
    public void testMethod2() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ query // OK
                  public void v() {}
                }
                """
        );
    }

    @Test
    public void testMethod3() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Pure // OK
                  public void v() {}
                }
                """
        );
    }

    @Test
    public void testMethod4() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@pure // OK
                  public void v() {}
                }
                """
        );
    }

    @Test
    public void testMethod5() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ pure query // BAD
                  public void v() {}
                }
                """
                ,"/A.java:3: A declaration may not be both pure and query",12
        );
    }

    @Test
    public void testMethod6() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Query @Pure // BAD
                  public void v() {}
                }
                """
                ,"/A.java:3: A declaration may not be both pure and query",3
        );
    }

    @Test
    public void testMethod7() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Pure //@ query // BAD
                  public void v() {}
                }
                """
                ,"/A.java:3: A declaration may not be both pure and query",13
        );
    }

    @Test
    public void testMethod8() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Query //@ query // BAD
                  public void v() {}
                }
                """
                ,"/A.java:3: org.jmlspecs.annotation.Query is not a repeatable annotation type",14
        );
    }

    @Test
    public void testMethod9() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Pure //@ pure // BAD
                  public void v() {}
                }
                """
                ,"/A.java:3: org.jmlspecs.annotation.Pure is not a repeatable annotation type",13
        );
    }

    @Test
    public void testCacheExample() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ secret public model \\datagroup value;
                  @Secret
                  protected Integer cache = null; //@ in value;
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query("value")
                  public int value() {
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                }
                """
        );
    }

    @Test
    public void testSimplerCacheExample() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ model public secret Object value;
                  @Secret
                  protected Integer cache = null; //@ in value;
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() {
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                }
                """
        );
    }

    @Test
    public void testAnotherCacheExample() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Secret
                  Integer cache = null; // Requires allowing non-model fields to be datagroups
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query("cache")
                  public int value() {
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                }
                """
        );
    }

    @Test
    public void testAnotherValidExample() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() {
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                  @Secret
                  Integer cache = null; //@ in value; // To use the implicit declaration, value here must be after the Query
                }
                """
        );
    }

    @Test
    public void testInvariant() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() {
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                  @Secret
                  public Integer cache = null; //@ in value; // To use the implicit declaration, value here must be after the Query
                  //@ @Secret("value") public invariant cache != null ==> cache == compute();
                }
                """
        );
    }

    @Test
    public void testForwardRef() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Secret
                  Integer cache = null; //@ in value;
                  //@ secret model Object value; // we're allowing forward reference
                }
                """
        );
    }

    @Test
    public void testCircular() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ secret model Integer cache ; //@ in value;
                  //@ secret model Object value; in cache; // error - circular
                }
                """
                ,"/A.java:3: error: This field participates in a circular datagroup inclusion chain: cache -> value -> cache",28
                ,"/A.java:4: error: This field participates in a circular datagroup inclusion chain: value -> cache -> value",27
        );
    }

    @Test
    public void testCircularSelf() {
        expectedExit = 0;
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ secret model Object value; in value; // warning - circular
                }
                """
                ,"/A.java:3: warning: Do not include a datagroup in itself: value",37
        );
    }

    @Test
    public void testQuery0() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Secret
                  Integer cache = null; //@ in value;
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() {
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                }
                """
        );
    }

    @Test
    public void testQuery1() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ model secret public Object value;
                  @Secret
                  public Integer cache = null; //@ in value;
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == cache; // ERROR - no use of secret in specs
                  @Query
                  public int value() {
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                }
                """
                ,"/A.java:8: Secret fields may not be read in non-secret context: cache",26
        );
    }

    @Test
    public void testQuery2() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ model secret Object value;
                  @Secret
                  Integer cache = null; //@ in value;
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() {
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return cache; } // ERROR - no use of secret in open method
                }
                """
                ,"/A.java:14: Secret fields may not be read in non-secret context: cache",29
        );
    }

    @Test
    public void testQuery3() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() {
                    f = 0; // ERROR - no assignment except to secret
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                  int f;
                  @Secret
                  Integer cache = null; //@ in value;
                }
                """
                ,"/A.java:8: The field f is not writable since it is not in the value secret datagroup",5
        );
    }

    @Test
    public void testQuery4() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ @Secret public model Object o;
                   @Secret
                   int q; //@ in o;
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() {
                    q = 0; // ERROR - no assignment except to own secret
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                  int f;
                  @Secret
                  Integer cache = null; //@ in value;
                }
                """
                ,"/A.java:11: A field may not be read in a secret context unless it is in the same secret datagroup: q not in value",5
                ,"/A.java:11: The field q is not writable since it is not in the value secret datagroup",5
        );
    }

    @Test
    public void testQuery5() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ @Secret public model Object o;
                   @Secret
                   int q; //@ in o;
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() {
                    if (cache == null) cache = compute() + q; // ERROR - no reading other secret
                    return cache;
                  }
                  public int use() { return value(); }
                  int f;
                  @Secret
                  Integer cache = null; //@ in value;
                }
                """
                ,"/A.java:11: A field may not be read in a secret context unless it is in the same secret datagroup: q not in value",43
        );
    }

    @Test
    public void testQuery6() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ @Secret public model Object value;
                  //@ @Secret public model Object o; in value;
                   @Secret
                   int q = 5; //@ in o;
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() {
                    if (cache == null) cache = compute() + q; // OK - q is nested in value
                    return cache;
                  }
                  public int use() { return value(); }
                  int f;
                  @Secret
                  Integer cache = null; //@ in value;
                }
                """
        );
    }

    @Test
    public void testQuery7() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ @Secret public model Object o;
                   @Secret
                   public int q; //@ in o;
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() {
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                  int f;
                  @Secret
                  public Integer cache = null; //@ in value;
                  //@ @Secret("value") public invariant cache != null ==> cache == compute() + q; // ERROR - no reading other secret
                }
                """
                ,"/A.java:18: A field may not be read in a secret context unless it is in the same secret datagroup: q not in value",80
        );
    }

    // Note the difference between this test and the one below - here the attempt to resolve value on line 3 used to fail because it is
    // processed before the datagroup 'value' is created
    @Test
    public void testQuery8() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Secret
                  public Object o; //@ in value;
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() { // creates a datagroup named 'value'
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                  int f;
                  @Secret
                  public Integer cache = null; //@ in value;
                  //@ @Secret("value") public invariant cache != null ==> cache == compute() + 0;
                }
                """
        );
    }

    @Test
    public void testQuery8c() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Secret
                  public int q = 5; //@ in o;
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() { // creates a datagroup named 'value'
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                  int f;
                  @Secret
                  public Integer cache = null; //@ in value;
                  //@ @Secret("value") public invariant cache != null ==> cache == compute() + q; // OK - q is nested in value
                  //@ @Secret public model Object o; in value;
                 }
                """
        );
    }

    // This test typechecks OK because the use of 'value' on line 3 is not resolved until after all Java declarations are
    // resolved - particularly value(), which will create the datagroup named value
    @Test
    public void testQuery8b() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ @Secret public model Object o; in value;
                   @Secret
                   public int q = 5; //@ in o;
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() { // creates a datagroup named 'value'
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                  int f;
                  @Secret
                  public Integer cache = null; //@ in value;
                  //@ @Secret("value") public invariant cache != null ==> cache == compute() + q; // OK - q is nested in value
                }
                """
        );
    }

    @Test
    public void testQuery8OK() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ @Secret public model Object value;
                  //@ @Secret public model Object o; in value;
                   @Secret
                   public int q = 5; //@ in o;
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() {
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                  int f;
                  @Secret
                  public Integer cache = null; //@ in value;
                  //@ @Secret("value") public invariant cache != null ==> cache == compute() + q; // OK - q is nested in value
                }
                """
        );
    }

    @Test
    public void testQuery8a() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ @Secret public model Object value;
                  //@ @Secret public model Object o; in value;
                   int f;
                   @Secret
                   int q = 5; //@ in o;
                  @Pure
                  public int compute() { return 0; }
                  //@ ensures \\result == compute();
                  @Query
                  public int value() {
                    if (cache == null) cache = compute();
                    return cache;
                  }
                  public int use() { return value(); }
                  @Secret
                  Integer cache = null; //@ in value;
                  //@ @Secret public invariant true; // BAD SYNTAX
                  //@ @Secret(0) public invariant true; // BAD SYNTAX
                  //@ @Secret("org") public invariant true; // BAD SYNTAX
                  //@ @Secret("value","value") public invariant true; // BAD SYNTAX
                  //@ @Secret("v") public invariant true; // ERROR - not found
                }
                """
                ,"/A.java:19: A secret annotation on an invariant must have exactly one argument",22
                ,"/A.java:20: incompatible types: int cannot be converted to java.lang.String",15
                ,"/A.java:21: cannot find symbol\n  symbol:   variable org\n  location: class A",15
                ,"/A.java:22: annotation values must be of the form 'name=value'",15
                ,"/A.java:22: annotation values must be of the form 'name=value'",23
                ,"/A.java:22: A secret annotation on an invariant must have exactly one argument",39
                ,"/A.java:23: cannot find symbol\n  symbol:   variable v\n  location: class A",15
        );
    }

    @Test
    public void testQuery9() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ @Secret public model int value;
                  //@ @Secret public model Object o; in value;
                   @Secret
                   int q = 5; //@ in o;
                  @Pure
                  public int compute() { return 0; }
                  int f;
                  @Secret
                  Integer cache = null; //@ in value;
                  @Secret("value")
                  public int mm() {
                    cache = null;
                    q = 0;
                    f = 0; // ERROR - can't write f
                  }
                }
                """
                ,"/A.java:17: The field f is not writable since it is not in the value secret datagroup",5
        );
    }

    @Test
    public void testQuery10() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ @Secret model int value;
                  //@ @Secret public model Object o;
                   @Secret
                   int q = 5; //@ in o;
                  @Pure
                  public int compute() { return 0; }
                  int f;
                  @Secret
                  Integer cache = null; //@ in value;
                  @Secret("value")
                  public int mm() {
                    q = 0; // ERROR - can't read or write q
                  }
                }
                """
                ,"/A.java:14: A field may not be read in a secret context unless it is in the same secret datagroup: q not in value",5
                ,"/A.java:14: The field q is not writable since it is not in the value secret datagroup",5
        );
    }

    @Test
    public void testQuery11() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ @Secret model int value;
                  //@ @Secret public model Object o;
                   @Secret
                   int q = 5; //@ in o;
                  @Pure
                  public int compute() { return 0; }
                  int f;
                  @Secret
                  Integer cache = null; //@ in value;
                  @Secret
                  public void mm() { } // ERROR - methods must have a argument to @Secret
                }
                """
                ,"/A.java:12: A secret annotation on a method must have exactly one argument",3
        );
    }

    // FIXME - what about secret invariants, represents clauses or initializers of secret fields
    // FIXME - what about reading from/writing to - selections and array references
    // FIXME - what about calling non-secret methods, constructors

}
