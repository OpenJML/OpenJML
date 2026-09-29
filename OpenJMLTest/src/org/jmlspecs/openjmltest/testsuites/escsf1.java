package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.SFBugsBase;
import org.jmlspecs.openjml.Main;

import java.util.*;

import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** Part 1 of the escsf tests (formerly SFBugs) (split in three so that no one suite dominates a parallel run); the
 * shared setup and helper methods are in SFBugsBase. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escsf1 extends SFBugsBase {

    @Test public void gitbug257() {
        helpEscFile("test/gitbug257","test/gitbug257", "-cp", "test/gitbug257", "--esc", "--progress", "-logic=AUFNIRA");
    }
    
    @Test public void gitbug260() {
        helpEscFile("test/gitbug260","test/gitbug260", "-cp", "test/gitbug260", "--esc", "--progress");
    }
    
    @Test public void gitbug450() {
        expectedExit = 1;
        ignoreNotes = true;
        helpEscFile("test/gitbug450","test/gitbug450", "-cp", "test/gitbug450", "--esc", "--progress");
    }
    
    @Test public void gitbug450c() {
        helpEscFile("test/gitbug450c","test/gitbug450c", "-cp", "test/gitbug450c", "--esc", "--progress");
    }
    
    @Test public void gitbug454() {
        helpEscFile("test/gitbug454","test/gitbug454", "-cp", "test/gitbug454", "--esc");
    }
    
    @Test public void gitbug457() {
        helpEscSimple("-nullableByDefault");
    }
    
    @Test public void gitbug457a() {
        helpEscSimple("-nonnullByDefault");
    }
    
    @Test public void gitbug458() {
        helpEscFile("test/gitbug458","test/gitbug458", "-cp", "test/gitbug458", "--esc","--check-feasibility=precondition,reachable,exit,spec,assume,assert");
    }
    
    @Test public void gitbug458a() {
        helpEscFile("test/gitbug458a","test/gitbug458a", "-cp", "test/gitbug458a", "--esc","--check-feasibility=precondition,reachable,exit,spec,assume,assert");
    }
    
    @Test public void gitbug458b() {
        helpEscFile("test/gitbug458b","test/gitbug458b", "-cp", "test/gitbug458b", "--esc");
    }
    
    @Test public void gitbug459() {
        helpEscFile("test/gitbug459","test/gitbug459", "-cp", "test/gitbug459", "--esc");
    }
    
    @Test public void gitbug462() {
        helpEscFile("test/gitbug462","test/gitbug462", "-cp", "test/gitbug462", "--esc");
    }
    
    @Test public void gitbug462a() {
        helpEscFile("test/gitbug462a","test/gitbug462a", "-cp", "test/gitbug462a", "--esc");
    }
    
    @Test public void gitbug462b() {
        helpEscFile("test/gitbug462b","test/gitbug462b", "-cp", "test/gitbug462b", "--esc");
    }
    
    @Test public void gitbug462c() {
        helpEscFile("test/gitbug462c","test/gitbug462c", "-cp", "test/gitbug462c", "--esc");
    }
    
    @Test public void gitbug456() {
        helpEscFile("test/gitbug456","test/gitbug456", "-cp", "test/gitbug456", "--esc", "--exclude", "bytebuf.ByteBuf.*");
    }
    
    @Test public void gitbug456a() {
        helpEscFile("test/gitbug456a","test/gitbug456a", "-cp", "test/gitbug456a", "--esc", "--exclude", "bytebuf.ByteBuf.*");
    }
    
    @Test public void gitbug455() {
        helpEscFile("test/gitbug455","test/gitbug455", "-cp", "test/gitbug455", "--esc");
    }
    
    @Ignore // FIXME - needs ability to specify/reason about derived classes
    @Test public void gitbug446() {
        helpEscFile("test/gitbug446","test/gitbug446", "-cp", "test/gitbug446", "--esc");
    }
    
    @Ignore // FIXME - syntax for model programs not settled
    @Test public void gitbug445() {
        expectedExit = 1;
        helpEscSimple();
    }
    
    @Ignore // FIXME - syntax for model programs not settled
    @Test public void gitbug445a() {
        helpEscSimple();
    }
    
    @Test public void gitbug463() {
        helpEscFile("test/gitbug463","test/gitbug463", "-cp", "test/gitbug463");
    }
    
    @Test public void gitbug463a() {
        helpEscFile("test/gitbug463a","test/gitbug463a", "-cp", "test/gitbug463a");
    }
    
    @Test public void gitbug444() {
        helpEscFile("test/gitbug444","test/gitbug444", "-cp", "test/gitbug444");
    }
    
    @Test public void gitbug444a() {
        helpEscFile("test/gitbug444a","test/gitbug444a", "-cp", "test/gitbug444a");
    }

    @Test public void gitbug466() {
        helpEscFile("test/gitbug466","test/gitbug466", "-cp", "test/gitbug466");
    }

    @Test public void gitbug467() {
        helpEscSimple();
    }

    @Test public void gitbug470() {
        helpEscFile("test/gitbug470/ACD.java","test/gitbug470", "-cp", "test/gitbug470","--code-math=java");
    }

    @Test public void gitbug471() {
        helpEscSimple();
    }

    @Test public void gitbug469() {
        helpEscSimple();
    }

    @Test public void gitbug474() {
        helpEscSimple();
    }

    @Test public void gitbug476() {
        helpEscSimple();
    }

    @Test public void gitbug477() {
        helpEscSimple();
    }

    @Test public void gitbug478() {
        helpEscSimple();  // NOTE: Uses a custom instance of ByteBuffer.jml, which made the original bug
    }

    @Test public void gitbug480() {
        helpEscSimple("--no-allow-pure-in-specs");
    }

    @Test public void gitbug497() {
        helpEscSimple();
    }

    @Test public void gitbug499() {
        expectedExit = 1;
        helpEscSimple();
    }

    @Test public void gitbug502() {
        helpEscSimple();
    }

    // FIXME - problem in 503 is that various subtests non-deterministically timeout
    // This seems particularly the case with A1 and A4, which have an extraneous template argument
    @Ignore // times out
    @Test public void gitbug503() {
        helpEscSimple("--code-math=java","--timeout=600","--solver-seed=142"); // java math just to avoid overflow error messages
    }

    @Ignore // times out
    @Test public void gitbug503a() {
        helpEscSimple("--code-math=java","--timeout=600","--solver-seed=42"); // java math just to avoid overflow error messages
    }

    @Test public void gitbug535() {
        helpEscSimple();
    }

    @Test public void gitbug538() {
        helpEscSimple();
    }

    @Test public void gitbug539() {
        helpEscSimple();
    }

    @Test public void gitbug540() {
        helpEscSimple();
    }

    @Test public void gitbug543() {
        helpEscSimple();  // FIXME - demonstrates problems with quantification over arrays
    }

    @Test public void gitbug545() {
        helpEscSimple();
    }

    @Test public void gitbug548() {
        helpEscSimple("--nullable-by-default");
    }
    
    @Test public void gitbug550() {
        helpEscSimple();
    }
    
    @Test public void gitbug554() {
        helpEscSimple();
    }
    
    @Test public void gitbug555() {
        helpEscSimple();
    }
    
    @Test public void gitbug555a() {
        helpEscSimple("--check-feasibility=none");
    }
    
    @Test public void gitbug555b() {
        helpEscSimple("--method=Test.1.show");
    }

    @Test public void gitbug518() {
        expectedExit = 1;
        helpEscSimple("--check");  // Just checking
    }

    @Test public void gitbug528() {
        helpEscSimple("--lang=jml","--check");  // Just checking
    }

    // Check everything in apache commons library!
    // FIXME - Needs more specification to avoid the errors reported in the tests below

    @Ignore // This checks everything - which times out - so the verification is broken up in other tests
    @Test public void gitbug481() {
        helpEscFile("test/gitbug481b","test/gitbug481", "-cp", "test/gitbug481b","--progress");
    }

    // Just one method, but parse and typecheck all files first
    @Test public void gitbug481c() {
        helpEscFile("test/gitbug481b","test/gitbug481c", "-cp", "test/gitbug481b","--method=org.apache.commons.math3.linear.ArrayFieldVector.getEntry");
    }

    // Just one method in one file
    @Test public void gitbug481b() {
        helpEscFile("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481b", "-cp", "test/gitbug481b","--method=org.apache.commons.math3.linear.ArrayFieldVector.getEntry","-no-staticInitWarning");
    }

    static String p = "org.apache.commons.math3.linear.ArrayFieldVector.";
    static String m1 = p + "ArrayFieldVector(org.apache.commons.math3.Field<T>)";
    static String m2 = p + "ArrayFieldVector(org.apache.commons.math3.Field<T>,int)";
    static String m3 = p + "ArrayFieldVector(int,T)";
    static String m4 = p + "ArrayFieldVector(org.apache.commons.math3.linear.ArrayFieldVector<T>,boolean)";
    static String m5 = p + "ArrayFieldVector(org.apache.commons.math3.linear.ArrayFieldVector<T>,org.apache.commons.math3.linear.ArrayFieldVector<T>)";
    static String m6 = p + "ArrayFieldVector(org.apache.commons.math3.linear.FieldVector<T>,org.apache.commons.math3.linear.FieldVector<T>)";
    static String m7 = p + "ArrayFieldVector(org.apache.commons.math3.linear.FieldVector<T>,T[])";
    static String m8 = p + "ArrayFieldVector(T[],org.apache.commons.math3.linear.ArrayFieldVector<T>)";
    static String m9 = p + "ArrayFieldVector(T[],org.apache.commons.math3.linear.FieldVector<T>)";
    static String m10 = p + "ArrayFieldVector(T[],T[])";
    
    static String all = m1+";"+m2+";"+m3+";"+m4+";"+m5+";"+m6+";"+m7+";"+m8+";"+m9+";"+m10;
    
    @Test public void gitbug481a1() {
        helpEscFile("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a1", "-cp", "test/gitbug481b","--method="+m1,"-no-staticInitWarning");
    }

    @Test public void gitbug481a2() {
        helpEscFile("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a2", "-cp", "test/gitbug481b","--method="+m2,"-no-staticInitWarning");
    }

    @Test public void gitbug481a3() {
        helpEscFile("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a3", "-cp", "test/gitbug481b","--method="+m3,"-no-staticInitWarning");
    }

    @Test public void gitbug481a4() {
        helpEscFile("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a4", "-cp", "test/gitbug481b","--method="+m4,"-no-staticInitWarning");
    }

    @Test public void gitbug481a5() {
        helpEscFile("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a5", "-cp", "test/gitbug481b","--method="+m5,"-no-staticInitWarning");
    }

    @Ignore // Requires more specs in the library
    @Test public void gitbug481a6() {
        helpEscFile("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a6", "-cp", "test/gitbug481b","--method="+m6,"-no-staticInitWarning");
    }

    @Ignore // Requires more specs in the library
    @Test public void gitbug481a7() {
        helpEscFile("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a7", "-cp", "test/gitbug481b","--method="+m7,"-no-staticInitWarning");
    }

    @Test public void gitbug481a8() {
        helpEscFile("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a8", "-cp", "test/gitbug481b","--method="+m8,"-no-staticInitWarning");
    }

    @Ignore // Requires more specs in the library
    @Test public void gitbug481a9() {
        helpEscFile("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a9", "-cp", "test/gitbug481b","--method="+m9,"-no-staticInitWarning");
    }

    @Ignore // FIXME - Out of memory
    @Test public void gitbug481a10() {
        helpEscFile("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a10", "-cp", "test/gitbug481b","--method="+m10,"-no-staticInitWarning","--solver-seed=42");
    }

    @Ignore // FIXME - timeout
    @Test public void gitbug481a() { // The rest
        expectedExit = 1;
        helpEscFile("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a", "-cp", "test/gitbug481b","--exclude="+all,"-no-staticInitWarning","--solver-seed=142");
    }

}
