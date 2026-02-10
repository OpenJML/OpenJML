package org.jmlspecs.openjmltest.testsuites;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class SFBugs extends EscBaseFiles {
    
    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        ignoreNotes = true;
        super.setUp();
    }
    
    // FIXME: Eventually, remove all --verify-exit=-1 options -- they have the effect of turning verification failures 
    // into pure warnings, both the in the diagnostic messages and the returned error code.
    // To fix this means editing all the expected output files.
    
    public void helpTG(String... opts) {
        super.helpTG(opts);
    }

    public void helpTCF(String sourceDirname, String outDir, String ... opts) {
        //Assert.fail(); // FIXME - Java8 - long running
        ArrayList<String> list = new ArrayList<String>();
        list.add("-code-math=safe");
        list.add("-spec-math=bigint");
        list.add("--check-feasibility=precondition,reachable,exit,spec");
        list.add("--progress");
  //      list.add("--verify-exit=-1");
        list.addAll(Arrays.asList(opts));
        escOnFiles(sourceDirname,outDir,list.toArray(opts));
    }

    public void helpTGNoOptions(String ... opts) {
        String dir = "test/" + getTestName();
        List<String> a = new LinkedList<>();
        a.add(0,"-cp"); 
        a.add(1,dir);
     //   a.add("--verify-exit=-1");
        a.addAll(Arrays.asList(opts));
        escOnFiles(dir, dir, a.toArray(new String[a.size()]));
    }

    // FIXME - change to use routines in EscBaseFiles

    @Test public void gitbug257() {
        helpTCF("test/gitbug257","test/gitbug257", "-cp", "test/gitbug257", "--esc", "--progress", "-logic=AUFNIRA");
    }
    
    @Test public void gitbug260() {
        helpTCF("test/gitbug260","test/gitbug260", "-cp", "test/gitbug260", "--esc", "--progress");
    }
    
    @Test public void gitbug450() {
        expectedExit = 1;
        ignoreNotes = true;
        helpTCF("test/gitbug450","test/gitbug450", "-cp", "test/gitbug450", "--esc", "--progress");
    }
    
    @Test public void gitbug450c() {
        helpTCF("test/gitbug450c","test/gitbug450c", "-cp", "test/gitbug450c", "--esc", "--progress");
    }
    
    @Test public void gitbug454() {
        helpTCF("test/gitbug454","test/gitbug454", "-cp", "test/gitbug454", "--esc");
    }
    
    @Test public void gitbug457() {
        helpTG("-nullableByDefault");
    }
    
    @Test public void gitbug457a() {
        helpTG("-nonnullByDefault");
    }
    
    @Test public void gitbug458() {
        helpTCF("test/gitbug458","test/gitbug458", "-cp", "test/gitbug458", "--esc","--check-feasibility=precondition,reachable,exit,spec,assume,assert");
    }
    
    @Test public void gitbug458a() {
        helpTCF("test/gitbug458a","test/gitbug458a", "-cp", "test/gitbug458a", "--esc","--check-feasibility=precondition,reachable,exit,spec,assume,assert");
    }
    
    @Test public void gitbug458b() {
        helpTCF("test/gitbug458b","test/gitbug458b", "-cp", "test/gitbug458b", "--esc");
    }
    
    @Test public void gitbug459() {
        helpTCF("test/gitbug459","test/gitbug459", "-cp", "test/gitbug459", "--esc");
    }
    
    @Test public void gitbug462() {
        helpTCF("test/gitbug462","test/gitbug462", "-cp", "test/gitbug462", "--esc");
    }
    
    @Test public void gitbug462a() {
        helpTCF("test/gitbug462a","test/gitbug462a", "-cp", "test/gitbug462a", "--esc");
    }
    
    @Test public void gitbug462b() {
        helpTCF("test/gitbug462b","test/gitbug462b", "-cp", "test/gitbug462b", "--esc");
    }
    
    @Test public void gitbug462c() {
        helpTCF("test/gitbug462c","test/gitbug462c", "-cp", "test/gitbug462c", "--esc");
    }
    
    @Test public void gitbug456() {
        helpTCF("test/gitbug456","test/gitbug456", "-cp", "test/gitbug456", "--esc", "--exclude", "bytebuf.ByteBuf.*");
    }
    
    @Test public void gitbug456a() {
        helpTCF("test/gitbug456a","test/gitbug456a", "-cp", "test/gitbug456a", "--esc", "--exclude", "bytebuf.ByteBuf.*");
    }
    
    @Test public void gitbug455() {
        helpTCF("test/gitbug455","test/gitbug455", "-cp", "test/gitbug455", "--esc");
    }
    
    @Ignore // FIXME - needs ability to specify/reason about derived classes
    @Test public void gitbug446() {
        helpTCF("test/gitbug446","test/gitbug446", "-cp", "test/gitbug446", "--esc");
    }
    
    @Ignore // FIXME - syntax for model programs not settled
    @Test public void gitbug445() {
        expectedExit = 1;
        helpTG();
    }
    
    @Ignore // FIXME - syntax for model programs not settled
    @Test public void gitbug445a() {
        helpTG();
    }
    
    @Test public void gitbug463() {
        helpTCF("test/gitbug463","test/gitbug463", "-cp", "test/gitbug463");
    }
    
    @Test public void gitbug463a() {
        helpTCF("test/gitbug463a","test/gitbug463a", "-cp", "test/gitbug463a");
    }
    
    @Test public void gitbug444() {
        helpTCF("test/gitbug444","test/gitbug444", "-cp", "test/gitbug444");
    }
    
    @Test public void gitbug444a() {
        helpTCF("test/gitbug444a","test/gitbug444a", "-cp", "test/gitbug444a");
    }

    @Test public void gitbug466() {
        helpTCF("test/gitbug466","test/gitbug466", "-cp", "test/gitbug466");
    }

    @Test public void gitbug467() {
        helpTG();
    }

    @Test public void gitbug470() {
        helpTCF("test/gitbug470/ACD.java","test/gitbug470", "-cp", "test/gitbug470","--code-math=java");
    }

    @Test public void gitbug471() {
        helpTG();
    }

    @Test public void gitbug469() {
        helpTG();
    }

    @Test public void gitbug474() {
        helpTG();
    }

    @Test public void gitbug476() {
        helpTG();
    }

    @Test public void gitbug477() {
        helpTG();
    }

    @Test public void gitbug478() {
        helpTG();  // NOTE: Uses a custom instance of ByteBuffer.jml, which made the original bug
    }

    @Test public void gitbug480() {
        helpTG();
    }

    @Test public void gitbug497() {
        helpTG();
    }

    @Test public void gitbug499() {
        expectedExit = 1;
        helpTG();
    }

    @Test public void gitbug502() {
        helpTG();
    }

    // FIXME - problem in 503 is that various subtests non-deterministically timeout
    // This seems particularly the case with A1 and A4, which have an extraneous template argument
    @Ignore // times out
    @Test public void gitbug503() {
        helpTG("--code-math=java","--timeout=600","--solver-seed=142"); // java math just to avoid overflow error messages
    }

    @Ignore // times out
    @Test public void gitbug503a() {
        helpTG("--code-math=java","--timeout=600","--solver-seed=42"); // java math just to avoid overflow error messages
    }

    @Test public void gitbug535() {
        helpTG();
    }

    @Test public void gitbug538() {
        helpTG();
    }

    @Test public void gitbug539() {
        helpTG();
    }

    @Test public void gitbug540() {
        helpTG();
    }

    @Test public void gitbug543() {
        helpTG();  // FIXME - demonstrates problems with quantification over arrays
    }

    @Test public void gitbug545() {
        helpTG();
    }

    @Test public void gitbug548() {
        helpTG("--nullable-by-default");
    }
    
    @Test public void gitbug550() {
        helpTG();
    }
    
    @Test public void gitbug554() {
        helpTG();
    }
    
    @Test public void gitbug555() {
        helpTG();
    }
    
    @Test public void gitbug555a() {
        helpTG("--check-feasibility=none");
    }
    
    @Test public void gitbug555b() {
        helpTG("--method=Test.1.show");
    }

    @Test public void gitbug518() {
        expectedExit = 1;
        helpTG("--check");  // Just checking
    }

    @Test public void gitbug528() {
        helpTG("--lang=jml","--check");  // Just checking
    }

    // Check everything in apache commons library!
    // FIXME - Needs more specification to avoid the errors reported in the tests below

    @Ignore // This checks everything - which times out - so the verification is broken up in other tests
    @Test public void gitbug481() {
        helpTCF("test/gitbug481b","test/gitbug481", "-cp", "test/gitbug481b","--progress");
    }

    // Just one method, but parse and typecheck all files first
    @Test public void gitbug481c() {
        helpTCF("test/gitbug481b","test/gitbug481c", "-cp", "test/gitbug481b","--method=org.apache.commons.math3.linear.ArrayFieldVector.getEntry");
    }

    // Just one method in one file
    @Test public void gitbug481b() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481b", "-cp", "test/gitbug481b","--method=org.apache.commons.math3.linear.ArrayFieldVector.getEntry","-no-staticInitWarning");
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
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a1", "-cp", "test/gitbug481b","--method="+m1,"-no-staticInitWarning");
    }

    @Test public void gitbug481a2() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a2", "-cp", "test/gitbug481b","--method="+m2,"-no-staticInitWarning");
    }

    @Test public void gitbug481a3() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a3", "-cp", "test/gitbug481b","--method="+m3,"-no-staticInitWarning");
    }

    @Test public void gitbug481a4() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a4", "-cp", "test/gitbug481b","--method="+m4,"-no-staticInitWarning");
    }

    @Test public void gitbug481a5() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a5", "-cp", "test/gitbug481b","--method="+m5,"-no-staticInitWarning");
    }

    @Ignore // Requires more specs in the library
    @Test public void gitbug481a6() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a6", "-cp", "test/gitbug481b","--method="+m6,"-no-staticInitWarning");
    }

    @Ignore // Requires more specs in the library
    @Test public void gitbug481a7() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a7", "-cp", "test/gitbug481b","--method="+m7,"-no-staticInitWarning");
    }

    @Test public void gitbug481a8() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a8", "-cp", "test/gitbug481b","--method="+m8,"-no-staticInitWarning");
    }

    @Ignore // Requires more specs in the library
    @Test public void gitbug481a9() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a9", "-cp", "test/gitbug481b","--method="+m9,"-no-staticInitWarning");
    }

    @Ignore // FIXME - Out of memory
    @Test public void gitbug481a10() {
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a10", "-cp", "test/gitbug481b","--method="+m10,"-no-staticInitWarning","--solver-seed=42");
    }

    @Ignore // FIXME - timeout
    @Test public void gitbug481a() { // The rest
        expectedExit = 1;
        helpTCF("test/gitbug481b/org/apache/commons/math3/linear/ArrayFieldVector.java","test/gitbug481a", "-cp", "test/gitbug481b","--exclude="+all,"-no-staticInitWarning","--solver-seed=142");
    }

    @Ignore // FIXME - needs work
    @Test public void gitbug482() {
        helpTCF("test/gitbug482/checkers/src/main/java/checkers","test/gitbug482", "-cp", "test/gitbug482/checkers/src/main","--check"); // check only, not esc
    }

    @Test public void gitbug556() {
        helpTG();
    }
    
    @Test public void gitbug557() {
        helpTG();
    }
    
    @Test public void gitbug558() {
        helpTG();
    }
    
    @Test public void gitbug558a() {
        helpTG();
    }
    
    @Test public void gitbug558b() {
        helpTG();
    }
    
    @Test public void gitbug559() {
        helpTG();
    }
    
    @Test public void gitbug559a() {
        helpTG();
    }
    
    @Test public void gitbug560() {
        helpTG("--check-feasibility=none");
    }
    
    @Test public void gitbug567() {
        helpTG();
    }
    
    @Test public void gitbug567a() {
        helpTG("--code-math=java");
    }
    
    @Test public void gitbug567b() {
        helpTG("--code-math=safe");
    }
    
    @Test public void gitbug567c() {
        helpTG("--code-math=bigint");
    }
    
    @Test public void gitbug572() {
        expectedExit = 1;
        helpTG();
    }
    
    // The .jml file is on the command-line, which caused a crash, now fixed
    @Test public void gitbug573() {
        expectedExit = 2;
        helpTCF("test/gitbug573/pckg/A.jml","test/gitbug573","-sourcepath","test/gitbug573");
    }
    
    @Test public void gitbug573a() {
        helpTG();
    }
    
    // Here .jml is on the command-line, but the .java does not exist
    @Test public void gitbug573b() {
        expectedExit = 2;
        helpTCF("test/gitbug573b/pckg/A.jml","test/gitbug573b","-sourcepath","test/gitbug573b");
    }
    
    @Test public void gitbug573c() {
        expectedExit = 2;
        helpTCF("test/gitbug573c/java/lang/Integer.jml","test/gitbug573c","-sourcepath","test/gitbug573c");
    }
    
    @Test public void gitbug574() {
        helpTG();
    }
    
    @Test public void gitbug575() {
        helpTG();
    }
    
    @Test public void gitbug578() {
        helpTG();
    }
    
    @Test
    public void gitbug589() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
    public void gitbug591() {
        helpTG();
    }
    
    @Test
    public void gitbug593() {
        helpTG("-check");
    }
    
    @Test
    public void gitbug594() {
        helpTG();
    }
    
    @Test
    public void gitbug596a() {
        helpTG();
    }
    
    @Test
    public void gitbug596b() {
        helpTG();
    }
    
    @Test
    public void gitbug596c() {
        helpTG();
    }
    
    @Test
    public void gitbug596d() {
        helpTG();
    }
    
    @Test
    public void gitbug597() {
        helpTG("--esc-max-warnings=1");
    }
    
    @Test
    public void gitbug598() {
        helpTG();
    }
    
    @Test
    public void gitbug598a() {
        helpTG();
    }
    
    @Test
    public void gitbug602() {
        helpTG("-Xlint:unchecked");
    }
    
    @Test
    public void gitbug603() {
        expectedExit = Main.Result.CMDERR.exitCode;
        helpTG("-Xmaxwarns=100"); // Arguments are part of the test
    }
    
    @Ignore   // FIXME requires implementation of \not_assigned
    @Test
    public void gitbug604() {
        helpTG("--code-math=safe","--method=AbsInterval.add");
    }
    
    @Test
    public void gitbug605() {
        helpTG("--code-math=safe");
    }
    
    @Test
    public void gitbug606() {
        helpTG("--code-math=safe");
    }
    
    @Test
    public void gitbug607() {
        helpTG("--show","--method=x"); // Arguments are part of the test
    }
    
    @Test
    public void gitbug608() {
        helpTG();
    }
    
    @Test
    public void gitbug610() {
        helpTG("--code-math=safe");
    }
    
    @Test
    public void gitbug611() {
        helpTG();
    }
    
    @Test
    public void gitbug613() {
        helpTG();
    }
    
    @Test
    public void gitbug615() {
        helpTG();
    }
    
    @Test
    public void gitbug618() {
        helpTG("--check-feasibility=precondition,reachable,exit,spec,assume,assert");
    }
    
    @Test
    public void gitbug621() {
        helpTG();
    }
    
    @Test
    public void gitbug621a() { // Original bug
        helpTG("--method=testMethod"); // Limited to this one method
    }
    
    @Test
    public void gitbug622() { // Problem with implicit assertion about string literal
        helpTG("-staticInitWarning");
    }
    
    @Test
    public void gitbug623() {
        helpTG("--check-feasibility=precondition,reachable,exit,spec,assume,assert");
    }
    
    @Ignore // Varying test output in trace
    @Test
    public void gitbug626() {
        helpTG("--subexpressions");
    }
    
    @Ignore // FIXME - Problem with fresh in loop bodies
    @Test
    public void gitbug627() {
        helpTG();
    }
    
    @Test
    public void gitbug629() {
        helpTG();
    }
    
    @Test
    public void gitbug629a() {
        helpTG();
    }
    
    @Test
    public void gitbug630() {
        helpTG();
    }
    
    @Test
    public void gitbug630a() { // FIXME - SMT encpoding problem
        helpTG();
    }
    
    @Test
    public void gitbug631() {
        helpTG("--check-feasibility=precondition,reachable,exit,spec,assume,assert");
    }
    
    @Test  // Z3 non-deterministically crashes; trying to fix that by specifying the seed
    public void gitbug633a() {
        helpTG("--solver-seed=42");
    }
    
    @Test
    public void gitbug634() {
        helpTG();
    }
    
    @Test
    public void gitbug635() {
        expectedExit = 6;
        helpTG("--verify-exit=6"); // FIXME - remove this option when all the others are adjusted to non-legacy behavior
    }
    
    @Test
    public void gitbug636() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
    public void gitbug637() {
        helpTG();
    }

    @Test
    public void gitbug638() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
   public void gitbug639() {
       helpTG();
   }
   
    @Test
   public void gitbug639a() {
       helpTG();
   }
   
    @Test
    public void gitbug640() {
        helpTG();
    }
    
    @Test
    public void gitbug643() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
    public void gitbug644() {
        helpTG();
    }
        
    @Test
    public void gitbug647() {
        helpTG();
    }
    
    @Test
    public void gitbug648() {
        helpTG();
    }
    
    @Test
    public void gitbug648a() {
        expectedExit = 6;
        helpTG("-cp","test/gitbug648","--verify-exit=6");
    }
    
    @Test
    public void gitbug650() {
        helpTG();
    }
    
    @Test
    public void gitbug650a() {
        helpTG();
    }
    
    @Test
    public void gitbug650b() {
        helpTG();
    }
    
    @Test
    public void gitbug650c() {
        helpTG();
    }

    @Test
    public void gitbug651() {
        helpTG();
    }

    @Test
    public void gitbug651a() {
        expectedExit = 1;
        helpTG(); 
    }   
        
    @Test
    public void gitbug651b() {
        helpTG();
    }

    @Test
    public void gitbug653() {
        helpTG("--specs-path=test/gitbug653");
    }
    
    @Test
    public void gitbug654() {
        helpTG();
    }
    
    @Test
    public void gitbug659() {
        helpTG();
    }
    
    
    @Test
    public void gitbug667() {
        helpTG();
    }
    
    @Test
    public void gitbug669() {
    }
    
    @Test
    public void gitbug666() {
    }
    
    @Test
    public void gitbug670() {
        helpTG();
    }
    
    @Test // FIXME -- Crash in speculative attribution
    public void gitbug671() {
        helpTCF("test/gitbug672/commons-collections4-4.3-sources/org/apache/commons/collections4/set/ListOrderedSet.java","test/gitbug671","--timeout=1800","-no-staticInitWarning","-cp","test/gitbug672/commons-collections4-4.3-sources","--esc-max-warnings=1");
    }
    
    @Test @Ignore // FIXME -- nullpointer exception, time out //  // Complained of infinite run time
    public void gitbug672() {
        helpTCF("test/gitbug672/commons-collections4-4.3-sources/org/apache/commons/collections4/bidimap/TreeBidiMap.java","test/gitbug672","--timeout=1800","-no-staticInitWarning","-cp","test/gitbug672/commons-collections4-4.3-sources","--esc-max-warnings=1");
    }
    
    @Test
    public void gitbug676() {
        helpTG();
    }
    
    @Test @Ignore // FIXME - this seems to be an incompleteness or bug in Z3 non-linear computations
    public void gitbug677() {
        helpTG("--code-math=safe");//,"-show","-method=calculateArea","-subexpressions","-ce"); // The problem manifests with safe math
    }
    
    @Test
    public void gitbug678() {
        helpTG();
    }
    
    @Test
    public void gitbug681() {
        helpTG();
    }
    
    @Test
    public void gitbug682() {
        helpTG();
    }
    
    @Test
    public void gitbug683() {
        helpTG();
    }
    
    @Test
    public void gitbug684() {
        helpTG();
    }
    
    @Test
    public void gitbug685() {
        helpTG();
    }
    
    @Test
    public void gitbug686() {
        helpTG();
    }
    
    @Test
    public void gitbug687() {
        helpTG();
    }
    
    @Test
    public void gitbug688() {
        helpTG("--subexpressions");
    }
    
    @Test
    public void gitbug688err() {
        expectedExit = 1;
        helpTG("--subexpressions");
    }
    
    @Test
    public void gitbug695() {
        helpTG("--check-feasibility=precondition,reachable,exit,spec,assume,assert");
    }
    
    @Test
    public void gitbug696() {
        helpTG();
    }
    
    @Test
    public void gitbug698() {
        helpTG();
    }
    
    @Test
    public void gitbug698A() {
        helpTG();
    }
    
    @Test @Ignore // Will erroneously succeed until measured_by is implemented
    public void gitbug705() {
        helpTG();
    }

    @Test @Ignore // FIXME: Bug fixed, but the specs are not complete
    public void gitbug710() {
        helpTCF("test/gitbug710/java/util/IdentityHashMap.java", "test/gitbug710","-cp","test/gitbug710","-no-staticInitWarning","--timeout=300");
    }
    
    @Test
    public void gitbug711() {
        helpTG();
    }
    
    @Test
    public void gitbug712() {
        helpTG();
    }
    
    @Test
    public void gitbug716() {
        helpTG();
    }
    
    @Test @Ignore // FIXME: EXAMPLE SPECS NOT YET COMPLETE
    public void gitbug717() {
        helpTG();
    }
    
    @Test @Ignore // FIXME: Specs not yet finished
    public void gitbug718() {
        helpTG();
    }
    
    @Test
    public void gitbug718a() {
        helpTG();
    }
    
    @Test
    public void gitbug718x1() {
        helpTG();
    }
    
    @Test
    public void gitbug718x2() {
        helpTG();
    }
    
    @Test
    public void gitbug718x4() {
        helpTG();
    }
    
    @Test
    public void gitbug719() {
        helpTG();
    }
    
    @Test
    public void gitbug719a() {
        helpTG();
    }
    
    @Test
    public void gitbug722() {
        helpTG();
    }
    
    @Test
    public void gitbug733() {
        helpTG();
    }
    
    @Test
    public void gitbug733a() {
        helpTG();
    }
    
    @Test
    public void gitbug734() {
        helpTG();
    }
    
    @Test
    public void gitbug736() {
        helpTG();
    }
    
    @Test
    public void gitbug737() {
        helpTG();
    }
    
    @Test
    public void gitbug738() {
        helpTG("--warn=missing-measured-by","--check-feasibility=none");
    }
    
    @Test
    public void gitbug738a() {
        helpTG("--check-feasibility=none");
    }
    
    @Test
    public void gitbug740() {
        helpTG("--check-feasibility=none");
    }
    
    @Test
    public void gitbug741() {
        expectedExit = 1;
        helpTG();
    }
    
    @Test
    public void gitbug888() {
        helpTG("--check-feasibility=all");
    }
    
    @Test
    public void gitbug888a() {
        helpTG("--check-feasibility=basic");
    }
    
    @Test
    public void gitbug998() {
        helpTG();
    }
    
    @Test
    public void gitbug999() {
        helpTG();
    }
    
    @Test
    public void rise4fun() {
        helpTGNoOptions("--check-feasibility=precondition,exit");
    }

}

