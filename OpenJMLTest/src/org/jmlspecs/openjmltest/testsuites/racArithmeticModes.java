package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.RacBase;

import org.junit.*;

/** These tests exercise the RAC checking.  They compile a test class 
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racArithmeticModes extends RacBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("-jmltesting");
    }
    
    @Override
    public void tearDown() throws Exception {
        testspecpath1 = "$A"+z+"$B";
    }


    @Test public void testNegJava() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = -250000; int k = -i; System.out.println((k==i) + \" \" + (k+i) + \" END\"); \n" +
                 "i = Integer.MIN_VALUE;  k = -i; System.out.println((k==i) + \" END\");} \n" +
                "}"
                ,"false 0 END"
                ,"true END"
                );
        
    }

    @Test public void testNegJavaLong() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "long i = -250000; long k = -i; System.out.println((k==i) + \" \" + (k+i) + \" END\"); \n" +
                 "i = Long.MIN_VALUE;  k = -i; System.out.println((k==i) +  \" END\");} \n" +
                "}"
                ,"false 0 END"
                ,"true END"
                );
        
    }

    @Test public void testNegSafe() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                                "int i = -250000; int k = -i; System.out.println((k==i) + \" \" + (k+i) + \" END\"); \n" +
                                "i = Integer.MIN_VALUE;  k = -i; \n System.out.println((k==i) + \" END\");} \n" +
                "}"
                ,"false 0 END"
                ,"/tt/TestJava.java:3: JML result of numeric operation is out of range of the target type"
                ,"true END"
                );
        
    }

    @Test public void testNegSafeLong() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                                "long i = -250000; long k = -i; System.out.println((k==i) + \" \" + (k+i) + \" END\"); \n" +
                                "i = Long.MIN_VALUE;  k = -i; System.out.println((k==i) + \" END\");} \n" +
                "}"
                ,"false 0 END"
                ,"/tt/TestJava.java:3: JML result of numeric operation is out of range of the target type"
                ,"true END"
                );
        
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testNegMath() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int j = Integer.MAX_VALUE; long k = -j; \nSystem.out.println(k + \" END\"); \n" +
                "int i = Integer.MIN_VALUE; long kk = -i; \nSystem.out.println(kk + \" END\");} \n" +
                "}"
                ,"-2147483647 END"
                ,"2147483648 END"
                );
    }

    // FIXME - in bigint mode, should all integer decls be bigint instead?
    @Ignore // No CodeBigintMath as yet
    @Test public void testNegMath2() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int j = Integer.MAX_VALUE; int k = -j; \nSystem.out.println(k + \" END\"); \n" +
                "int i = Integer.MIN_VALUE; int kk = -i; \nSystem.out.println(kk + \" END\");} \n" +
                "}"
                ,"-2147483647 END"
                ,"verify: JML argument to numeric cast is out of range of the target type"
                ,"-2147483648 END"
                );
    }

    // FIXME - in bigint mode, should all integer decls be bigint instead?
    @Ignore // No CodeBigintMath as yet
    @Test public void testNegMathLong() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "long j = Long.MAX_VALUE; long k = -j; \nSystem.out.println(k + \" END\"); \n" +
                "long i = Long.MIN_VALUE; long kk = -i; \nSystem.out.println(kk + \" END\");} \n" +
                "}"
                ,"-9223372036854775807 END"
                ,"verify: JML argument to numeric cast is out of range of the target type"
                ,"-9223372036854775808 END"
                );
    }

    @Test public void testCompJava() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = ~i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 2147483647"
                );
    }
    @Test public void testCompSafe() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = ~i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 2147483647"
                );
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testCompMath() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = ~i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 2147483647"
                );
    }


    @Test public void testSumJava() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; int k = i + i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END -2"
                );
    }

    @Test public void testSumSafe() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; int k = i + i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END -2"
                );
    }

    @Test public void testSumJavaLong() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "long i = Long.MAX_VALUE; long k = i + i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END -2"
                );
    }

    @Test public void testSumSafeLong() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "long i = Long.MAX_VALUE; long k = i + i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END -2"
                );
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testSumMath() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; long k = i + i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 4294967294"
                );
    }

    // FIXME - still have to sort out how assignments are handled in Math mode
    @Ignore // No CodeBigintMath as yet
    @Test public void testSumMathCast() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; int k = i + i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML argument to numeric cast is out of range of the target type"
                ,"END -2"
                );
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testSumMathArg() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "  int i = Integer.MAX_VALUE; mm(i+i); } \n" +
                "  static void mm(int k) {System.out.println(\"END \" + k);} }"
                ,"/tt/TestJava.java:2: JML argument to numeric cast is out of range of the target type"
                ,"END -2"
                );
    }


    @Test public void testDiffJava() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; int k = i - Integer.MIN_VALUE; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END -1"
                );
    }

    @Test public void testDiffSafe() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; int k = i - Integer.MIN_VALUE; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END -1"
                );
    }

    @Test public void testDiffJavaLong() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "long i = Long.MAX_VALUE; long k = i - Long.MIN_VALUE; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END -1"
                );
    }

    @Test public void testDiffSafeLong() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "long i = Long.MAX_VALUE; long k = i - Long.MIN_VALUE; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END -1"
                );
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testDiffMath() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; long k = i - Integer.MIN_VALUE; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 4294967295"
                );
    }
 
    @Test public void testDivJava() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = i / (-1); System.out.println(\"END \" + (k==i));} \n" +
                "}"
                ,"END true"
                );
    }

    @Test public void testDivSafe() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = i / (-1); System.out.println(\"END \" + (k==i));} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END true"
                );
    }

    @Test public void testDivJavaLong() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "long i = Long.MIN_VALUE; long k = i / (-1); System.out.println(\"END \" + (k==i));} \n" +
                "}"
                ,"END true"
                );
    }

    @Test public void testDivSafeLong() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "long i = Long.MIN_VALUE; long k = i / (-1); System.out.println(\"END \" + (k==i));} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END true"
                );
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testDivMath() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; long k = i / (-1); System.out.println(\"END \" + (-k==i));} \n" +
                "}"
                ,"END true"
                );
    }

    @Test public void testMultJava() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                                "int i = 30000; int k = i * i; System.out.println(\"END \" + k); \n" +
                                " i = 70000;  k = i * i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 900000000"
                ,"END 605032704"
                );
    }

    @Test public void testMultSafe() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                                "int i = 30000; int k = i * i; System.out.println(\"END \" + k); \n" +
                                " i = 70000;  k = i * i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 900000000"
                ,"/tt/TestJava.java:3: JML result of numeric operation is out of range of the target type"
                ,"END 605032704"
                );
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testMultMath() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                                "int i = 30000; int k = i * i; System.out.println(\"END \" + k); \n" +
                                " i = 70000;  k = i * i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 900000000"
                ,"/tt/TestJava.java:3: JML argument to numeric cast is out of range of the target type"
                ,"END 605032704"
                );
    }

    @Test public void testMultJavaLong() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                                "long i = 2000000000L; long k = i * i; System.out.println(\"END \" + k); \n" +
                                " i = 5000000000L;  k = i * i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 4000000000000000000"
                ,"END 6553255926290448384"
                );
    }

    @Test public void testMultSafeLong() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                                "long i = 2000000000L; long k = i * i; System.out.println(\"END \" + k); \n" +
                                " i = 5000000000L;  k = i * i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 4000000000000000000"
                ,"/tt/TestJava.java:3: JML result of numeric operation is out of range of the target type"
                ,"END 6553255926290448384"
                );
    }

    @Ignore // No CodeBigintMath as yet
    @Test public void testMultMathLong() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                                "long i = 2000000000L; long k = i * i; System.out.println(\"END \" + k); \n" +
                                " i = 5000000000L;  k = i * i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 4000000000000000000"
                ,"/tt/TestJava.java:3: JML argument to numeric cast is out of range of the target type"
                ,"END 6553255926290448384"
                );
    }

    @Test
    public void testModJava() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecSafeMath public class TestJava { \n"
                +"  public static void main(String... args) {\n"
                +"    int k = 7 ;\n" 
                +"    int j = 3;\n" 
                +"    int m = 1;\n" 
                +"    int qq = 2;\n" 
                +"    int i = k % j;\n" 
                +"    int q = k / j;\n" 
                +"    //@ assert i == m && q == qq ;\n" 
                +"    //@ assert (k%j) == m && (k/j) == qq;\n" 
                +"    i = (-k) % j;\n" 
                +"    q = (-k) / j;\n" 
                +"    //@ assert i == -m && q == -qq;\n" 
                +"    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq;\n"   // Line 15
                +"    i = k % -j;\n" 
                +"    q = k / -j;\n" 
                +"    //@ assert i == m && q == -qq;\n" 
                +"    //@ assert (k%-j) == m && (k/-j) == -qq;\n" 
                +"    i = -k % -j;\n"                                   // Line 20
                +"    q = -k / -j;\n" 
                +"    //@ assert i == -m && q == qq;\n" 
                +"    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;\n" 
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testModSafe() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecSafeMath public class TestJava { \n"
                +"  public static void main(String... args) {\n"
                +"    int k = 7 ;\n" 
                +"    int j = 3;\n" 
                +"    int m = 1;\n" 
                +"    int qq = 2;\n" 
                +"    int i = k % j;\n" 
                +"    int q = k / j;\n" 
                +"    //@ assert i == m && q == qq ;\n" 
                +"    //@ assert (k%j) == m && (k/j) == qq;\n" 
                +"    i = (-k) % j;\n" 
                +"    q = (-k) / j;\n" 
                +"    //@ assert i == -m && q == -qq;\n" 
                +"    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq;\n"   // Line 15
                +"    i = k % -j;\n" 
                +"    q = k / -j;\n" 
                +"    //@ assert i == m && q == -qq;\n" 
                +"    //@ assert (k%-j) == m && (k/-j) == -qq;\n" 
                +"    i = -k % -j;\n"                                   // Line 20
                +"    q = -k / -j;\n" 
                +"    //@ assert i == -m && q == qq;\n" 
                +"    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;\n" 
                +"  }\n"
                +"}\n"
              );
    }

    @Ignore // No CodeBigintMath as yet
    @Test
    public void testModMath() {
        helpRacText("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath @SpecBigintMath public class TestJava { \n"
                +"  public static void main(String... args) {\n"
                +"    int k = 7 ;\n" 
                +"    int j = 3;\n" 
                +"    int m = 1;\n" 
                +"    int qq = 2;\n" 
                +"    int i = k % j;\n" 
                +"    int q = k / j;\n" 
                +"    //@ assert i == m && q == qq ;\n" 
                +"    //@ assert (k%j) == m && (k/j) == qq;\n" 
                +"    i = (-k) % j;\n" 
                +"    q = (-k) / j;\n" 
                +"    //@ assert i == -m && q == -qq;\n" 
                +"    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq;\n"   // Line 15
                +"    i = k % -j;\n" 
                +"    q = k / -j;\n" 
                +"    //@ assert i == m && q == -qq;\n" 
                +"    //@ assert (k%-j) == m && (k/-j) == -qq;\n" 
                +"    i = -k % -j;\n"                                   // Line 20
                +"    q = -k / -j;\n" 
                +"    //@ assert i == -m && q == qq;\n" 
                +"    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;\n" 
                +"  }\n"
                +"}\n"
              );
    }

}
