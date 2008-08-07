package tests;


public class esc extends EscBase {

    protected void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        options.put("-noPurityCheck","");
        //options.put("-jmlverbose",   "");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //org.jmlspecs.openjml.esc.JmlEsc.escdebug = true;
    }
    
    public void testStrings() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  String s;\n"
                +"  String ss = \"abcde\";\n"
                +"  public boolean m(String sss) {\n"
                +"    return sss == (\"abcde\");\n"
                +"  }\n"
                +"  public boolean m1(String sss) {\n"
                +"    return sss.equals(\"abcde\");\n"
                +"  }\n"
                +"}"
                );
    }

    public void testRequires() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  TestJava() { b = true; }\n"
                +"  public TestJava(int i) {}\n"  // fails
                +"  //@ requires false;\n"
                +"  public static boolean bf(boolean bb) { return true; }\n"
                +"  //@ requires true;\n"
                +"  public static boolean bt(boolean bb) { return true; }\n"
                +"  static boolean b;\n"
                +"  //@ static invariant b;\n"
                +"  //@ requires !b;\n"
                +"  public static boolean bq(boolean bb) { return true; }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Invariant) in method <init>",10,
                "/tt/TestJava.java:10: warning: Associated declaration",24,
                "/tt/TestJava.java:6: warning: Invariants+Preconditions appear to be contradictory in method bf",25,
                "/tt/TestJava.java:12: warning: Invariants+Preconditions appear to be contradictory in method bq",25);
    }

    public void testJava() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static boolean bstatic;\n"
                +"  boolean binstance;\n"
                +"  boolean binstance2;\n"
                +"  /*@ non_null */ Object o;\n"
                +"  //@ ghost Object oo;\n"
                +"  //@static invariant bstatic;\n"
                +"  //@invariant binstance;\n"
                +"  //@initially binstance2;\n"
                +"  //@constraint binstance2 == \\old(binstance2);\n"
                +"  //@static constraint bstatic == \\old(bstatic);\n"
                +"  public static void main(/*@ non_null*/ String[] args) {  }\n"
                +"  //@ requires true;\n"
                +"  //@ ensures \\result;\n"
                +"  public static boolean b(boolean bb) { return true; }\n"
                +"  //@ requires false;\n"
                +"  //@ ensures true;\n"
                +"  public static int i(int ii) { return 0; }\n"
                +"  //@ requires ii == 10;\n"
                +"  //@ ensures true;\n"
                +"  public Object inst(int ii) { binstance = ii == 0; o = null; /*@ set oo = null;*/ return null; }\n"
                +"}",
                "/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Invariant) in method <init>",8,
                "/tt/TestJava.java:8: warning: Associated declaration",23,
                "/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Invariant) in method <init>",8,
                "/tt/TestJava.java:9: warning: Associated declaration",16,
                "/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Initially) in method <init>",8,
                "/tt/TestJava.java:10: warning: Associated declaration",16,
                "/tt/TestJava.java:19: warning: Invariants+Preconditions appear to be contradictory in method i",21,
                "/tt/TestJava.java:22: warning: The prover cannot establish an assertion (Invariant) in method inst",17,
                "/tt/TestJava.java:9: warning: Associated declaration",16
        );
    }

    public void testAssert() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert(boolean bb, boolean b) { /*@ assume b; */ /*@assert false;*/   }\n" // Should fail because of the explicit assert false
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert2(boolean bb, boolean b) { /*@ assume b; */ /*@assert !bb;*/   }\n" // Should fail because of the tautologically false assert
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassert3(boolean bb, boolean b) { /*@ assume bb; */ /*@assert b;*/   }\n" // Should fail because of the unprovable assert
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method bassert",75,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method bassert2",76,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method bassert3",77
        );
    }

    public void testAssume() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassumeBADASSUMP(boolean bb) { /*@assume false;*/  /*@ assert false; */ }\n" // Should succeed despite the false assert
                +"  //@ requires bbb;\n"
                +"  public static void bifOK(boolean bb,boolean b, boolean bbb) { /*@assume true;*/ if (bb) { /*@assume !b;*/ /*@ assert !bb; */ }  }\n"
                +"  //@ requires b;\n"
                +"  public static void bifBAD(boolean bb,boolean b) { /*@assume true;*/ if (bb) { /*@assume !b;*/ /*@ assert !bb; */ }  }\n"
                +"  //@ requires bb;\n"
                +"  //@ ensures true;\n"
                +"  public static void bassumeBADASSUMP2(boolean bb) { /*@assume false;*/  /*@ assert true; */ }\n" // Should succeed despite the false assert
                +"  public static void bassumeCHAIN1(boolean bb, boolean b) { if (bb) { /*@ assume !bb; assume bb;*/ b = true;  /* @ assert false; */ } }\n" 
                +"  public static void bassumeCHAIN2(boolean bb, boolean b) { if (bb) { /*@assume bb; assume !bb; */ b = true; /* @ assert false; */ } }\n" 
                +"  public static void bassumeMULT(boolean bb, boolean b) { if (bb) { /*@assume bb; assume !bb; */ b = true; /* @ assert false; */ } else { /*@assume bb; assume !bb; */ b = true; /* @ assert false; */} }\n" 
                +"  public TestJava() {}\n"
                +"}",
                "/tt/TestJava.java:5: warning: An assumption appears to be infeasible in method bassumeBADASSUMP(boolean)",56,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method bifOK",113,
                "/tt/TestJava.java:9: warning: An assumption appears to be infeasible in method bifBAD(boolean,boolean)",84,
                "/tt/TestJava.java:12: warning: An assumption appears to be infeasible in method bassumeBADASSUMP2(boolean)",57,
                "/tt/TestJava.java:13: warning: An assumption appears to be infeasible in method bassumeCHAIN1(boolean,boolean)",87,
                "/tt/TestJava.java:13: warning: An assumption appears to be infeasible in method bassumeCHAIN1(boolean,boolean)",75,
                "/tt/TestJava.java:14: warning: An assumption appears to be infeasible in method bassumeCHAIN2(boolean,boolean)",85,
                "/tt/TestJava.java:15: warning: An assumption appears to be infeasible in method bassumeMULT(boolean,boolean)",153,
                "/tt/TestJava.java:15: warning: An assumption appears to be infeasible in method bassumeMULT(boolean,boolean)",142,
                "/tt/TestJava.java:15: warning: An assumption appears to be infeasible in method bassumeMULT(boolean,boolean)",83
        );
    }

    public void testDeadBranch() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //static int ii;\n"
                +"  public static void bok(boolean b, int i) { if (b) i = 7; else i = 9; }\n" 
                +"  public static void bok2(boolean b, int i, int ii) { if (b) i = 7; else i = 9; if (b) ii = 7; else ii = 9; }\n" 
                +"  public static void bdead(boolean b, int i) { /*@ assume b; */ if (b) i = 7; else i = 9; }\n" 
                +"  public static void bdeadelse(boolean b, int i) { /*@ assume !b; */ if (b) i = 7; else i = 9; }\n" 
                +"}",
                "/tt/TestJava.java:6: warning: else branch apparently never taken in method bdead(boolean,int)", 69,
                "/tt/TestJava.java:7: warning: then branch apparently never taken in method bdeadelse(boolean,int)", 73
        );
    }

    public void testDecl() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void bok() { int k = 0; /*@ assert k == 0; */ }\n" 
                +"  public static void bfalse() { int k = 0; /*@ assert k != 0; */ }\n" 
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method bfalse",48
        );
    }

    public void testIncarnations() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void bnotok() { int k = 10; int i = 0; i = 1; i = k; k = 5; k = i+k; /*@ assert i == 10; assert k == 16; */}\n" // We want to be sure it fails
                +"  public static void bifok(boolean b) { int k = 10; if (b) { k = k+1; if (b) k = k-1; else k = k+1; } else { k=k-1; if (b) k=k-1; else k=k+1; } /*@ assert k == 10; */}\n"
                +"  public static void bifbad(boolean b) { int k = 10; if (b) { k = k+1; if (b) k = k-1; else k = k+1; } else { k=k-1; if (b) k=k-1; else k=k+1; } /*@ assert k == 11; */}\n" // We want to be sure it fails
                +"  public static void bifbad2(boolean b) { int k = 10; if (b) { k = k+1; if (!b) k = k+1; } else { k=k-1; if (b) {k=k-1; b = false; } } /*@ assert k == 11; */}\n" // We want to be sure it fails
                +"}",
                "/tt/TestJava.java:3: warning: The prover cannot establish an assertion (Assert) in method bnotok",106,
                "/tt/TestJava.java:4: warning: then branch apparently never taken in method bifok(boolean)", 120,
                "/tt/TestJava.java:4: warning: else branch apparently never taken in method bifok(boolean)", 75,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method bifbad",150,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method bifbad2",140
        );
    }

    public void testOld() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                +"  //@ static constraint i > \\old(i);\n"
                +"  //@ modifies i;\n"
                +"  //@ ensures i == \\old(i)+1;\n"
                +"  public static void bok() { i = i - 1; }\n"
                +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method bok",22,
                "/tt/TestJava.java:6: warning: Associated declaration", 15,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Constraint) in method bok",22,
                "/tt/TestJava.java:4: warning: Associated declaration", 25
        );
    }

    public void testOld2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                +"  //@ modifies i;\n"
                +"  //@ ensures i == \\old(i)+2;\n"
                +"  public static void bok() { i = i + 1; i = i + 1;}\n"
                +"  //@ modifies i;\n"
                +"  //@ ensures i == \\old(i+1);\n"
                +"  public static void bbad() { i = i - 1; }\n"
                +"}",
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method bbad",22,
                "/tt/TestJava.java:8: warning: Associated declaration", 15
        );
    }

    public void testReturn() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires 0<=ii && ii <=3;\n"
                +"  //@ ensures ii<=0 ==> \\result ==-ii;\n"
                +"  public static int bok(int ii) { if (ii==1) return -1; else if (ii==2) return -2; else if (ii==3) return -3; return 0; }\n"
                +"  //@ ensures \\result == -ii;\n"
                +"  public static int bbad(int ii) { if (ii==1) return -1; else if (ii==2) return -2; else if (ii==3) return -3; return 0; }\n"
                +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method bbad",21,
                "/tt/TestJava.java:6: warning: Associated declaration",15
        );
    }

    public void testThrow() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void bok(int i) { if (i == 0) throw new RuntimeException(); /*@ assert i!=0; */ }\n"
                +"  public static void bbad(int i) { if (i == 0) throw new RuntimeException(); /*@ assert i==0; */ }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method bbad",82
        );
    }

    public void testNonNull() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  //@ requires ii == 10;\n"
                +"  //@ ensures true;\n"
                +"  public /*@ non_null */Object inst(int ii) { return null; }\n"
                +"  //@ requires ii == 10;\n"
                +"  //@ ensures true;\n"
                +"  public @NonNull Object inst2(int ii) {  return null; }\n"
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method inst",32,
                "/tt/TestJava.java:5: warning: Associated declaration",14,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method inst2",26,
                "/tt/TestJava.java:8: warning: Associated declaration",10
        );
    }

    public void testNonNullParam() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  //@ ensures \\result != null;\n"
                +"  public Object inst(boolean b, /*@ non_null */Object i, Object ii) { return i; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public Object instbad(boolean b, /*@ non_null */Object i, Object ii) { return ii; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public Object inst2(boolean b, @NonNull Object i, Object ii) { return i; }\n"
                +"  //@ ensures \\result != null;\n"
                +"  public Object inst2bad(boolean b, @NonNull Object i, Object ii) { return ii; }\n"
                +"}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method instbad",17,
                "/tt/TestJava.java:5: warning: Associated declaration",15,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method inst2bad", 17,
                "/tt/TestJava.java:9: warning: Associated declaration",15
        );
    }

    public void testMethodCall() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  static public int j;\n"
                +"  //@ requires i>0;\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures j == -i;\n"
                +"  static public void m(int i) { j = -i; }\n"
                +"  //@ requires i>1; \n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == -i;\n"
                +"  public int inst(boolean b, int i) { m(i); return j; }\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == j;\n"
                +"  public int instbad(boolean b, int i) { m(i); return j; }\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == i;\n"
                +"  public int instbad2(boolean b, int i) { m(1); return j; }\n"
                +"}",
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Postcondition) in method instbad",14,
                "/tt/TestJava.java:13: warning: Associated declaration",15,
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Precondition) in method instbad",43,
                "/tt/TestJava.java:4: warning: Associated declaration",16,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Postcondition) in method instbad2",14,
                "/tt/TestJava.java:16: warning: Associated declaration",15
        );
    }

    public void testMethodCall2() { // Had problems with static and non-static
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public int j;\n"
                +"  //@ requires i>0;\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures j == -i;\n"
                +"  public void m(int i) { j = -i; }\n"
                +"  //@ requires i>1; \n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == -i;\n"
                +"  public int inst(boolean b, int i) { m(i); return j; }\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == j;\n"
                +"  public int instbad(boolean b, int i) { m(i); return j; }\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == i;\n"
                +"  public int instbad2(boolean b, int i) { m(1); return j; }\n"
                +"}",
                //"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Postcondition) in method instbad",14,
                //"/tt/TestJava.java:13: warning: Associated declaration",15,
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Precondition) in method instbad",43,
                "/tt/TestJava.java:4: warning: Associated declaration",16,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Postcondition) in method instbad2",14,
                "/tt/TestJava.java:16: warning: Associated declaration",15
        );
    }

    public void testMethodCallRet() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  static public int j;\n"
                +"  //@ requires i>0;\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures j == i+1 && \\result == j;\n"
                +"  static public int m(int i) { j = i+1; return j; }\n"
                +"  //@ requires i>1; \n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == \\old(i)+1;\n"
                +"  public int inst(boolean b, int i) { m(i); m(i); m(i); return j; }\n"
                +"  //@ requires i>1; \n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == \\old(i)+3;\n"
                +"  public int inst2(boolean b, int i) { m(m(m(i))); return j; }\n"
                +"}"
        );
    }

    public void testMethodCallThis() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  static TestJava o;\n"
                +"  static TestJava p;\n"
                +"  public int j;\n"
                +"  //@ ensures \\result == j;\n"
                +"  public int m() { return j; }\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == j;\n"
                +"  public int n() { return j; }\n"
                +"  //@ requires o!=null && p != null && o.j == 1 && p.j == 2 && j == 3;"
                +"  //@ ensures \\result == 6;\n"
                +"  public int inst() { return o.m() + p.m() + j; }\n"
                +"  //@ requires o!=null && p != null && o.j == 1 && p.j == 2 && j == 3;"
                +"  //@ modifies j;\n"
                +"  //@ ensures \\result == 6;\n"
                +"  public int instbad() { return o.n() + p.n() + j; }\n"
                +"}",
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Postcondition) in method instbad",14,
                "/tt/TestJava.java:14: warning: Associated declaration",15
        );
    }

    // FIXME  need tests for for loops
    // FIXME need tests for do loops

    // FIXME - more tests needed, and with specs
    // FIXME - need a loop invariant to prove this
    public void _testForeachSpecs() { 
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst(int[] a) { \n"
                +"    //@ assume a.length > 2 && a[0] == 1;\n"
                +"    for(int i: a) a[i] = 0; \n"
                +"    //@ assert a[1] == 0;\n"
                +"  }\n"
                +"}"
        );
    }

    public void testForLoopSpecs() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst() { int n = 0; /*@ loop_invariant 0<=i && i<=5 && n==i; decreases 5-i; */ for (int i=0; i<5; i++) n++; /*@ assert n == 5; */ }\n"
                +"  public void instb() { int n = 0; /*@ loop_invariant 0<=i && i<=5 && n==i; decreases 3-i; */ for (int i=0; i<5; i++) n++; /*@ assert n == 5; */ }\n"
                +"  public void instc() { int n = 0; /*@ loop_invariant 0<=i && i<5 && n==i; decreases 5-i; */ for (int i=0; i<5; i++) n++; /*@ assert n == 5; */ }\n"
                +"  public void instd() { int n = 0; /*@ loop_invariant 0<=i && i<=5 && n==i-1; decreases 5-i; */ for (int i=0; i<5; i++) n++; /*@ assert n == 5; */ }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreasesNotPositive) in method instb",119,
                "/tt/TestJava.java:4: warning: Associated declaration",77,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (LoopInvariant) in method instc",118,
                "/tt/TestJava.java:5: warning: Associated declaration",40,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (LoopInvariant) in method instd",97,
                "/tt/TestJava.java:6: warning: Associated declaration",40,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (LoopInvariant) in method instd",122,
                "/tt/TestJava.java:6: warning: Associated declaration",40
        );
    }

    public void _testDoWhileSpecs() { // FIXME - figure out this better
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst() { int i = 5; /*@ loop_invariant i>0; decreases i; */ do { i = i-1; } while (i>0); /*@ assert i == 0; */ }\n"
                +"  public void instb() { int i = 5; /*@ loop_invariant i>=0; decreases i-2; */ do  i = i+1;  while (i>0); /*@ assert i == 0; */ }\n"
                +"  public void instc() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ do { i = i+1; } while (i>0); /*@ assert i == 0; */ }\n"
                +"  public void instd() { int i = 5; /*@ loop_invariant i>0; decreases i; */ do { i = i-1; } while (i>0); /*@ assert i == 0; */ }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopInvariant) in method instb",91, // This presumably an effect of the 
                "/tt/TestJava.java:4: warning: Associated declaration",40,
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreasesNotPositive) in method instb",91,
                "/tt/TestJava.java:4: warning: Associated declaration",61,
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method instb",108,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (LoopDecreases) in method instc",89,
                "/tt/TestJava.java:5: warning: Associated declaration",61,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method instc",106,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (LoopInvariant) in method instd",88,
                "/tt/TestJava.java:6: warning: Associated declaration",40,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method instd",105
        );
    }

    public void testWhileSpecs() { 
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                +"  public void instb() { int i = 5; /*@ loop_invariant i>=0; decreases i-2; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                +"  public void instc() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ while (i>0) { i = i+1; } /*@ assert i == 0; */ }\n"
                +"  public void instd() { int i = 5; /*@ loop_invariant i>0; decreases i; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                +"}",
//                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopInvariant) in method instb",91, // This presumably an effect of the 
//                "/tt/TestJava.java:4: warning: Associated declaration",40,
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreasesNotPositive) in method instb",91,
                "/tt/TestJava.java:4: warning: Associated declaration",61,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (LoopDecreases) in method instc",89,
                "/tt/TestJava.java:5: warning: Associated declaration",61,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (LoopInvariant) in method instd",88,
                "/tt/TestJava.java:6: warning: Associated declaration",40
        );
    }

    // FIXME - need to sort out loop invariants for while loops with side effects
    //    public void testWhileSpecs2() {
    //        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
    //                +"public class TestJava { \n"
    //                +"  public void inst() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ while (--i > 0) { } /*@ assert i == 0; */ }\n"
    //                +"  public void instb() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ while (i-- >0) { } /*@ assert i == 0; */ }\n"
    //                              +"}",
    //                 "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreasesNotPositive) in method instb",91,
    //                 "/tt/TestJava.java:4: warning: Associated declaration",71,
    //                 "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method instb", 108
    //                );
    //    }

    public void testIncDec() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1() { int i = 5; i++; /*@ assert i == 6; */ }\n"
                +"  public void inst1b() { int i = 5; i++; /*@ assert i == 5; */ }\n"
                +"  public void inst2() { int i = 5; i--; /*@ assert i == 4; */ }\n"
                +"  public void inst2b() { int i = 5; i--; /*@ assert i == 5; */ }\n"
                +"  public void inst3() { int i = 5; ++i; /*@ assert i == 6; */ }\n"
                +"  public void inst3b() { int i = 5; ++i; /*@ assert i == 5; */ }\n"
                +"  public void inst4() { int i = 5; --i; /*@ assert i == 4; */ }\n"
                +"  public void inst4b() { int i = 5; --i; /*@ assert i == 5; */ }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1b",46,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst2b",46,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst3b",46,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst4b",46
        );
    }

    public void testIncDec2() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1() { int i = 5; int j = i++; /*@ assert j == 5; */ }\n"
                +"  public void inst1b() { int i = 5; int j = i++; /*@ assert j == 6; */ }\n"
                +"  public void inst2() { int i = 5; int j = i--; /*@ assert j == 5; */ }\n"
                +"  public void inst2b() { int i = 5; int j = i--; /*@ assert j == 4; */ }\n"
                +"  public void inst3() { int i = 5; int j = ++i; /*@ assert j == 6; */ }\n"
                +"  public void inst3b() { int i = 5; int j = ++i; /*@ assert j == 5; */ }\n"
                +"  public void inst4() { int i = 5; int j = --i; /*@ assert j == 4; */ }\n"
                +"  public void inst4b() { int i = 5; int j = --i; /*@ assert j == 5; */ }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1b",54,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst2b",54,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst3b",54,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst4b",54
        );
    }

    public void testAssignOp() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1() { int i = 5; i+=7; /*@ assert i == 12; */ }\n"
                +"  public void inst1b() { int i = 5; i+=7; /*@ assert i == 5; */ }\n"
                +"  public void inst1c() { int i = 5; int j = (i+=7); /*@ assert i == 12 && i == j; */ }\n"
                +"  public void inst1d() { int i = 5; int j = (i+=7); /*@ assert i == 5; */ }\n"
                +"  public void inst2() { int i = 5; i-=7; /*@ assert i == -2; */ }\n"
                +"  public void inst2b() { int i = 5; i-=7; /*@ assert i == 5; */ }\n"
                +"  public void inst2c() { int i = 5; int j = (i-=7); /*@ assert i == -2 && i == j; */ }\n"
                +"  public void inst2d() { int i = 5; int j = (i-=7); /*@ assert i == 5; */ }\n"
                +"  public void inst3() { int i = 5; i*=7; /*@ assert i == 5*7; */ }\n"
                +"  public void inst3b() { int i = 5; i*=7; /*@ assert i == 5; */ }\n"
                +"  public void inst3c() { int i = 5; int j = (i*=7); /*@ assert i == 5*7 && i == j; */ }\n"
                +"  public void inst3d() { int i = 5; int j = (i*=7); /*@ assert i == 5; */ }\n"
                +"  public void inst4() { int i = 5; i/=7; /*@ assert i == 5/7; */ }\n"
                +"  public void inst4b() { int i = 5; i/=7; /*@ assert i == 5; */ }\n"
                +"  public void inst4c() { int i = 5; int j = (i/=7); /*@ assert i == 5/7 && i == j; */ }\n"
                +"  public void inst4d() { int i = 5; int j = (i/=7); /*@ assert i == 5; */ }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1b",47,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst1d",57,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst2b",47,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst2d",57,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method inst3b",47,
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method inst3d",57,
                "/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Assert) in method inst4b",47,
                "/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Assert) in method inst4d",57
        ); // FIXME - not getting errors for / ; need %= <<= >>= >>>= &= |= ^=
    }

    public void testConditional() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1(int i) { int j = i<0?-i:i; /*@ assert j >= 0; */ }\n"
                +"  public void inst1a(int i) { int j = i<0?-i:i; /*@ assert j == -1; */ }\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1a",53
        );
    }

    public void testLbl() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1(int i) { /*@ assume i > 0; */ /*@ assert (\\lblpos ISP i>0); */}\n" // no report
                +"  public void inst1a(int i) { /*@ assume i > 0; */ /*@ assert (\\lblneg ISN i<0); */}\n" // reported
                +"  public void inst1b(int i) { /*@ assume i > 0; */ /*@ assert !(\\lblneg ISN2 i>0); */}\n" // no report
                +"  public void inst1c(int i) { /*@ assume i > 0; */ /*@ assert (\\lblpos ISP i<0); */}\n" // no report
                +"  public void inst1d(int i) { /*@ assume i > 0; */ /*@ assert !(\\lblpos ISP2 i>0); */}\n" // reported
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1a",56,
                "/tt/TestJava.java:4: warning: Label ISN reported",64,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method inst1b",56,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst1c",56,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst1d",56,
                "/tt/TestJava.java:7: warning: Label ISP2 reported",65
        );
    }

    public void testNewObject() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1() { Object o = new Object(); Object oo = new Object(); /*@ assert o != oo;*/ }\n" 
                +"  public void inst1a() { Object o = new Object(); Object oo = new Object(); /*@ assert o == oo;*/ }\n" 
                +"  public void inst2() { Object o = new Object(); /*@ assert o != null;*/ }\n" 
                +"  public void inst2a() { Object o = new Object(); /*@ assert o == null;*/ }\n" 
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1a",81,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst2a",55
        );
    }

    public void testNewArray() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1() { Object o = new int[5]; Object oo = new int[5]; /*@ assert o != oo;*/ }\n" 
                +"  public void inst1a() { Object o = new int[5]; Object oo = new int[5]; /*@ assert o == oo;*/ }\n" // FALSE
                +"  public void inst2() { int[] o = new int[5]; /*@ assert o != null; assert o.length == 5; */ }\n" 
                +"  public void inst2a() { int[] o = new int[5]; /*@ assert o.length == 6;*/ }\n"  // FALSE
                +"  public void inst3(/*@non_null*/int[] a) { /*@ assert a.length >= 0;*/ }\n" 
                +"  public void inst4() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 3; assert o[1] == 11;*/ }\n" 
                +"  public void inst4a() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 4; */ }\n"  // FALSE
                +"  public void inst4b() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 3; assert o[1] == 10;*/ }\n"  // FALSE
                +"  public void inst5() { Object o = new boolean[5]; Object oo = new boolean[5]; /*@ assert o != oo;*/ }\n" 
                +"  public void inst5a() { Object o = new boolean[5]; Object oo = new boolean[5]; /*@ assert o == oo;*/ }\n" // FALSE
                +"  public void inst6() { int[] o = {10,11,12}; /*@ assert o != null; assert o.length == 3; assert o[1] == 11;*/ }\n" 
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1a",77,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst2a",52,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method inst4a",61,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst4b",83,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method inst5a",85
        );
    }

    public void testNewArrayMD() { 
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst0() { Object o = new int[2][3]; o = new int[2][]; o = new int[][] {{2}, {3,4,5}}; int[][] oo = {{1},{2,3}}; /*@ assert oo[0] != oo[1]; */}\n" 
                +"  public void inst1() { Object o = new int[5][3]; Object oo = new int[5][3]; /*@ assert o != oo;*/ }\n" 
                +"  public void inst1a() { Object o = new int[5][3]; Object oo = new int[5][3]; /*@ assert o == oo;*/ }\n" // FALSE
                +"  public void inst2() { int[][] o = new int[5][3]; /*@ assert o.length == 5; assert o[1].length == 3; */ }\n" 
                +"  public void inst2a() { int[][] o = new int[5][3]; /*@ assert o.length == 6;*/ }\n" // FALSE
                +"  public void inst2b() { int[][] o = new int[5][3]; /*@ assert o[1].length == 4;*/ }\n" // FALSE
                +"  public void inst3(/*@non_null*/int[][] a) { /*@ assert a.length >= 0;*/ }\n" 
                +"  public void inst4() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o.length == 3; */ }\n" 
                +"  public void inst4a() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o.length == 2; */ }\n"  // FALSE
                +"  public void inst5() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[1][2] == 14; */ }\n" 
                +"  public void inst6() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[2].length == 1; */ }\n" 
                +"  public void inst7() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[0].length == 2; */ }\n" 
                +"  public void inst8() { int[][] o = new int[5][]; /*@ assert o != null; assert o.length == 5; assert o[1] == null; */ }\n" 
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method inst1a",83
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst2a",57
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst2b",57
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method inst4a",80
        );
    }

    public void testArrays() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst2(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  /*@ assert a[1] == 2; */ }\n" // OK
                +"  public void inst2a(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  /*@ assert a[1] == 3; */ }\n" // BAD
                +"  public void inst3(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */ }\n" // OK
                +"  public void inst3a(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 4; */ }\n" // BAD
                +"  public void inst4(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[0] == 2; */  a[1] = 3; /*@ assert a[0] == 2; */ }\n" // OK
                +"  public void inst4a(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[0] == 2; */  a[1] = 3; /*@ assert a[0] == 4; */ }\n" // BAD
                +"  public void inst5(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */  a[1] = 4; /*@ assert a[1] == 4; */}\n" // OK
                +"  public void inst5a(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */  a[1] = 4; /*@ assert a[1] == 5; */}\n" // BAD
                +"  public void inst6(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] == b[0]; */}\n" // OK
                +"  public void inst6a(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] != b[0]; */}\n" // BAD
                +"  public void inst7(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@ assume b.length == 10 && a.length == 10;*/ b[0] = 0; b = a; a[0] = 7; /*@ assert b[0] == 7; */}\n" // OK
                +"  public void inst7a(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@ assume b.length == 10 && a.length == 10;*/  b[0] = 0; b = a; a[0] = 7; /*@ assert b[0] == 8; */}\n" // BAD
                +"  public void inst8(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@ assume b.length == 10 && a.length == 12;*/ b = a; a[0] = 5; /*@ assert b != null; assert a != null; assert b.length == 12; assert a.length == 12; */}\n" // BAD
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst2a",103,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst3a",113,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst4a",113,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst5a",149,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method inst6a",106,
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method inst7a",147
        );
    }
    
    public void testArraysMD() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst2(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  /*@ assert a[1][2]; */ }\n" // OK
                +"  public void inst2a(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  /*@ assert !a[1][2]; */ }\n" // BAD
                +"  public void inst3(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  a[1][2] = false; /*@ assert !a[1][2]; */ }\n" // OK
                +"  public void inst3a(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  a[1][2] = false; /*@ assert a[1][3]; */ }\n" // BAD
                +"  public void inst3b(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  a[1][2] = false; /*@ assert a[0][2]; */ }\n" // BAD
                +"  public void inst4(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[0] != null; assume a[1].length == 5; assume a[0].length == 3; *//*@ assume a[0][0]; */  a[1][0] = false; /*@ assert a[0][0]; */ }\n" // OK
                +"  public void inst4a(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[0] != null; assume a[1].length == 5; assume a[0].length == 3; *//*@ assume a[0][0]; */  a[1][0] = false; /*@ assert !a[0][0]; */ }\n" // BAD
                +"  public void inst5(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; */  a[0] = a[1]; /*@ assert a[0][3] == a[1][3]; */}\n" // OK
                +"  public void inst5a(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; */ a[0] = a[1]; /*@ assert a[0][3] != a[1][3]; ; */}\n" // BAD
                +"  public void inst6(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] == b[0]; */}\n" // OK
                +"  public void inst6a(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] != b[0]; */}\n" // BAD
                +"  public void inst7(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@ assume b.length == 10 && a.length == 10 && b[0] != null && a[0] != null && b[0].length == 5 && a[0].length==6;*/ b[0][0] = true; b = a; a[0][0] = false; /*@ assert !b[0][0]; */}\n" // OK
                +"  public void inst7a(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@ assume b.length == 10 && a.length == 10 && b[0] != null && a[0] != null && b[0].length == 5 && a[0].length==6;*/  b[0][0] = true; b = a; a[0][0] = false; /*@ assert b[0][0]; */}\n" // BAD
                +"  public void inst8(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@ assume b.length == 10 && a.length == 12;*/ b = a; a[0] = null; /*@ assert b != null; assert a != null; assert b.length == 12; assert a.length == 12; */}\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst2a",154
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst3a",171
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst3b",171
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method inst4a",217
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method inst5a",144
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method inst6a",118
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method inst7a",242
        );
    }
    
    public void testFields() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  int f; static int sf;\n"
                +"  int g; static int sg;\n"
                +"  static TestJava t;  //@ invariant t != null; \n"
                +"  public void inst2(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  /*@ assert t.f == 2; */ }\n" // OK
                +"  public void inst2a(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  /*@ assert t.f == 3; */ }\n" // BAD
                +"  public void inst3(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */ }\n" // OK
                +"  public void inst3a(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 4; */ }\n" // BAD
                +"  public void inst4(/*@non_null*/int[] a) { /*@ assume t.g == 2; */  t.f = 3; /*@ assert t.g == 2; */ }\n" // OK
                +"  public void inst4a(/*@non_null*/int[] a) { /*@ assume t.g == 2; */  t.f = 3; /*@ assert t.g == 4; */ }\n" // BAD
                +"  public void inst5(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */  t.f = 4; /*@ assert t.f == 4; */}\n" // OK
                +"  public void inst5a(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */  t.f = 4; /*@ assert t.f == 5; */}\n" // BAD
                +"  public void inst6(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b = a; /*@ assert a.f == b.f; */}\n" // OK
                +"  public void inst6a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b = a; /*@ assert a.f != b.f; */}\n" // BAD
                +"  public void inst7(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b.f = 0; b = a; a.f = 7; /*@ assert b.f == 7; */}\n" // OK
                +"  public void inst7a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b.f = 0; b = a; a.f = 7; /*@ assert b.f == 8; */}\n" // BAD
                +"  public void inst8(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { /*@ assert a.sf == b.sf; */}\n" // OK
                +"  public void inst8a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { /*@ assert a.sf != b.sf; */}\n" // BAD
                +"  public void inst9(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { a.sf = 3; /*@ assert 3 == b.sf; */}\n" // OK
                +"  public void inst9a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { a.sf = 3; /*@ assert 3 != b.sf; */}\n" // BAD
                +"  public void inst10(/*@non_null*/TestJava a) { /*@ assert f == this.f; */ /*@ assert a == this ==> a.f == f; */}\n" // OK
                +"  public void inst10a(/*@non_null*/TestJava a) { /*@ assert f == this.f; */ /*@ assert a.f == f; */}\n" // BAD
                +"  public void inst11(/*@non_null*/TestJava a) { /*@ assert sf == this.sf; */ /*@ assert a.sf == sf; */}\n" // OK
                +"}",
                "/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Invariant) in method <init>",8,
                "/tt/TestJava.java:5: warning: Associated declaration",37,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst2a",75,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method inst3a",84,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method inst4a",84,
                "/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method inst5a",118,
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method inst6a",85,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method inst7a",103,
                "/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Assert) in method inst8a",78,
                "/tt/TestJava.java:21: warning: The prover cannot establish an assertion (Assert) in method inst9a",88,
                "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Assert) in method inst10a",81
        );
    }

    public void testSwitch() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  int f; static int sf;\n"
                +"  int g; static int sg;\n"
                +"  static TestJava t;\n"
                +"  public void inst1(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; break; case 2: j = 2; } /*@ assert j!=0; */ }\n" // OK
                +"  public void inst1a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; break; case 2: j = 2; } /*@ assert j==1; */ }\n" // BAD
                +"  public void inst2(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; case 2: j = 2; } /*@ assert j>0; */ }\n" // OK
                +"  public void inst2a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; case 2: j = 2; } /*@ assert i==0 ==> j==-1; */ }\n" // BAD
                +"  public void inst3(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {default: i=4; } break; default: j=-1; case 2: j = 2; } /*@ assert j>0; */ }\n" // OK
                +"  public void inst3a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {default: i=4; } break; default: j=-1; break; case 2: j = 2; } /*@ assert j>0; */ }\n" // OK
                +"  public void inst4(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {} break; default: j=-1; case 2: j = 2; } /*@ assert j>=0; */ }\n" // OK
                +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst1a",148,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method inst2a",141,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method inst3a",170
        );
    }

    public void testTry() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                +"  //@ ensures i == 2;\n"
                +"  public void inst1() { i=0; try { i = 1; return; } finally { i = 2; } }\n" // OK
                +"  //@ ensures i == 1;\n"
                +"  public void inst1a() { i=0; try { i = 1; return; } finally { i = 2; } }\n" // BAD
                +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method inst1a",15, // FIXME - really ought to point to the return or finally statement
                "/tt/TestJava.java:6: warning: Associated declaration",15
        );
    }


    public void testMisc() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                +"  //@ requires i > 0;\n"
                +"  //@ ensures i > 0;\n"
                +"  public static void m() { i = i -1; }\n" // OK
                +"}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m",22,
                "/tt/TestJava.java:5: warning: Associated declaration",15
        );
    }

    public void testArith() {  // FIXME - need more arithmetic support
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public static void m1(int a, int b) { /*@ assert a*2 == a + a; */ }\n"
                //+"  public static void m2(int a, int b) { /*@ assert a * b == a *(b-1) + a; */ }\n"
                +"  public static void m3(int a, int b) { /*@ assert (2*a)/2 == a; */ }\n"
                +"  public static void m4(int a, int b) { /*@ assert a >= 0 ==> (a%3) < 3; */ }\n"
                +"  public static void m5(int a, int b) { /*@ assert a >= 0 ==> (a%3) >= 0; */ }\n"
                //+"  public static void m6(int a, int b) { /*@ assert (a >= 0 && b > 0) ==> (a%b) >= 0; */ }\n"
                //+"  public static void m7(int a, int b) { /*@ assert (a >= 0 && b > 0) ==> ((a*b)%b) == 0; */ }\n"
                +"  public static void m8(int a, int b) { /*@ assert (a >= 0 ) ==> ((5*a)%5) == 0; */ }\n"
                +"}"
        );
    }

    public void testPureMethodStatic() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  //@ ensures \\result == i+1;\n"
                +"  //@ pure \n"
                +"  public static int m(int i) { return i+1; }\n"
                +"  public static void m1(int a, int b) { int k = a+1; /*@ assert k == m(a); */ }\n"
                +"  public static void m1a(int a, int b) { int k = a+2; /*@ assert k == m(a); */ }\n"
                +"  public static void m2(int a, int b) { int k = 2*a+2; /*@ assert k == m(a) + m(a); */ }\n"
                +"  public static void m2a(int a, int b) { int k = 2*a+2; /*@ assert k == 1 + m(a) + m(a); */ }\n"
                +"  public static void m3(int a, int b) { int k = a+3; /*@ assert k == m(m(a+1)); */ }\n"
                +"  public static void m3a(int a, int b) { int k = a+2; /*@ assert k == m(m(a+1)); */ }\n"
                +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m1a",59,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m2a",61,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method m3a",59
        );
    }

    public void testPureMethod() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  //@ ensures \\result == i+1;\n"
                +"  //@ pure \n"
                +"  public int m(int i) { return i+1; }\n"
                +"  public void m1(int a, int b) { int k = a+1; /*@ assert k == m(a); */ }\n"
                +"  public void m1a(int a, int b) { int k = a+2; /*@ assert k == m(a); */ }\n"
                +"  public void m2(int a, int b) { int k = 2*a+2; /*@ assert k == m(a) + m(a); */ }\n"
                +"  public void m2a(int a, int b) { int k = 2*a+2; /*@ assert k == 1 + m(a) + m(a); */ }\n"
                +"  public void m3(int a, int b) { int k = a+3; /*@ assert k == m(m(a+1)); */ }\n"
                +"  public void m3a(int a, int b) { int k = a+2; /*@ assert k == m(m(a+1)); */ }\n"
                +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m1a",52,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m2a",54,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method m3a",52
        );
    }

    public void testPureNonFunction() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  int z;\n"
                +"  //@ ensures \\result == z+1;\n"
                +"  //@ pure \n"
                +"  public int m() { return z+1; }\n"
                +"  public void m1(int a, int b) { int k = z+1; /*@ assert k == m(); */ }\n"
                +"  public void m1a(int a, int b) { int k = z+2; /*@ assert k == m(); */ }\n"
                +"  public void m2(int a, int b) { int k = 2*z+2; /*@ assert k == m() + m(); */ }\n"
                +"  public void m2a(int a, int b) { int k = 2*z+2; /*@ assert k == 1 + m() + m(); */ }\n"
                +"  public void m3(int a, int b) { z = 7; int k = z+1; /*@ assert k == m(); */ }\n"
                +"  public void m3a(int a, int b) { z = 7; int k = z+2; /*@ assert k == m(); */ }\n"
                +"}",
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m1a",52,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m2a",54,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method m3a",59
        );
    }

    public void testPureNoArguments() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  static int z;\n"
                +"  //@ ensures \\result == z+1;\n"
                +"  //@ pure \n"
                +"  public static int m() { return z+1; }\n"
                +"  public void m1(int a, int b) { int k = z+1; /*@ assert k == m(); */ }\n"
                +"  public void m1a(int a, int b) { int k = z+2; /*@ assert k == m(); */ }\n"
                +"  public void m2(int a, int b) { int k = 2*z+2; /*@ assert k == m() + m(); */ }\n"
                +"  public void m2a(int a, int b) { int k = 2*z+2; /*@ assert k == 1 + m() + m(); */ }\n"
                +"}",
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m1a",52,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m2a",54
        );
    }

    public void testInheritedPost() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"abstract public class TestJavaA { \n"
                +"  //@ requires iii > 0;\n"
                +"  //@ ensures \\result > 0;\n"
                +"  abstract public int m(int iii);\n"
                +"}\n"
                +"abstract public class TestJavaB extends TestJavaA { \n"
                +"  //@ also\n"
                +"  //@ ensures \\result > ii;\n"
                +"  abstract public int m(int ii);\n"
                +"}\n"
                +"public class TestJava extends TestJavaB { \n"
                +"  //@ also\n"
                +"  //@ ensures \\result == i+1;\n"
                +"  //@ pure\n"
                +"  public int m(int i) { return i+1; }\n"
                +"  //@ ensures \\result == a+1;\n"
                +"  public int m1(int a) { return m(a); }\n"
                +"  public int m1a(int a) { return m(-1); }\n"
                +"}"
        );
    }

    public void testInheritedPre() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"abstract public class TestJavaA { \n"
                +"  //@ requires iii == 1;\n"
                +"  //@ ensures \\result == iii;\n"
                +"  abstract public int m(int iii);\n"
                +"}\n"
                +"abstract public class TestJavaB extends TestJavaA { \n"
                +"  //@ also\n"
                +"  //@ requires ii == 2;\n"
                +"  //@ ensures \\result == ii;\n"
                +"  abstract public int m(int ii);\n"
                +"}\n"
                +"public class TestJava extends TestJavaB { \n"
                +"  //@ also\n"
                +"  //@ requires i == 3;\n"
                +"  //@ ensures \\result == i;\n"
                +"  //@ pure\n"
                +"  public int m(int i) { return i; }\n"
                +"  //@ requires a >= 1 && a <= 3;\n"
                +"  //@ ensures \\result == a;\n"
                +"  public int m1(int a) { return m(a); }\n"
                +"  //@ ensures \\result == a;\n"
                +"  public int m1a(int a) { return m(-1); }\n"
                +"}",
                "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Postcondition) in method m1a",14,
                "/tt/TestJava.java:22: warning: Associated declaration",15,
                "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Precondition) in method m1a",35,
                "/tt/TestJava.java:15: warning: Associated declaration",7
        );
    }

    public void testTrace() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires 0<=ii && ii <=3;\n"
                +"  //@ ensures \\result < 0;\n"
                +"  public static int m(int ii) { \n"
                +"    if (ii==1) return -1; \n"
                +"    if (ii==2) return -2; \n"
                +"    if (ii==3) return -3; \n"
                +"    ii = 7;\n"
                +"    return 0; }\n"
                +"  //@ requires ii == 2;\n"
                +"  //@ ensures \\result == 0;\n"
                +"  public static int mm(int ii) { \n"
                +"    if (ii==1) return -1; \n"
                +"    if (ii==2) return -2; \n"
                +"    if (ii==3) return -3; \n"
                +"    ii = 7;\n"
                +"    return 0; }\n"
                +"  public static int is;"
                +"  //@ ensures is == 6;\n"
                +"  public static int m3(int ii) { \n"
                +"    try { ii = 0; \n"
                +"      if (ii == 0) return -2; \n"
                +"    } finally { \n"
                +"      is = 7;\n"
                +"    }"
                +"    return 0; }\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public static int m4(int ii) { \n"
                +"    try { ii = 0; \n"
                +"      if (ii == 0) return -2; \n"
                +"    } finally { \n"
                +"      is = 7;\n"
                +"    }"
                +"    return 0; }\n"
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method m",21,
                "/tt/TestJava.java:4: warning: Associated declaration",15,
                "/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Postcondition) in method mm",21,
                "/tt/TestJava.java:12: warning: Associated declaration",15,
                "/tt/TestJava.java:20: warning: The prover cannot establish an assertion (Postcondition) in method m3",21,
                "/tt/TestJava.java:19: warning: Associated declaration",38,
                "/tt/TestJava.java:27: warning: The prover cannot establish an assertion (Postcondition) in method m4",21,
                "/tt/TestJava.java:26: warning: Associated declaration",15
        );
    }

    public void testForwardInit() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static int m() { \n"
                +"    int c = c+1; \n"
                +"    //@ assert c == 1; \n"
                +"    return c; \n"
                +"  }\n"
                +"}",
                "/tt/TestJava.java:4: variable c might not have been initialized",13
        );
    }

    public void testGhostVars() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static int m() { \n"
                +"    int c = 4; \n"
                +"    //@ ghost int d = c+1;\n"
                +"    //@ assert d + c == 9; \n"
                +"    return c; \n"
                +"  }\n"
                +"  public static int mm() { \n"
                +"    int c = 4; \n"
                +"    //@ ghost int d = c+1;\n"
                +"    //@ assert d + c == 10; \n"
                +"    return c; \n"
                +"  }\n"
                +"}",
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method mm",9
        );
    }

    public void testSetDebug() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static int m() { \n"
                +"    int c = 4; \n"
                +"    //@ ghost int d = c+1;\n"
                +"    //@ set d = 10;\n"
                +"    //@ assert d + c == 14; \n"
                +"    return c; \n"
                +"  }\n"
                +"  public static int mm() { \n"
                +"    int c = 4; \n"
                +"    //@ ghost int d = c+1;\n"
                +"    //@ set d = 10;\n"
                +"    //@ assert d + c == 15; \n"
                +"    return c; \n"
                +"  }\n"
                +"  public static int q() { \n"
                +"    int c = 4; \n"
                +"    //@ ghost int d = c+1;\n"
                +"    //@ debug d = 10;\n"
                +"    //@ assert d + c == 14; \n"
                +"    return c; \n"
                +"  }\n"
                +"  public static int qq() { \n"
                +"    int c = 4; \n"
                +"    //@ ghost int d = c+1;\n"
                +"    //@ debug d = 10;\n"
                +"    //@ assert d + c == 15; \n"
                +"    return c; \n"
                +"  }\n"
                +"}",
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method mm",9,
                "/tt/TestJava.java:28: warning: The prover cannot establish an assertion (Assert) in method qq",9
        );
    }

    /** Tests whether various ways of guarding a field reference are successful in
     * avoiding a failed assertion.
     */
    public void testUndefinedInJava() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j;\n"
                +"  public static void m(TestJava o) { \n"
                +"    int i = o.j; \n"
                +"  }\n"
                +"  public static void m1(/*@non_null*/ TestJava o) { \n"
                +"    int i = o.j; \n"
                +"  }\n"
                +"  //@ requires o != null;\n"
                +"  public static void m2(TestJava o) { \n"
                +"    int i = o.j; \n"
                +"  }\n"
                +"  public static void m3(TestJava o) { \n"
                +"    boolean i = o != null && o.j == 1; \n"
                +"  }\n"
                +"  public static void m4(TestJava o) { \n"
                +"    boolean i = o == null || o.j == 1; \n"
                +"  }\n"
                +"  public static void m5(TestJava o) { \n"
                +"    int i = ( o != null ? o.j : 6); \n"
                +"  }\n"
                +"  public static void m6(TestJava o) { \n"
                +"    int i = ( o == null ? 7 : o.j); \n"
                +"  }\n"
                +"  public static void m6a(TestJava o) { \n"
                +"    int i = ( o != null ? 7 : o.j); \n"
                +"  }\n"
                +"  //@ ensures \\result == (oo != null);\n"
                +"  public static boolean p(TestJava oo) { \n"
                +"    return oo != null; \n"
                +"  }\n"
                +"  public static void m7(TestJava o) { \n"
                +"    boolean i = p(o) && o.j == 0; \n"
                +"  }\n"
                +"  public static void m7a(TestJava o) { \n"
                +"    boolean i = p(o) || o.j == 0; \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m",14
                ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m6a",32
                ,"/tt/TestJava.java:37: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m7a",26
        );
    }
    /** Tests whether the various kinds of undefined constructs are actually detected.
     */  // FIXME - need a bad cast
    public void testUndefinedInJava2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j;\n"
                +"  public static void m(TestJava o) { \n"
                +"    int i = o.j; \n"
                +"  }\n  "
                +"  public static void m1(int[] a) { \n"
                +"    int i = a[0]; \n"
                +"  }\n"
                +"  //@ requires a != null;\n"
                +"  public static void m2(int[] a) { \n"
                +"    int i = a[-1]; \n"
                +"  }\n"
                +"  //@ requires a != null;\n"
                +"  public static void m3(int[] a) { \n"
                +"    //@ assume a.length == 1; \n"
                +"    int i = a[1]; \n"
                +"  }\n"
                +"  public static void m4(int i, int j) { \n"
                +"    int k = i/j; \n"
                +"  }\n"
                +"  public static void m5(int i, int j) { \n"
                +"    int k = i%j; \n"
                +"  }\n"
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m",14,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m1",14,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1",14,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m2",14,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m3",14,
                "/tt/TestJava.java:20: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m4",14,
                "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m5",14
        );
    }


    /** Tests whether various ways of guarding a field reference are successful in
     * avoiding a failed assertion.
     */
    public void testUndefinedInSpec() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j;\n"
                +"  public static void m(TestJava o) { \n"
                +"    //@ assume o.j == 1; \n"
                +"  }\n"
                +"  public static void m1(/*@non_null*/ TestJava o) { \n"
                +"    //@ assume o.j == 1; \n"
                +"  }\n"
                +"  //@ requires o != null;\n"
                +"  public static void m2(TestJava o) { \n"
                +"    //@ assume o.j == 1; \n"
                +"  }\n"
                +"  public static void m3(TestJava o) { \n"
                +"    //@ assume o != null && o.j == 1; \n"
                +"  }\n"
                +"  public static void m4(TestJava o) { \n"
                +"    //@ assume o == null || o.j == 1; \n"
                +"  }\n"
                +"  public static void m5(TestJava o) { \n"
                +"    //@ assume o != null ==> o.j == 1; \n"
                +"  }\n"
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m",17
        );
    }

    /** Tests whether the various kinds of undefined constructs are actually detected.
     */  // FIXME - need a bad cast, pure method violating preconditions
    public void testUndefinedInSpec2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j;\n"
                +"  public static void m(TestJava o) { \n"
                +"    //@ assume o.j == 1; \n"
                +"  }\n  "
                +"  public static void m1(int[] a) { \n"
                +"    //@ assume a[0] == 1; \n"
                +"  }\n"
                +"  //@ requires a != null;\n"
                +"  public static void m2(int[] a) { \n"
                +"    //@ assume a[-1] == 1; \n"
                +"  }\n"
                +"  //@ requires a != null;\n"
                +"  public static void m3(int[] a) { \n"
                +"    //@ assume a.length == 1; \n"
                +"    //@ assume a[1] == 1; \n"
                +"  }\n"
                +"  public static void m4(int i, int j) { \n"
                +"    //@ assume i/j == 4; \n"
                +"  }\n"
                +"  public static void m5(int i, int j) { \n"
                +"    //@ assume i%j == 4; \n"
                +"  }\n"
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m",17,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m1",17,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m1",17,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m2",17,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m3",17,
                "/tt/TestJava.java:20: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m4",17,
                "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m5",17
        );
    }

    /** Tests whether undefinedness is caught in various JML constructions */
    // FIXME - loop invariants, variants,  represents,  signals, modifies 
    // FIXME - old constructs, quantifications, set comprehension, pure methods - check other JMl expressions
    public void testUndefinedInSpec3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j = 1;\n"
                +"  static TestJava t;\n"
                +"  public static void m(TestJava o) { \n"
                +"    //@ assume o.j == 1; \n"
                +"  }\n  "
                +"  public static void m1(TestJava o) { \n"
                +"    //@ assert o.j == 1 ? true : true; \n"
                +"  }\n  "
                +"  public static void m2(TestJava o) { \n"
                +"    //@ ghost int i = o.j; \n"
                +"  }\n  "
                +"  public static void m3(TestJava o) { \n"
                +"    //@ ghost int i; debug i = o.j; \n"
                +"  }\n  "
                +"  //@ requires o.j == 1;\n"
                +"  public static void m4(TestJava o) { \n"
                +"  }\n  "
                +"  //@ ensures t.j == 1 ? true : true;\n"
                +"  public static void m5(TestJava o) { \n"
                +"  }\n  "
                +"  public static void m6(TestJava o) { \n"
                +"    //@ ghost int i; set i = o.j; \n"
                +"  }\n  "
                +"}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m",17,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m1",17,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m2",24,
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m3",33,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m4",19,
                "/tt/TestJava.java:20: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m5",18,
                "/tt/TestJava.java:24: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m6",31
        );   
    }
    /** Tests whether undefinedness is caught in various JML constructions */
    // FIXME - readable writable, represents, assertother clauses
    public void testUndefinedInSpec4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j = 1;\n"
                +"  static TestJava t;\n"
                +"  public void m(TestJava o) { \n"
                +"    //@ assume o.j == 1; \n"
                +"  }\n  "
                +"  //@ invariant t.j ==1;\n"
                +"}"
                ,"/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Invariant) in method <init>",8
                ,"/tt/TestJava.java:8: warning: Associated declaration",19
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m",17
        );
    }
    
    /** Check to catch undefinedness in an initially clause */
    public void testUndefinedInSpec4a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  boolean j = true;\n"
                +"  static TestJava t;\n"
                +"  public TestJava() { \n"
                +"  }\n  "
                +"  //@ initially t.j ? true : true;\n"
                +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (UndefinedNullReference) in method <init>",20  // FIXME - column position could be better
        );
    }

    /** Check to catch undefinedness in a constraint clause */
    public void testUndefinedInSpec4b() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j = 1;\n"
                +"  static TestJava t;\n"
                +"  public void m(TestJava o) { \n"
                +"  }\n  "
                +"  //@ constraint t.j ==1;\n"
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Constraint) in method m",15
                ,"/tt/TestJava.java:7: warning: Associated declaration",20
        );
    }

    /** Check to catch undefinedness in a axiom clause */
    public void testUndefinedInSpec4c() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int j = 1;\n"
                +"  static TestJava t;\n"
                +"  public void m(TestJava o) { \n"
                +"  }\n  "
                +"  // @ axiom (\\forall TestJava q;; q.j ==1);\n" // FIXME
                +"}"
        );
    }
    
    // FIXME
    public void _testUndefinedInSpec5() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static TestJava t;\n"
                +"  int j = t.j;\n"
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m2",19
        );
    }

    public void testUndefinedInJava6() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static TestJava t;\n"
                +"  int j = 1;\n"
                +"  public void m1(TestJava o) { \n"
                +"    int i = t.j; \n"
                +"  }\n  "
                +"  public void m2(TestJava o) { \n"
                +"    t.j = 1; \n"
                +"  }\n  "
                +"  public void m3(TestJava o) { \n"
                +"    t.j += 1; \n"
                +"  }\n  "
                +"  public void m4(TestJava o) { \n"
                +"    int i = 0; i += t.j; \n"
                +"  }\n  "
                +"  public void m5(TestJava o) { \n"
                +"    assert t.j == 1; \n"
                +"  }\n  "
                // FIXME
                // for, while, foreach, do, switch, case, if, throw, method call, index, conditional, 
                // annotation, binary, unary, conditional, new array, new class, return, synchronized
                +"}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m1",14,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m2",6,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m3",6,
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m4",22,
                "/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Assert) in method m5",12  // FIXME
        );
    }

    // FIXME - need tests within various Java constructs, including with short-circuits

    /** This test tests catch blocks */
    // FIXME - make sure this works once instanceof is implemented
    // FIXME - add more tests
    public void testCatch() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m() {\n"
                +"    int i = 0;\n"
                +"    try {\n"
                +"      throw new RuntimeException();\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    }\n"
                +"    //@ assert i == 1;\n"
                +"  }\n"
                +"  public void ma() {\n"
                +"    int i = 0;\n"
                +"    try {\n"
                +"      throw new RuntimeException();\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    }\n"
                +"    //@ assert i == 2;\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Assert) in method ma",9
                );
    }
    
    public void testCatch2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m() {\n"
                +"    int i = 0;\n"
                +"    try {\n"
                +"      throw new Exception();\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    }\n"
                +"    //@ assert i == 2;\n"
                +"  }\n"
                +"  public void mp() {\n"
                +"    int i = 0; int j = 0;\n"
                +"    try {\n"
                +"      throw new Exception();\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    } finally {\n"
                +"      j=3;\n"
                +"    }\n"
                +"    //@ assert i == 2 && j == 3;\n"
                +"  }\n"
                +"  public void ma() {\n"
                +"    int i = 0;\n"
                +"    try {\n"
                +"      throw new Exception();\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    }\n"
                +"    //@ assert i == 1;\n"
                +"  }\n"
                +"  public void m1(int k) {\n"
                +"    int i = 0; int j = 0; //@ assume k == 0; \n"
                +"    try {\n"
                +"      try {\n"
                +"         if (k == 0) throw new Exception();\n"
                +"      } finally {\n"
                +"         j = 50;\n"
                +"      }\n"
                +"      j = 60;\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    }\n"
                +"    //@ assert i == 2 && j == 50;\n"
                +"  }\n"
                +"  public void m11(int k) throws Exception {\n"
                +"    int i = 0; int j = 0; //@ assume k == 0; \n"
                +"    try {\n"
                +"    try {\n"
                +"      try {\n"
                +"         if (k == 0) throw new Exception();\n"
                +"      } finally {\n"
                +"         j = 50;\n"
                +"      }\n"
                +"      j = 60;\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } finally {\n"
                +"      i=2;\n"
                +"    }\n"
                +"    } finally {\n"
                +"    //@ assert i == 2 && j == 50;\n"
                +"    }\n"

                +"  }\n"
                +"  public void m2() {\n"
                +"    int i = 20;\n"
                +"    try {\n"
                +"      i=10;\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    }\n"
                +"    i = 0;\n"
                +"    //@ assert i == 0;\n"
                +"  }\n"
                +"  public void m3() {\n"
                +"    int i = 20;\n"
                +"    try {\n"
                +"      i=10;\n"
                +"    } catch (RuntimeException e) {\n"
                +"      i=1;\n"
                +"    } catch (Exception e) {\n"
                +"      i=2;\n"
                +"    } finally {\n"
                +"      i = 0;\n"
                +"    }\n"
                +"    //@ assert i == 0;\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (Assert) in method ma",9
                ,"/tt/TestJava.java:42: warning: else branch apparently never taken in method m1(int)",14
                ,"/tt/TestJava.java:59: warning: else branch apparently never taken in method m11(int)",14
                );
    }
    
    public void testTypes() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1(/*@non_null*/Object o) {\n"
                +"    //@ assume \\typeof(o) == Object.class;\n"
                +"    //@ assert \\typeof(o) == \\typeof(o);\n"
                +"    //@ assert \\typeof(o) == Object.class;\n"
                +"    //@ assert \\typeof(o) <: Object.class;\n"
                +"  }\n"
                +"  public void m1a(/*@non_null*/Object o) {\n"
                +"    //@ assume \\typeof(o) == Object.class;\n"
                +"    //@ assert \\typeof(o) != Object.class;\n"
                +"  }\n"
                +"  public void m2(/*@non_null*/Object o) {\n"
                +"    //@ assume \\typeof(o) == Object.class;\n"
                +"    //@ assert \\typeof(o) == \\type(Object);\n"
                +"  }\n"
                +"  public void m2a(/*@non_null*/Object o) {\n"
                +"    //@ assume \\typeof(o) == Object.class;\n"
                +"    //@ assert \\typeof(o) == \\type(TestJava);\n"
                +"  }\n"
                +"  public void m3(/*@non_null*/Object o) {\n"
                +"    //@ assume \\typeof(o) == Object.class;\n"
                +"    //@ assert \\type(TestJava) <: \\typeof(o);\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method m1a",9
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Assert) in method m2a",9
                );
    }
    public void testTypes2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1(/*@non_null*/TestJava o) {\n"
                +"    //@ assume \\typeof(o) <: TestJava.class;\n"
                +"    //@ assert \\typeof(o) <: Object.class;\n"
                +"  }\n"
                +"  public void m2(/*@non_null*/TestJava o) {\n"
                +"    //@ assert \\typeof(o) <: Object.class;\n"
                +"  }\n"
                +"}"
                );
    }
    
    public void testTypes3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m1(/*@non_null*/Object o) {\n"
                +"    //@ assert \\typeof(o) == o.getClass();\n"
                +"  }\n"
                +"}"
                );
    }

    public void testSignals() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                +"  //@ requires i >= 0;\n"
                +"  //@ ensures i>0;\n"
                +"  //@ signals (Exception e) i == 0;\n"
                +"  public void m1() throws Exception {\n"
                +"    if (i==0) throw new Exception();\n"
                +"  }\n"
                +"  //@ requires i >= 0;\n"
                +"  //@ ensures i>0;\n"
                +"  //@ signals (Exception e) i == 1;\n" // FAILS
                +"  public void m1a() throws Exception {\n"
                +"    if (i==0) throw new Exception();\n"
                +"  }\n"
                +"  //@ requires i >= 0;\n"
                +"  //@ ensures i>0;\n"
                +"  //@ signals (RuntimeException e) i == 1;\n"
                +"  public void m2() throws Exception {\n"
                +"    if (i==0) throw new Exception();\n"
                +"  }\n"
                +"  //@ requires i >= 0;\n"
                +"  //@ ensures i>0;\n"
                +"  //@ signals (Exception e) i == 0;\n"
                +"  public void m3() {\n"
                +"    if (i==0) throw new RuntimeException();\n"
                +"  }\n"
                +"  //@ requires i >= 0;\n"
                +"  //@ ensures i>0;\n"
                +"  //@ signals (Exception e) i == 1;\n" // FAILS
                +"  public void m3a() {\n"
                +"    if (i==0) throw new RuntimeException();\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1a",15
                ,"/tt/TestJava.java:12: warning: Associated declaration",7
                ,"/tt/TestJava.java:31: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m3a",15
                ,"/tt/TestJava.java:30: warning: Associated declaration",7
                );
    }

    public void testSignalsOnly() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                +"  //@ signals_only java.io.IOException;\n" // FAILS
                +"  public void m1a() throws Exception {\n"
                +"    if (i==0) throw new Exception();\n"
                +"  }\n"
                +"  //@ signals_only \\nothing;\n"  // FAILS
                +"  public void m2a() {\n"
                +"    if (i==0) throw new RuntimeException();\n"
                +"  }\n"
                +"  //@ signals_only Exception;\n"  // OK
                +"  public void m3() {\n"
                +"    if (i==0) throw new RuntimeException();\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1a",15
                ,"/tt/TestJava.java:4: warning: Associated declaration",20
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m2a",15
                ,"/tt/TestJava.java:8: warning: Associated declaration",7
                );
    }

    
}

