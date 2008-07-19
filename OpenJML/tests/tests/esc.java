package tests;

public class esc extends EscBase {

    protected void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        //options.put("-jmlverbose",   "");
        //options.put("-noInternalSpecs",   "");
        System.out.println("TESTING " + getName());
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
                "/tt/TestJava.java:5: warning: An assumption appears to be infeasible in method bassumeBADASSUMP",56,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method bifOK",113,
                "/tt/TestJava.java:9: warning: An assumption appears to be infeasible in method bifBAD",84,
                "/tt/TestJava.java:12: warning: An assumption appears to be infeasible in method bassumeBADASSUMP2",57,
                "/tt/TestJava.java:13: warning: An assumption appears to be infeasible in method bassumeCHAIN1",87,
                "/tt/TestJava.java:13: warning: An assumption appears to be infeasible in method bassumeCHAIN1",75,
                "/tt/TestJava.java:14: warning: An assumption appears to be infeasible in method bassumeCHAIN2",85,
                "/tt/TestJava.java:15: warning: An assumption appears to be infeasible in method bassumeMULT",153,
                "/tt/TestJava.java:15: warning: An assumption appears to be infeasible in method bassumeMULT",142,
                "/tt/TestJava.java:15: warning: An assumption appears to be infeasible in method bassumeMULT",83
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
                "/tt/TestJava.java:6: warning: else branch apparently never taken in method bdead", 69,
                "/tt/TestJava.java:7: warning: then branch apparently never taken in method bdeadelse", 73
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
                "/tt/TestJava.java:4: warning: then branch apparently never taken in method bifok", 120,
                "/tt/TestJava.java:4: warning: else branch apparently never taken in method bifok", 75,
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
                 "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Precondition) in method instbad",42,
                 "/tt/TestJava.java:7: warning: Associated declaration",22,
                 "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Postcondition) in method instbad",14,
                 "/tt/TestJava.java:11: warning: Associated declaration",15,
                 "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Postcondition) in method instbad2",14,
                 "/tt/TestJava.java:13: warning: Associated declaration",15
                );
    }
    
    public void _testMethodCallBUG() { // FIXME - problems with static and non-static
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public int j;\n"
                +"  //@ requires i>0;\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures j == -i;\n"
                +"  public void m(int i) { j = -i; }\n"
                +"  //@ requires i>1; \n"
                +"  //@ ensures \\result == -i;\n"
                +"  public int inst(boolean b, int i) { m(i); return j; }\n"
                +"  //@ ensures \\result == j;\n"
                +"  public int instbad(boolean b, int i) { m(i); return j; }\n"
                +"  //@ ensures \\result == i;\n"
                +"  public int instbad2(boolean b, int i) { m(1); return j; }\n"
                 +"}",
                 "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Precondition) in method instbad",42,
                 "/tt/TestJava.java:7: warning: Associated declaration",15,
                 "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Postcondition) in method instbad2",14,
                 "/tt/TestJava.java:11: warning: Associated declaration",15
                );
    }
    
    public void testWhileSpecs() {  // FIXME
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                +"  public void instb() { int i = 5; /*@ loop_invariant i>=0; decreases i-2; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                +"  public void instc() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ while (i>0) { i = i+1; } /*@ assert i == 0; */ }\n"
                +"  public void instd() { int i = 5; /*@ loop_invariant i>0; decreases i; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                              +"}",
                 "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreasesNotPositive) in method instb",91,
                 "/tt/TestJava.java:4: warning: Associated declaration",61,
                 // FIXME - the next two lines are erroneous - on an infeasible branch, assertions may be assigned to fail or not - need to check the branchConditions and identify the path
                 "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopInvariant) in method instb",91,
                 "/tt/TestJava.java:4: warning: Associated declaration",55,
                 //"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method instb", 108,
                 "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (LoopDecreases) in method instc",89,
                 "/tt/TestJava.java:5: warning: Associated declaration",71,
                 "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method instc",106,
                 "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (LoopInvariant) in method instd",88,
                 "/tt/TestJava.java:6: warning: Associated declaration",55,
                 "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method instd",105
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
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method inst3d",57
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
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1a",81
                );
    }
    
    public void testNewArray() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1() { Object o = new int[5]; Object oo = new int[5]; /*@ assert o != oo;*/ }\n" 
                +"  public void inst1a() { Object o = new int[5]; Object oo = new int[5]; /*@ assert o == oo;*/ }\n" 
                +"  public void inst2() { int[] o = new int[5]; /*@ assert o.length == 5;*/ }\n" 
                +"  public void inst2a() { int[] o = new int[5]; /*@ assert o.length == 6;*/ }\n"
                +"  public void inst3(int[] a) { /*@ assert a.length >= 0;*/ }\n" 
                +"  public void inst4() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 3; assert o[1] == 11;*/ }\n" 
                +"  public void inst4a() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 4; */ }\n" 
                +"  public void inst4b() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 3; assert o[1] == 10;*/ }\n" 
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1a",77,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst2a",52,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method inst4a",61,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst4b",83
                );
    }
    
    public void _testNewArrayMD() { // FIXME
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst1() { Object o = new int[5][3]; Object oo = new int[5][3]; /*@ assert o != oo;*/ }\n" 
                +"  public void inst1a() { Object o = new int[5][3]; Object oo = new int[5][3]; /*@ assert o == oo;*/ }\n" 
                +"  public void inst2() { int[][] o = new int[5][3]; /*@ assert o.length == 5; assert o[1].length == 3; */ }\n" 
                +"  public void inst2a() { int[][] o = new int[5][3]; /*@ assert o.length == 6;*/ }\n"
                +"  public void inst2b() { int[][] o = new int[5][3]; /*@ assert o[1].length == 4;*/ }\n"
                +"  public void inst3(int[][] a) { /*@ assert a.length >= 0;*/ }\n" 
                +"  public void inst4() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o.length == 3; */ }\n" 
                +"  public void inst4a() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o.length == 2; */ }\n" 
                +"  public void inst5() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[1][2] == 14; */ }\n" 
                +"  public void inst6() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[2].length == 1; */ }\n" 
                +"  public void inst7() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[0].length == 2; */ }\n" 
                +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1a",77,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst2a",52,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst2b",52,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst4a",61
                );
    }
    
    public void testArrays() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  public void inst2(int[] a) { /*@ assume a[1] == 2; */  /*@ assert a[1] == 2; */ }\n" // OK
                +"  public void inst2a(int[] a) { /*@ assume a[1] == 2; */  /*@ assert a[1] == 3; */ }\n" // BAD
                +"  public void inst3(int[] a) { /*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */ }\n" // OK
                +"  public void inst3a(int[] a) { /*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 4; */ }\n" // BAD
                +"  public void inst4(int[] a) { /*@ assume a[0] == 2; */  a[1] = 3; /*@ assert a[0] == 2; */ }\n" // OK
                +"  public void inst4a(int[] a) { /*@ assume a[0] == 2; */  a[1] = 3; /*@ assert a[0] == 4; */ }\n" // BAD
                +"  public void inst5(int[] a) { /*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */  a[1] = 4; /*@ assert a[1] == 4; */}\n" // OK
                +"  public void inst5a(int[] a) { /*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */  a[1] = 4; /*@ assert a[1] == 5; */}\n" // BAD
                +"  public void inst6(int[] a, int[] b) { b = a; /*@ assert a[0] == b[0]; */}\n" // OK
                +"  public void inst6a(int[] a, int[] b) { b = a; /*@ assert a[0] != b[0]; */}\n" // BAD
                +"  public void inst7(int[] a, int[] b) { b[0] = 0; b = a; a[0] = 7; /*@ assert b[0] == 7; */}\n" // OK
                +"  public void inst7a(int[] a, int[] b) { b[0] = 0; b = a; a[0] = 7; /*@ assert b[0] == 8; */}\n" // BAD
                              +"}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst2a",63,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst3a",73,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst4a",73,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst5a",109,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method inst6a",53,
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method inst7a",73
                 );
    }
    
    public void testFields() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotations.*; \n"
                +"public class TestJava { \n"
                +"  int f; static int sf;\n"
                +"  int g; static int sg;\n"
                +"  static TestJava t;\n"
                +"  public void inst2(int[] a) { /*@ assume t.f == 2; */  /*@ assert t.f == 2; */ }\n" // OK
                +"  public void inst2a(int[] a) { /*@ assume t.f == 2; */  /*@ assert t.f == 3; */ }\n" // BAD
                +"  public void inst3(int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */ }\n" // OK
                +"  public void inst3a(int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 4; */ }\n" // BAD
                +"  public void inst4(int[] a) { /*@ assume t.g == 2; */  t.f = 3; /*@ assert t.g == 2; */ }\n" // OK
                +"  public void inst4a(int[] a) { /*@ assume t.g == 2; */  t.f = 3; /*@ assert t.g == 4; */ }\n" // BAD
                +"  public void inst5(int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */  t.f = 4; /*@ assert t.f == 4; */}\n" // OK
                +"  public void inst5a(int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */  t.f = 4; /*@ assert t.f == 5; */}\n" // BAD
                +"  public void inst6(TestJava a, TestJava b) { b = a; /*@ assert a.f == b.f; */}\n" // OK
                +"  public void inst6a(TestJava a, TestJava b) { b = a; /*@ assert a.f != b.f; */}\n" // BAD
                +"  public void inst7(TestJava a, TestJava b) { b.f = 0; b = a; a.f = 7; /*@ assert b.f == 7; */}\n" // OK
                +"  public void inst7a(TestJava a, TestJava b) { b.f = 0; b = a; a.f = 7; /*@ assert b.f == 8; */}\n" // BAD
                +"  public void inst8(TestJava a, TestJava b) { /*@ assert a.sf == b.sf; */}\n" // OK
                +"  public void inst8a(TestJava a, TestJava b) { /*@ assert a.sf != b.sf; */}\n" // BAD
                +"  public void inst9(TestJava a, TestJava b) { a.sf = 3; /*@ assert 3 == b.sf; */}\n" // OK
                +"  public void inst9a(TestJava a, TestJava b) { a.sf = 3; /*@ assert 3 != b.sf; */}\n" // BAD
                +"  public void inst10(TestJava a) { /*@ assert f == this.f; */ /*@ assert a == this ==> a.f == f; */}\n" // OK
                +"  public void inst10a(TestJava a) { /*@ assert f == this.f; */ /*@ assert a.f == f; */}\n" // BAD
                +"  public void inst11(TestJava a) { /*@ assert sf == this.sf; */ /*@ assert a.sf == sf; */}\n" // OK
                              +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst2a",62,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method inst3a",71,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method inst4a",71,
                "/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method inst5a",105,
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method inst6a",59,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method inst7a",77,
                "/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Assert) in method inst8a",52,
                "/tt/TestJava.java:21: warning: The prover cannot establish an assertion (Assert) in method inst9a",62,
                "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Assert) in method inst10a",68
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
                +"  public void inst3a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {default: i=4; } break; default: j=-1; case 2: j = 2; } /*@ assert j>0; */ }\n" // OK
                +"  public void inst4(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {} break; default: j=-1; case 2: j = 2; } /*@ assert j>=0; */ }\n" // OK
                              +"}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst1a",148,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method inst2a",141,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst3a",163
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
}

