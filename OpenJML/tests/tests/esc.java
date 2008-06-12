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
                +"  TestJava(int i) {}\n"  // fails
                +"  //@ requires false;\n"
                +"  public static boolean bf(boolean bb) { return true; }\n"
                +"  //@ requires true;\n"
                +"  public static boolean bt(boolean bb) { return true; }\n"
                +"  static boolean b;\n"
                +"  //@ static invariant b;\n"
                +"  //@ requires !b;\n"
                +"  public static boolean bq(boolean bb) { return true; }\n"
                +"}",
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Invariant) in method <init>",24,
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
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Invariant) in method <init>",23,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Invariant) in method <init>",16,
                "/tt/TestJava.java:19: warning: Invariants+Preconditions appear to be contradictory in method i",21,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Invariant) in method inst",16
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
                +"}",
                "/tt/TestJava.java:5: warning: An assumption appears to be infeasible in method bassumeBADASSUMP",56,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method bifOK",113,
                "/tt/TestJava.java:9: warning: An assumption appears to be infeasible in method bifBAD",84
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
                "/tt/TestJava.java:4: warning: else branch apparently never taken in method bifok", 75,
                "/tt/TestJava.java:4: warning: then branch apparently never taken in method bifok", 120,
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
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method bok",15,
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Constraint) in method bok",27
                );
    }
    
    public void testOld2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static int i;\n"
                +"  //@ modifies i;\n"
                +"  //@ ensures i == \\old(i)+1;\n"
                +"  public static void bok() { i = i + 1; }\n"
                +"  //@ modifies i;\n"
                +"  //@ ensures i == \\old(i+1);\n"
                +"  public static void bbad() { i = i - 1; }\n"
                +"}",
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method bbad",15
                );
    }
    
    public void testReturn() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires 0<=ii && ii <=3;"
                +"  //@ ensures ii<=0 ==> \\result ==-ii;\n"
                +"  public static int bok(int ii) { if (ii==1) return -1; else if (ii==2) return -2; else if (ii==3) return -3; return 0; }\n"
                +"  //@ ensures \\result == -ii;\n"
                +"  public static int bbad(int ii) { if (ii==1) return -1; else if (ii==2) return -2; else if (ii==3) return -3; return 0; }\n"
                +"}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method bbad",15
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
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method inst",14,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method inst2", 10
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
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method instbad",15,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method inst2bad", 15
                );
    }
    
    public void testMethodCall() {
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
                +"  //@ ensures \\result == i;\n"
                +"  public int instbad(boolean b, int i) { m(i); return j; }\n"
                 +"}",
                 "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method instbad",17,
                 "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Postcondition) in method instbad",15
                );
    }
    
    
}

