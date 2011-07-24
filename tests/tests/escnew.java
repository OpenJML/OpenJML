package tests;


public class escnew extends EscBase {

    protected void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        options.put("-newesc","");
        options.put("-noPurityCheck","");
        //options.put("-jmlverbose",   "");
        //options.put("-method",   "m5good");
        options.put("-showbb",   "");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //options.put("-showce",   "");
        //options.put("-trace",   "");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }

    public void testPrecondition1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public void m1bad(int i) {\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>=0;\n"
                +"  public void m2bad(int i) {\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  public void m1good(int i) {\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  public void m2good(int i) {\n"
                +"    //@ assert i>=0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  //@ also\n"
                +"  //@ requires i==0;\n"
                +"  public void m3good(int i) {\n"
                +"    //@ assert i>=0 ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m2bad",9
                );
    }
    
    public void testPrecondition2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires i>0;\n"
                +"  //@ ensures false;\n"
                +"  public void m1a(int i) {\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  //@ requires i<0;\n"
                +"  //@ ensures false;\n"  // FIXME - this should eventually warn about infeasible preconditions
                +"  public void m1b(int i) {\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method m1a",15
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:10: warning: Invariants+Preconditions appear to be contradictory in method m1b(int)",-15
                );
    }
    
    public void testPrecondition3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires a[i]>0;\n"
                +"  public void m1bad(int[] a, int i) {\n"
                +"  }\n"
                
                +"  //@ requires i >= 0 && i < a.length;\n"
                +"  //@ requires a[i]>0;\n"
                +"  public void m1good(int[] a, int i) {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m1bad",17
                );
    }

    public void testPostcondition1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ signals (Exception) false;\n"
                +"  public void m1bad(int[] a, int i) {\n"
                +"    throw new RuntimeException(); \n"
                +"  }\n"
                
                +"  //@ ensures false;\n"
                +"  public void m2bad(int[] a, int i) {\n"
                +"  }\n"
                
                +"  //@ ensures false;\n"
                +"  public void m3bad(int[] a, int i) {\n"
                +"     return;\n"
                +"  }\n"
                
                +"  //@ ensures true;\n"
                +"  //@ signals (Exception e)  false;\n"
                +"  public void m1good(int[] a, int i) {\n"
                +"  }\n"
                
                +"  //@ ensures false;\n"
                +"  public void m2good(int[] a, int i) {\n"
                +"    throw new RuntimeException(); \n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",5
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",15
                ,"/tt/TestJava.java:7: warning: Associated declaration",7
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",6
                ,"/tt/TestJava.java:10: warning: Associated declaration",7
                );
    }
    
    public void testPostcondition2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires i == 0;\n"
                +"  //@ ensures false;\n"
                +"  //@ also\n"
                +"  //@ requires i!= 0;\n"
                +"  //@ ensures true;\n"
                +"  public void m1bad(int[] a, int i) {\n"
                +"      if (i == 0) \n"
                +"         return;\n"
                +"      else\n"
                +"         return;\n"
                +"  }\n"
                
                +"  //@ requires i == 0;\n"
                +"  //@ ensures true;\n"
                +"  //@ also\n"
                +"  //@ requires i!= 0;\n"
                +"  //@ ensures false;\n"
                +"  public void m2bad(int[] a, int i) {\n"
                +"      if (i == 0) \n"
                +"         return;\n"
                +"      else\n"
                +"         return;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",10
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",10
                ,"/tt/TestJava.java:18: warning: Associated declaration",7
                );
    }
    
    public void testPostcondition3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires i == 0;\n"
                +"  //@ signals (Exception e) false;\n"
                +"  //@ also\n"
                +"  //@ requires i!= 0;\n"
                +"  //@ signals (Exception e) true;\n"
                +"  public void m1bad(int[] a, int i) throws Exception {\n"
                +"      if (i == 0) \n"
                +"         throw new Exception();\n"
                +"      else\n"
                +"         throw new Exception();\n"
                +"  }\n"
                
                +"  //@ requires i == 0;\n"
                +"  //@ signals (Exception e) true;\n"
                +"  //@ also\n"
                +"  //@ requires i!= 0;\n"
                +"  //@ signals (Exception e) false;\n"
                +"  public void m2bad(int[] a, int i) throws Exception {\n"
                +"      if (i == 0) \n"
                +"         throw new Exception();\n"
                +"      else\n"
                +"         throw new Exception();\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",10
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:23: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m2bad",10
                ,"/tt/TestJava.java:18: warning: Associated declaration",7
                );
    }
    
    // Tests use of \exception token
    public void testPostcondition4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ signals (Exception e) \\exception == null;\n"
                +"  public void m1bad(int[] a, int i) throws Exception {\n"
                +"         throw new Exception();\n"
                +"  }\n"
                
                +"  //@ signals (Exception e) \\exception != null;\n"
                +"  public void m1good(int[] a, int i) throws Exception {\n"
                +"         throw new Exception();\n"
                +"  }\n"
                
                +"  //@ signals (Exception) \\exception != null;\n"
                +"  public void m2good(int[] a, int i) throws Exception {\n"
                +"         throw new Exception();\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",10
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                );
    }
    
    public void testNullThrow() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1bad(int i) throws Exception {\n"
                +"      if (i == 0) \n"
                +"         throw null;\n"
                +"  }\n"
                
                +"  public void m2bad(int i, /*@ nullable */ Exception e) throws Exception {\n"
                +"      if (i == 0) \n"
                +"         throw e;\n"
                +"  }\n"
                
                +"  //@ requires i != 0; \n"
                +"  public void m1good(int i) throws Exception {\n"
                +"      if (i == 0) \n"
                +"         throw null;\n"
                +"  }\n"
                
                +"  //@ requires i != 0; \n"
                +"  public void m2good(int i, Exception e) throws Exception {\n"
                +"      if (i == 0) \n"
                +"         throw e;\n"
                +"  }\n"
                
                +"  public void m3good(int i, Exception e) throws Exception {\n"
                +"      if (i == 0) \n"
                +"         throw e;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m1bad",16
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m2bad",16
                );
    }
    
    public void testNullSynchronized() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1bad(/*@ nullable */ Object o) throws Exception {\n"
                +"       synchronized (o) {};\n"
                +"  }\n"
                
                +"  public void m2bad( Object o) throws Exception {\n"
                +"       synchronized (o) {\n"
                +"          o = null; };\n"
                +"  }\n"
                
                +"  public void m1good(Object o) throws Exception {\n"
                +"       synchronized (o) {};\n"
                +"  }\n"
                
                +"  public void m2good(Object o) throws Exception {\n"
                +"       synchronized (this) {};\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m1bad",21
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2bad",13
                );
    }
    
    // FIXME - add checks on object fields, quantifier variables
    // FIXME - need attribute checks on scopes of variables
    public void testLabeled() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires i == 0; \n"
                +"  public void m1good(int i) throws Exception {\n"
                +"       int j = 0;\n"
                +"       //@ assert j == 0;\n"
                +"       a: j = 1; i = 1;\n"
                +"       //@ assert \\old(i) == 0;\n"
                +"       b: j = 2; i = 2;\n"
                +"       //@ assert \\old(j,a) == 0;\n"
                +"       //@ assert \\old(i,a) == 0;\n"
                +"       //@ assert \\old(j,b) == 1;\n"
                +"       //@ assert \\old(i,b) == 1;\n"
                +"       //@ assert \\pre(i) == 0;\n"
                +"       \n"
                +"  }\n"
                
                +"}"
                );
    }
    
    public void testSwitch() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures \\result == i* 2 + 1; \n"
                +"  public int m1bad(int i) throws Exception {\n"
                +"      int k;\n"
                +"       switch (i) {\n"
                +"        case 1: k = 3; break;\n"
                +"        default: k = i + i + 1; break;\n"
                +"        case 2: k = 6; return k;\n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures \\result == i* 2 + 1; \n"
                +"  public int m1good(int i) throws Exception {\n"
                +"      int k;\n"
                +"       switch (i) {\n"
                +"        case 1: k = 3; break;\n"
                +"        default: k = i + i + 1; break;\n"
                +"        case 2: k = 5; break;\n"
                +"       } return k;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",24
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                );
    }
    
    public void testTry() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures \\result == 1; \n"
                +"  public int m1bad() throws Exception {\n"
                +"      int k;\n"
                +"       try {\n"
                +"        k=1; \n"
                +"       } finally {\n"
                +"           k = 2;\n"
                +"        }return k;\n"
                +"  }\n"
                
                +"  //@ ensures \\result == 0; \n"
                +"  public int m2bad() throws Exception {\n"
                +"      int k;\n"
                +"       try {\n"
                +"        k=1; throw new RuntimeException();\n"
                +"       } catch (RuntimeException e) {\n"
                +"           k = 2;\n"
                +"        } return k; \n"
                +"  }\n"
                
                +"  //@ ensures \\result == 0; \n"
                +"  public int m3bad() throws Exception {\n"
                +"      int k;\n"
                +"       try {\n"
                +"        k=1; throw new RuntimeException();\n"
                +"       } catch (RuntimeException e) {\n"
                +"           k = 2;\n"
                +"       } finally {\n"
                +"           k = 3;\n"
                +"        } return k; \n"
                +"  }\n"
                
                +"  //@ ensures \\result == 1; \n"
                +"  public int m1good() throws Exception {\n"
                +"      int k;\n"
                +"       try {\n"
                +"        k=1; return k;\n"
                +"       } finally {\n"
                +"           k = 2;\n"
                +"        } \n"
                +"  }\n"
                
                +"  //@ ensures \\result == 2; \n"
                +"  public int m0good() throws Exception {\n"
                +"      int k;\n"
                +"       try {\n"
                +"        k=1; \n"
                +"       } finally {\n"
                +"           k = 2;\n"
                +"        } return k;\n"
                +"  }\n"
                
                +"  //@ ensures \\result == 2; \n"
                +"  public int m2good() throws Exception {\n"
                +"      int k;\n"
                +"       try {\n"
                +"        k=1; throw new RuntimeException();\n"
                +"       } catch (RuntimeException e) {\n"
                +"           k = 2;\n"
                +"        } return k; \n"
                +"  }\n"
                
                +"  //@ ensures \\result == 3; \n"
                +"  public int m3good() throws Exception {\n"
                +"      int k;\n"
                +"       try {\n"
                +"        k=1; throw new RuntimeException();\n"
                +"       } catch (RuntimeException e) {\n"
                +"           k = 2;\n"
                +"       } finally {\n"
                +"           k = 3\n;"
                +"        } return k; \n"
                +"  }\n"
                
                +"  static int kk;\n"

                +"  //@ assignable kk;\n"
                +"  //@ ensures \\result == 3; signals (Exception e)  false; \n"
                +"  public int m4good(int i ) throws Exception {\n"
                +"       try {\n"
                +"        kk=1; if (i == 0) throw new RuntimeException();\n"
                +"       } catch (RuntimeException e) {\n"
                +"           kk = 2;\n"
                +"        } \n"
                +"       kk = 3;\n"
                +"       return kk; \n"
                +"  }\n"
                
                +"  //@ assignable kk;\n"
                +"  //@ ensures \\result == 3; signals (Exception e)  kk == 1; \n"
                +"  public int m5good(int i) throws Exception {\n"
                +"       try {\n"
                +"        kk=1; if (i == 0) throw new RuntimeException();\n"
                +"        } finally {} \n"
                +"       kk = 3;\n"
                +"       return kk; \n"
                +"  }\n"
                
                +"  //@ assignable kk;\n"
                +"  //@ ensures \\result == 3; signals (Exception e)  kk == 1; \n"
                +"  public int m6good(int i) throws Exception {\n"
                +"        kk=1; if (i == 0) throw new RuntimeException();\n"
                +"       kk = 3;\n"
                +"       return kk; \n"
                +"  }\n"
                
                +"  //@ assignable kk;\n"
                +"  //@ ensures \\result == 3; signals (Exception e) kk == 4; \n"
                +"  public int m7good(int i) throws Exception {\n"
                +"       try {\n"
                +"           kk=1; if (i == 0) throw new RuntimeException();\n"
                +"           try {\n"
                +"             kk=2; if (i == 1) throw new RuntimeException();\n"
                +"           } finally { kk = 5; } \n"
                +"       } finally { kk = 4; } \n"
                +"       kk = 3;\n"
                +"       return kk; \n"
                +"  }\n"
                
                +"  //@ assignable kk;\n"
                +"  //@ ensures i==0 ==> \\result == 4; signals (Exception e) false; \n"
                +"  public int m8good(int i) throws Exception {\n"
                +"       try {\n"
                +"           kk=1; if (i == 0) throw new RuntimeException();\n"
                +"       } finally { if (i == 0) return 4; } \n"
                +"       kk = 3;\n"
                +"       return kk; \n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",10
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",11
                ,"/tt/TestJava.java:12: warning: Associated declaration",7
                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",11
                ,"/tt/TestJava.java:21: warning: Associated declaration",7
                
                );
    }
    
    public void testUnreachable() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1bad(int i) {\n"
                +"      if (i == 0) { \n"
                +"         //@ unreachable;\n"
                +"      }\n"
                +"  }\n"
                
                +"  //@ requires i != 0; \n"
                +"  public void m1good(int i) {\n"
                +"      if (i == 0) { \n"
                +"         //@ unreachable;\n"
                +"      }\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Unreachable) in method m1bad",14
                );
    }
    

    public void testGhostSet() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1bad(int i) {\n"
                +"      //@ ghost int k = 0;"
                +"      //@ set k = 1;\n"
                +"      //@ assert k == 0; \n"
                +"  }\n"
                
                +"  //@ requires i != 0; \n"
                +"  public void m1good(int i) {\n"
                +"      //@ ghost int k = 0;"
                +"      //@ set k = 1;\n"
                +"      //@ assert k == 1; \n"
                +"  }\n"
                
                +"  public void m2bad(int i) {\n"
                +"      //@ ghost int k = 0;"
                +"      //@ debug k = 1;\n"
                +"      //@ assert k == 0; \n"
                +"  }\n"
                
                +"  //@ requires i != 0; \n"
                +"  public void m2good(int i) {\n"
                +"      //@ ghost int k = 0;"
                +"      //@ debug k = 1;\n"
                +"      //@ assert k == 1; \n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m1bad",11
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method m2bad",11
                );
    }
    

    
    // FIXME _ check that different return or throw statements are properly pointed to

    // FIXME - needs proper expansion of array accesses
//    public void testPostcondition1() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ ensures a[i]>0;\n"
//                +"  public void m1bad(int[] a, int i) {\n"
//                +"  }\n"
//                
//                +"  //@ requires i >= 0 && i < a.length;\n"
//                +"  //@ ensures a[i]==true || a[i]==false;\n"
//                +"  public void m1good(boolean[] a, int i) {\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m1bad",16
//                );
//    }
    
    // FIXME - need tests with multiple ensures and various cases
    
    // FIXME - test definedness in postconditions
    
    // FIXME - exceptional postconditions
    
    // FIXME - need precondition checks for calling methods
    // FIXME - need checks for ensures assumptions when calling methods
    // FIXME - complete assignables
    // FIXME - assignables for method calls

    // Just testing binary and unary 
    public void testBinaryUnary() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result ==4;\n"
                +"  public int m1bad() {\n"
                +"    return 1 + 2;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result == 3;\n"
                +"  public int m1ok() {\n"
                +"    return 1 + 2;\n"
                +"  }\n"
                
                +"  //@ requires x >= 0;\n"
                +"  //@ ensures \\result < 0;\n"
                +"  public int m2bad(int x) {\n"
                +"    return -x;\n"
                +"  }\n"
                
                +"  //@ requires x >= 0;\n"
                +"  //@ ensures \\result <= 0;\n"
                +"  public int m2ok(int x) {\n"
                +"    return -x;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                ,"/tt/TestJava.java:14: warning: Associated declaration",7
                );
    }

    // Just testing binary and unary 
    public void testJMLBinaryUnary() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires p ==> q;\n"
                +"  //@ ensures !p || q;\n"
                +"  public void m1ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                +"  //@ requires p <==> q;\n"
                +"  //@ ensures p == q;\n"
                +"  public void m2ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                +"  //@ requires p <=!=> q;\n"
                +"  //@ ensures p != q;\n"
                +"  public void m3ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                +"  //@ requires p <== q;\n"
                +"  //@ ensures p || !q;\n"
                +"  public void m4ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                +"  //@ requires !p || q;\n"
                +"  //@ ensures p ==> q;\n"
                +"  public void m5ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                +"  //@ requires p == q;\n"
                +"  //@ ensures p <==> q;\n"
                +"  public void m6ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                +"  //@ requires p != q;\n"
                +"  //@ ensures p <=!=> q;\n"
                +"  public void m7ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                +"  //@ requires p || !q;\n"
                +"  //@ ensures p <== q;\n"
                +"  public void m8ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                
                +"}"
                );
    }

    public void testConditional() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result == i;\n"
                +"  public int m1bad(boolean b, int i) {\n"
                +"    return (b && (i == 1)) ? i : i + 1 ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result >= i;\n"
                +"  public int m1ok(boolean b, int i) {\n"
                +"    return (b && (i == 1)) ? i : i + 1 ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    public void testBoolOpsParens() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m1bad(boolean p, boolean q) {\n"
                +"    return p == q;\n"
                +"  }\n"
                
                +"  //@ requires p && q;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m1ok(boolean p, boolean q) {\n"
                +"    return ((p == q)) ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m2bad(boolean p, boolean q) {\n"
                +"    return p != q;\n"
                +"  }\n"
                
                +"  //@ requires p && !q;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m2ok(boolean p, boolean q) {\n"
                +"    return p != q ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m3bad(boolean p, boolean q) {\n"
                +"    return p == !q;\n"
                +"  }\n"
                
                +"  //@ requires p && !q;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m3ok(boolean p, boolean q) {\n"
                +"    return p == !q ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                ,"/tt/TestJava.java:14: warning: Associated declaration",7
                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                ,"/tt/TestJava.java:24: warning: Associated declaration",7
                );
    }

    public void testSelect() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m1bad() {\n"
                +"    return this.f ;\n"
                +"  }\n"
                
                +"  //@ requires this.f == 1;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m1ok() {\n"
                +"    return this.f ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m2bad() {\n"
                +"    return f ;\n"
                +"  }\n"
                
                +"  //@ requires f == 1;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m2ok() {\n"
                +"    return f ;\n"
                +"  }\n"
                
                +"  //@ requires f == 1;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m3bad(TestJava p) {\n"
                +"    return p.f ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures true;\n"
                +"  public int m3bad2(/*@nullable*/ TestJava p) {\n"
                +"    return p.f ;\n"
                +"  }\n"
                
                +"  //@ requires p.f == 1;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m3ok(TestJava p) {\n"
                +"    return p.f ;\n"
                +"  }\n"
                
                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:5: warning: Associated declaration",7
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                ,"/tt/TestJava.java:15: warning: Associated declaration",7
                ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                ,"/tt/TestJava.java:25: warning: Associated declaration",7
                ,"/tt/TestJava.java:32: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m3bad2",13
                );
    }

    public void testArrayIndex() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  public int m1bad(int[] a) {\n"
                +"    return a[10] ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  public int m1bada(int[] a) {\n"
                +"    return a[-1] ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  public int m1badb(int[] a, int i) {\n"
                +"    return a[i] ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  public int m1good(int[] a) {\n"
                +"    return a[0] ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  public int m1gooda(int[] a) {\n"
                +"    return a[9] ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  //@ requires i >= 3;\n"
                +"  //@ requires i <= 8;\n"
                +"  public int m1goodb(int[] a, int i) {\n"
                +"    return a[i] ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1bad",13
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1bada",13
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1badb",-13
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1badb",-13
                );
    }

    public void testArrayValue() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  //@ ensures \\result == a[1];\n"
                +"  public int m1bad(int[] a) {\n"
                +"    return a[0] ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  //@ ensures \\result == a[0];\n"
                +"  public int m1good(int[] a) {\n"
                +"    return a[0] ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:5: warning: Associated declaration",7
                );
    }

    public void testAssignOp() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ ensures \\result == j;\n"
                +"  public int m1bad(int j) {\n"
                +"    int i = j ;\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                +"  //@ ensures \\result == j+1;\n"
                +"  public int m1good(int j) {\n"
                +"    int i = j ;\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    public void testChangedParam() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ ensures \\result == i;\n"
                +"  public int m1bad(int i) {\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                +"  //@ ensures \\result == i+1;\n"
                +"  public int m1good(int i) {\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    public void testNonNullField() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public Object nnf;\n"
                +"  public /*@ nullable*/ Object f;\n"

                // FIXME - these crash Z3
//                +"  public Object m1bad() {\n"
//                +"    return this.f ;\n"
//                +"  }\n"
//                
//                +"  public Object m1ok() {\n"
//                +"    return this.nnf ;\n"
//                +"  }\n"
                
                +"  public void m2bad() {\n"
                +"    nnf = null ;\n"
                +"  }\n"
                
//                +"  public void m2ok() {\n"
//                +"    f = null ;\n"
//                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2bad",9
                );
    }

    public void testExplicitAssert() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  public void m1bad(int i) {\n"
                +"    //@ assert i == 0 ;\n"
                +"  }\n"
                
                +"  //@ requires i == 0;\n"
                +"  public void m1ok(int i) {\n"
                +"    //@ assert i == 0 ;\n"
                +"  }\n"
                
                +"  public void m1okb(int i) {\n"
                +"    //@ assume i == 0 ;\n"
                +"    //@ assert i == 0 ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  public void m2bad(int i) {\n"
                +"    assert i == 0 ;\n"
                +"  }\n"
                
                +"  //@ requires i == 0;\n"
                +"  public void m2ok(int i) {\n"
                +"    assert i == 0 : \"ASD\" ;\n"
                +"  }\n"
                
                +"  public void m2okb(int i) {\n"
                +"    //@ assume i == 0 ;\n"
                +"    assert i == 0 ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method m2bad",12
                );
    }
    
    public void testAssignment() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1bad(boolean i) {\n"
                +"    int x = 0 ;\n"
                +"    if (i) x = 1; else x = 2; ;\n"
                +"    x = x + 1 ;\n"
                +"    //@ assert x < 3 ;\n"
                +"  }\n"
                
                +"  public void m1ok(boolean i) {\n"
                +"    int x = 0 ;\n"
                +"    if (i) x = 1; else x = 2; ;\n"
                +"    x = x + 1 ;\n"
                +"    //@ assert x < 4 ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
                );    }

    public void testUndefined() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires 10/i < 0;\n"
                +"  public void m1bad(int i) {\n"
                +"  }\n"
                
                +"  //@ requires i != 0 && 10/i < 0;\n"
                +"  public void m1good(int i) {\n"
                +"  }\n"
                
                +"  //@ ensures 10/i < 0 || true;\n"
                +"  public void m2bad(int i) {\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 || 10/i < 0 || true;\n"
                +"  public void m2good(int i) {\n"
                +"  }\n"
                
                +"  public void m3bad(int i) {\n"
                +"  //@ assume 10/i < 0 || true;\n"
                +"  }\n"
                
                +"  public void m3good(int i) {\n"
                +"  //@ assume i == 0 || 10/i < 0 || true;\n"
                +"  }\n"
                
                +"  public void m4bad(int i) {\n"
                +"  //@ assert 10/i < 0 ||true;\n"
                +"  }\n"
                
                +"  public void m4good(int i) {\n"
                +"  //@ assert i == 0 || 10/i < 0 || true;\n"
                +"  }\n"
                
                +"  public void m5bad(int i) {\n"
                +"  //@ assert 10%i < 0 ||true;\n"
                +"  }\n"
                
                +"  public void m5good(int i) {\n"
                +"  //@ assert i == 0 || 10%i < 0 || true;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m1bad",18
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m2bad",17
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m3bad",16
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m4bad",16
                ,"/tt/TestJava.java:28: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m5bad",16
                );    }

    public void testAssignable1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int x,y; \n"
                
                +"  //@ assignable x; \n"
                +"  public void m1bad(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"
                
                +"  //@ assignable x; \n"
                +"  public void m1good(int i) {\n"
                +"    x = 0 ;\n"
                +"    i = 0; ;\n"
                +"    int k = 0; ;\n"
                +"    k = 0; ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assignable) in method m1bad",7
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
        }

    public void testAssignable2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int x; \n"
                
                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  public void mgood(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"
                
                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  public void m1good(int i) {\n"
                +"    if (i > 0) x = 0 ;\n"  // FIXME - warn about else branch
                +"  }\n"
                
                +"}"
                );
        }

    public void testAssignable3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int x,y; \n"
                
                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  //@ also \n"
                +"  //@ requires i == 0; \n"
                +"  //@ assignable y; \n"
                +"  public void m1bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"
                
                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  //@ also \n"
                +"  //@ requires i == 0; \n"
                +"  //@ assignable y; \n"
                +"  public void m1good(int i) {\n"
                +"    if (i > 0) x = 0 ;\n"
                +"    if (i == 0) y = 0 ;\n"
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assignable) in method m1bad",7
                ,"/tt/TestJava.java:8: warning: Associated declaration",7
                );
        }

    public void testAssignable4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int x,y; \n"
                
                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  //@ also \n"
                +"  //@ requires i == 0; \n"
                +"  //@ assignable y; \n"
                +"  public void m1bad(int i) {\n"
                +"    i = 0 ;\n"
                +"    y = 0 ;\n"
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assignable) in method m1bad",7
                ,"/tt/TestJava.java:5: warning: Associated declaration",7
                );
        }

    public void testAssignable5() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int x,xx; static int y,yy; \n"
                
                +"  //@ assignable this.x; \n"
                +"  public void m1bad(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"
                                
                +"  //@ assignable this.x; \n"
                +"  public void m2bad(int i) {\n"
                +"    xx = 0 ;\n"
                +"  }\n"
                                
                +"  //@ assignable TestJava.y; \n"
                +"  public void m3bad(int i) {\n"
                +"    yy = 0 ;\n"
                +"  }\n"
                                
                +"  //@ assignable TestJava.y; \n"
                +"  public void m4bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"
                                
                +"  //@ assignable tt.TestJava.y; \n"
                +"  public void m5bad(int i) {\n"
                +"    yy = 0 ;\n"
                +"  }\n"
                                
                +"  //@ assignable tt.TestJava.y; \n"
                +"  public void m6bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"
                                
                +"  //@ assignable this.x; \n"
                +"  public void m1good(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"
                                
                +"  //@ assignable TestJava.y; \n"
                +"  public void m2good(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"
                                
                +"  //@ assignable tt.TestJava.y; \n"
                +"  public void m3good(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assignable) in method m1bad",7
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assignable) in method m2bad",8
                ,"/tt/TestJava.java:8: warning: Associated declaration",7
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assignable) in method m3bad",8
                ,"/tt/TestJava.java:12: warning: Associated declaration",7
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Assignable) in method m4bad",7
                ,"/tt/TestJava.java:16: warning: Associated declaration",7
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (Assignable) in method m5bad",8
                ,"/tt/TestJava.java:20: warning: Associated declaration",7
                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Assignable) in method m6bad",7
                ,"/tt/TestJava.java:24: warning: Associated declaration",7
                );
        }

    public void testAssignable6() {
//      options.put("-showbb","");
//    options.put("-trace", "");
//    options.put("-method","m1good");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int x,xx; static int y,yy; \n"
                
                +"  //@ assignable this.*; \n"
                +"  public void m1bad(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"
                                
                +"  //@ assignable TestJava.*; \n"
                +"  public void m2bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"
                                
                +"  //@ assignable tt.TestJava.*; \n"
                +"  public void m3bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"
                                
                +"  //@ assignable this.*; \n"
                +"  public void m1good(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"
                                
                +"  //@ assignable TestJava.*; \n"
                +"  public void m2good(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"
                                
                +"  //@ assignable tt.TestJava.*; \n"
                +"  public void m3good(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assignable) in method m1bad",7
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assignable) in method m2bad",7
                ,"/tt/TestJava.java:8: warning: Associated declaration",7
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assignable) in method m3bad",7
                ,"/tt/TestJava.java:12: warning: Associated declaration",7
                );
        }


}
