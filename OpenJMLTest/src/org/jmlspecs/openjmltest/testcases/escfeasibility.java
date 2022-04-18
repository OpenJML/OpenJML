package org.jmlspecs.openjmltest.testcases;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escfeasibility extends EscBase {

    public escfeasibility(String option, String solver) {
        super(option,solver);
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        //print = true;
    }
    
    @Test
    public void testPrecondition() {
        main.addOptions("--check-feasibility=precondition");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i > 0;
                    //@ requires i < 0;
                    public void m(int i) {
                    }
                }
                """
                ,"/tt/TestJava.java:5: warning: Invariants+Preconditions appear to be contradictory in method tt.TestJava.m(int)",17
                );
    }

    @Test
    public void testPreconditionA() {
        main.addOptions("--check-feasibility=all");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i > 0;
                    //@ requires i < 0;
                    public void m(int i) {
                    }
                }
                """
                ,"/tt/TestJava.java:5: warning: Invariants+Preconditions appear to be contradictory in method tt.TestJava.m(int)",17
                );
    }

    // This is not a great test of debug as it does not show all the points actually tested
    // FIXME: Improve names of program points and locations
    @Test
    public void testPreconditionD() {
        main.addOptions("--check-feasibility=debug","-method=m");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public void m(int i) {
                        //@ assume i > 0 && i < 0;
                    }
                }
                """
                ,"/tt/TestJava.java:4: warning: There is no feasible path to program point Extra-Assume in method tt.TestJava.m(int)",26
                ,"/tt/TestJava.java:4: warning: There is no feasible path to program point after explicit assume statement in method tt.TestJava.m(int)",13
                ,"/tt/TestJava.java:3: warning: There is no feasible path to program point at program exit in method tt.TestJava.m(int)",17
                ,"/tt/TestJava.java: warning: There is no feasible path to program point Extra-Assert in method tt.TestJava.m(int)",-1
                );
    }

    @Test
    public void testPreconditionN() {
        main.addOptions("--check-feasibility=none");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i > 0;
                    //@ requires i < 0;
                    public void m(int i) {
                    }
                }
                """
                );
    }

    @Test
    public void testIfThen() {
        main.addOptions("--check-feasibility=if");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i > 0;
                    public void m(int i) {
                        if (i < 0) {
                            
                        }
                    }
                }
                """
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point at then branch in method tt.TestJava.m(int)",9
                );
    }


    @Test
    public void testIfElse() {
        main.addOptions("--check-feasibility=if");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i > 0;
                    public void m(int i) {
                        if (true) {
                            
                        } else {
                            
                        }
                    }
                }
                """
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point at else branch in method tt.TestJava.m(int)",9
                );
    }


    @Test
    public void testIfOnlyThen() {
        main.addOptions("--check-feasibility=if");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i > 0;
                    public void m(int i) {
                        if (true) {
                            
                        }
                    }
                }
                """
                // OK
                );
    }

    @Test
    public void testCall() {
        main.addOptions("--check-feasibility=call");
        helpTCX("tt.TestJava",
                """
                package tt;
                abstract class A {
                    public int kk;
                    //@ ensures kk == \\old(kk) + 1;
                    //@ pure // faulty spec
                    abstract public void mm();
                }
                abstract public class TestJava extends A {
                    //@ requires i > 0;
                    public void m(int i) {
                        mm();
                    }
                }
                """
                ,"/tt/TestJava.java:11: warning: There is no feasible path to program point after call in method tt.TestJava.m(int)",11
                );
    }

    @Test
    public void testHalt() {
        main.addOptions("--check-feasibility=halt");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i > 0;
                    public void m(int i) {
                        int j = i;
                        if (i != j) {
                            //@ halt;
                        }
                    }
                }
                """
                ,"/tt/TestJava.java:7: warning: There is no feasible path to program point at halt statement in method tt.TestJava.m(int)",17
                );
    }

    @Test
    public void testAssert() {
        main.addOptions("--check-feasibility=assert");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i > 0;
                    public void m(int i) {
                        int j = i;
                        //@ assume i < 0;
                        //@ assert i != j;
                    }
                }
                """
                ,"/tt/TestJava.java:7: warning: There is no feasible path to program point before explicit assert statement in method tt.TestJava.m(int)",13
                );
    }

    @Test
    public void testAssume() {
        main.addOptions("--check-feasibility=assume");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i > 0;
                    public void m(int i) {
                        int j = i;
                        //@ assume i < 0;
                    }
                }
                """
                ,"/tt/TestJava.java:6: warning: There is no feasible path to program point after explicit assume statement in method tt.TestJava.m(int)",13
                );
    }

    @Test
    public void testReachable() {
        main.addOptions("--check-feasibility=reachable");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i > 0;
                    public void m(int i) {
                        int j = i;
                        if (i != j) {
                            //@ reachable;
                        }
                    }
                }
                """
                ,"/tt/TestJava.java:7: warning: There is no feasible path to program point at reachable statement in method tt.TestJava.m(int)",17
                );
    }

    @Test
    public void testSwitch() {
        main.addOptions("--check-feasibility=switch");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires 0 < i < 3;
                    public void m(int i) {
                        switch(i) {
                            case 1: break;
                            case 4: break;
                            case 2: break;
                            default: break;
                        }
                    }
                }
                """
                ,"/tt/TestJava.java:7: warning: There is no feasible path to program point after case condition in method tt.TestJava.m(int)",13
                ,"/tt/TestJava.java:9: warning: There is no feasible path to program point after case condition in method tt.TestJava.m(int)",13
                );
    }

    @Test
    public void testFinally() {
        main.addOptions("--check-feasibility=finally");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public void m(int i) {
                        try {
                            //@ assume i > 0;
                            //@ assume i < 0;
                        } finally {
                            int j = 1;
                        }
                    }
                }
                """
                ,"/tt/TestJava.java:7: warning: There is no feasible path to program point at beginning of finally block in method tt.TestJava.m(int)",19
                );
    }

    @Test
    public void testCatch() {
        main.addOptions("--check-feasibility=catch");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i == 1;
                    public void m(int i) {
                        try {
                            if (i != 1) throw new RuntimeException();
                        } catch (RuntimeException e) {
                            
                        } finally {
                            int j = 1;
                        }
                    }
                }
                """
                ,"/tt/TestJava.java:7: warning: There is no feasible path to program point at beginning of catch block in method tt.TestJava.m(int)",11
                );
    }

    @Test
    public void testSpec() {
        main.addOptions("--check-feasibility=spec");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public int k;
                    //@ requires i == 1 && k < 1000;
                    public void m(int i) {
                        //@ refining
                        //@ ensures k == \\old(k) + 1;
                        {
                            k++;
                            //@ assume i == 2;
                        }
                        //@ assert i == 2;
                    }
                }
                """
                ,"/tt/TestJava.java:6: warning: There is no feasible path to program point at statement spec (after using summary) in method tt.TestJava.m(int)",13
                ,"/tt/TestJava.java:6: warning: There is no feasible path to program point at statement spec (after specified block) in method tt.TestJava.m(int)",13
                ); // FIXME - improve message positions
    }

    @Test
    public void testExit() {
        main.addOptions("--check-feasibility=exit");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i == 1;
                    public void m(int i) {
                        //@ assume i == 2;
                    }
                }
                """
                ,"/tt/TestJava.java:4: warning: There is no feasible path to program point at program exit in method tt.TestJava.m(int)",17
                );
    }

    @Test
    public void testReturn() {
        main.addOptions("--check-feasibility=return");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i == 1;
                    public void m(int i) {
                        if (i == 2) return;
                    }
                }
                """
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point at return statement in method tt.TestJava.m(int)",21
                );
    }

    @Test @Ignore // FIXME - need to implement a way of telling whether execution flow is still alive at the end of the block
    public void testReturnDefault() {
        main.addOptions("--check-feasibility=return");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i == 1;
                    public void m(int i, RuntimeException e) {
                        if (i == 1) throw e;
                    }
                }
                """
                ,"/tt/TestJava.java:4: warning: There is no feasible path to program point at fall-through return in method tt.TestJava.m(int,java.lang.RuntimeException)",46
                );
    }

    @Test
    public void testReturnOK() {
        main.addOptions("--check-feasibility=return");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i == 1;
                    public void m(int i) {
                        return;
                    }
                }
                """
                );
    }

    @Test
    public void testReturnDefaultOK() {
        main.addOptions("--check-feasibility=return");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i == 1;
                    public void m(int i) {
                    }
                }
                """
                );
    }

    @Test
    public void testThrow() {
        main.addOptions("--check-feasibility=throw");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i == 1;
                    public void m(int i) {
                        if (i == 2) throw new RuntimeException();
                    }
                }
                """
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point at throw statement in method tt.TestJava.m(int)",21
                );
    }

    @Test
    public void testLoopForExit() {
        main.addOptions("--check-feasibility=loopexit");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i == 1;
                    public void m(int i) {
                        for (int k = 0; i==1; ) {
                            
                        }
                    }
                }
                """
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point at loop exit in method tt.TestJava.m(int)",9
                );
    }

    @Test
    public void testLoopForCondition() {
        main.addOptions("--check-feasibility=loopcondition");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i == 1;
                    public void m(int i) {
                        for (int k = 0; i!=1; ) {
                            
                        }
                    }
                }
                """
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point at beginning of loop body in method tt.TestJava.m(int)",9
                );
    }

    @Test
    public void testLoopWhileExit() {
        main.addOptions("--check-feasibility=loopexit");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i == 1;
                    public void m(int i) {
                        while (i==1) {
                            
                        }
                    }
                }
                """
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point at loop exit in method tt.TestJava.m(int)",9
                );
    }

    @Test
    public void testLoopWhileCondition() {
        main.addOptions("--check-feasibility=loopcondition");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i == 1;
                    public void m(int i) {
                        while (i!=1) {
                            
                        }
                    }
                }
                """
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point at beginning of loop body in method tt.TestJava.m(int)",9
                );
    }

    @Test
    public void testLoopDoWhileExit() {
        main.addOptions("--check-feasibility=loopexit");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i == 1;
                    public void m(int i) {
                        do {
                            
                        } while (i == 1);
                    }
                }
                """
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point at loop exit in method tt.TestJava.m(int)",9
                );
    }

    @Test @Ignore // FIXME needs fixing
    public void testLoopDoWhileCondition() {
        main.addOptions("--check-feasibility=loopcondition");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires i == 1;
                    public void m(int i) {
                        do {
                            
                        } while (i == 1);
                    }
                }
                """
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point at loop exit in method tt.TestJava.m(int)",9
                );
    }

    @Test @Ignore // FIXME needs fixing
    public void testLoopForEachExit() {
        main.addOptions("--check-feasibility=loopexit");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires a.length > 0;
                    public void m(int[] a) {
                        for (int i: a) {
                            return;
                        }
                    }
                }
                """
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point at loop exit in method tt.TestJava.m(int)",9
                );
    }

    @Test
    public void testLoopForEachCondition() {
        main.addOptions("--check-feasibility=loopcondition");
        helpTCX("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ requires a.length == 0;
                    public void m(int[] a) {
                        for (int i: a) {
                            return;
                        }
                    }
                }
                """
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point at beginning of loop body in method tt.TestJava.m(int[])",9
                );
    }

    @Test
    public void testPreconditionOnlyA() {
        main.addOptions("-checkFeasibility=precondition");
        helpTCX("tt.TestJava",
                                "package tt; \n"
                              + "public class TestJava { \n"
                              + "  //@ requires i > -10 && i < 10;\n"
                              + "  public void m(int i) {\n"
                              + "     //@ assert i != i;\n" // ERROR
                              + "    }\n"
                              + "\n"
                              + "  //@ requires i > 0;\n"
                              + "  //@ requires i < 0;\n"
                              + "  public void mm(int i) {\n"
                              + "     //@ assert i != i;\n"
                              + "    }\n"
                              + "  //@ requires i > 0;\n"
                              + "  //@ ensures \\result > 0;\n" // ERROR
                              + "  public int mmm(int i) {\n"
                              + "     return -i;\n"
                              + "    }\n"
                              + "}"
                              ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m",10
                              ,"/tt/TestJava.java:10: warning: Invariants+Preconditions appear to be contradictory in method tt.TestJava.mm(int)",15
                              ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method mmm",6
                              ,"/tt/TestJava.java:14: warning: Associated declaration",7
                              );
        }
        
        @Test
        public void testPreconditionOnly() {
            main.addOptions("-checkFeasibility=preconditionOnly");
            helpTCX("tt.TestJava",
                                    "package tt; \n"
                                  + "public class TestJava { \n"
                                  + "  //@ requires i > -10 && i < 10;\n"
                                  + "  public void m(int i) {\n"
                                  + "     //@ assert i != i;\n"
                                  + "    }\n"
                                  + "\n"
                                  + "  //@ requires i > 0;\n"
                                  + "  //@ requires i < 0;\n"
                                  + "  public void mm(int i) {\n"
                                  + "     //@ assert i != i;\n"
                                  + "    }\n"
                                  + "  //@ requires i > 0;\n"
                                  + "  //@ ensures \\result > 0;\n"
                                  + "  public int mmm(int i) {\n"
                                  + "     return -i;\n"
                                  + "    }\n"
                                  + "}"
                                  ,"/tt/TestJava.java:10: warning: Invariants+Preconditions appear to be contradictory in method tt.TestJava.mm(int)",15
                                  );
        }


}
