package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.ParameterizedWithNames;


@RunWith(ParameterizedWithNames.class)
public class esclambdas extends EscBase {

    public esclambdas(String options, String solver) {
        super(options,solver);
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
    
    @Test
    public void testIterable1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public static class M {\n"
                +"    public int i ;\n"
                +"    public void bump() { i++; }\n"
                +"  }\n"
                
                +"  public void m1(Iterable<M> a) {\n"
                +"    a.forEach(M::bump);\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    @Test
    public void testIterable2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public static class M {\n"
                +"    public int i ;\n"
                +"    public void bump() { i++; }\n"
                +"  }\n"
                
                +"  public void m1(Iterable<M> a) {\n"
                +"    a.forEach(m->m.bump());\n"
                +"  }\n"
                                
                +"}"
                );
    }

 
}
