package tests;

import java.util.ArrayList;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class escnew2 extends EscBase {

    String option;
    
    public escnew2(String option) {
        this.option = option;
    }
    
    @Parameters
    static public  Collection<String[]> datax() {
        Collection<String[]> data = new ArrayList<String[]>(10);
        data.add(new String[]{"-boogie"}); 
        data.add(new String[]{"-newesc"}); 
        //data.add(new String[]{null}); 
        //data.add(new String[]{"-rac"}); 
        return data;
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        setOption(option);
        main.addOptions(option);
        main.addOptions("-noPurityCheck");
        //options.put("-jmlverbose",   "");
        //options.put("-method",   "m2bad");
        //options.put("-showbb",   "");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //options.put("-showce",   "");
        //options.put("-trace",   "");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }


    
    @Test
    public void testBreak() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures i == 0 ==> \\result == 6; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n"
                +"  public int m1good(int i) throws Exception {\n"
                +"      int k = 0;\n"
                +"       out: {\n"
                +"        in: { if (i ==1) break in;\n"
                +"              if (i ==2) break out;\n"
                +"              k=5;\n"
                +"        } k++; \n"
                +"       } \n"
                +"      return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 7; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n"
                +"  public int m1bad(int i) throws Exception {\n" // Line 19
                +"      int k = 0;\n"
                +"       out: {\n"
                +"        in: { if (i ==1) break in;\n"
                +"              if (i ==2) break out;\n"
                +"              k=5;\n"
                +"        } k++; \n"
                +"       } \n"
                +"      return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 6; \n"
                +"  //@ ensures i == 1 ==> \\result == 2; \n"
                +"  //@ ensures i == 2 ==> \\result == 0; \n"
                +"  public int m2bad(int i) throws Exception {\n"
                +"      int k = 0;\n"
                +"       out: {\n"
                +"        in: { if (i ==1) break in;\n"
                +"              if (i ==2) break out;\n"
                +"              k=5;\n"
                +"        } k++; \n"
                +"       } \n"
                +"      return k;\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 ==> \\result == 6; \n"
                +"  //@ ensures i == 1 ==> \\result == 1; \n"
                +"  //@ ensures i == 2 ==> \\result == 9; \n"
                +"  public int m3bad(int i) throws Exception {\n"
                +"      int k = 0;\n"
                +"       out: {\n"
                +"        in: { if (i ==1) break in;\n"
                +"              if (i ==2) break out;\n"
                +"              k=5;\n"
                +"        } k++; \n"
                +"       } \n"
                +"      return k;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",7
                ,"/tt/TestJava.java:16: warning: Associated declaration",7
                ,"/tt/TestJava.java:40: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",7
                ,"/tt/TestJava.java:30: warning: Associated declaration",7
                ,"/tt/TestJava.java:53: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",7
                ,"/tt/TestJava.java:44: warning: Associated declaration",7
                );
    }
    

}
