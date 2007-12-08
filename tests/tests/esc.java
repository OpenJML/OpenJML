package tests;

public class esc extends EscBase {

    protected void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        //options.put("-jmlverbose",   "");
        //options.put("-noInternalSpecs",   "");
    }

    public void testJava() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static boolean bstatic;\n"
                +"  boolean binstance;\n"
                +"  boolean binstance2;\n"
                +"  /*@ non_null */ Object o;\n"
                +"  //@static invariant bstatic;\n"
                +"  //@invariant binstance;\n"
                +"  //@initially binstance2;\n"
                +"  //@constraint binstance2 == \\old(binstance);\n"
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
                +"  public /*@non_null*/ Object inst(int ii) { binstance = ii == 0; o = null; return null; }\n"
                +"}"
                );
    }
}

