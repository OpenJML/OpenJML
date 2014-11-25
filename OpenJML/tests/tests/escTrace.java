package tests;

import java.util.Collection;

import junit.framework.Assert;

import org.jmlspecs.openjml.JmlTree;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(ParameterizedIgnorable.class)
public class escTrace extends EscBase {
    
    public escTrace(String option, String solver) {
        super(option,solver);
    }
    
    @Override
    public void setUp() throws Exception {
        captureOutput = true;
        super.setUp();
        main.addOptions("-subexpressions");
    }
    
    /** This String declaration and assignment */
    @Test
    public void testSimpleTrace() {
        String expectedOut =""
+JmlTree.eol+"TRACE of tt.TestJava.m1(int)"
+JmlTree.eol+" \t//Declare pre-state value of formals"
+JmlTree.eol+" \t//Assume axioms"
+JmlTree.eol+" \t//Assume static final constant fields"
+JmlTree.eol+" \t//Assume field type, allocation, and nullness"
+JmlTree.eol+"/tt/TestJava.java:3:  \tassume ImplicitAssume -2147483648 <= THIS.objectTimesFinalized && THIS.objectTimesFinalized <= 2147483647; ..."
+JmlTree.eol+"\t\t\tVALUE: -2147483648\t === ???"
+JmlTree.eol+"\t\t\tVALUE: THIS\t === THIS"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_objectTimesFinalized_9235\t === ???"
+JmlTree.eol+"\t\t\tVALUE: -2147483648 <= THIS.java.lang.Object_objectTimesFinalized_9235\t === ???"
+JmlTree.eol+"\t\t\tVALUE: -2147483648 <= THIS.java.lang.Object_objectTimesFinalized_9235 && THIS.java.lang.Object_objectTimesFinalized_9235 <= 2147483647\t === ???"
+JmlTree.eol+"/tt/TestJava.java:2:  \tassume ImplicitAssume THIS.theString == null || THIS.theString instanceof java.lang.String && <:(\\typeof(THIS.theString), \\type(java.lang.String)); ..."
+JmlTree.eol+"\t\t\tVALUE: THIS\t === THIS"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_theString_6988\t === ???"
+JmlTree.eol+"\t\t\tVALUE: null\t === NULL"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_theString_6988 == null\t === ???"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_theString_6988 == null || THIS.java.lang.Object_theString_6988 instanceof java.lang.String && <:(\\typeof(THIS.java.lang.Object_theString_6988), \\type(java.lang.String))\t === ???"
+JmlTree.eol+"/tt/TestJava.java:3:  \tassume ImplicitAssume -2147483648 <= THIS.theHashCode && THIS.theHashCode <= 2147483647; ..."
+JmlTree.eol+"\t\t\tVALUE: -2147483648\t === ???"
+JmlTree.eol+"\t\t\tVALUE: THIS\t === THIS"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_theHashCode_2129\t === ???"
+JmlTree.eol+"\t\t\tVALUE: -2147483648 <= THIS.java.lang.Object_theHashCode_2129\t === ???"
+JmlTree.eol+"\t\t\tVALUE: -2147483648 <= THIS.java.lang.Object_theHashCode_2129 && THIS.java.lang.Object_theHashCode_2129 <= 2147483647\t === ???"
+JmlTree.eol+"/tt/TestJava.java:2:  \tassume ImplicitAssume THIS.owner == null || THIS.owner instanceof java.lang.Object && <:(\\typeof(THIS.owner), \\type(java.lang.Object)); ..."
+JmlTree.eol+"\t\t\tVALUE: THIS\t === THIS"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_owner_1585\t === ???"
+JmlTree.eol+"\t\t\tVALUE: null\t === NULL"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_owner_1585 == null\t === ???"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_owner_1585 == null || THIS.java.lang.Object_owner_1585 instanceof java.lang.Object && <:(\\typeof(THIS.java.lang.Object_owner_1585), \\type(java.lang.Object))\t === ???"
+JmlTree.eol+"/tt/TestJava.java:2:  \tassume ImplicitAssume THIS.privateState == null || THIS.privateState instanceof org.jmlspecs.lang.JMLDataGroup && <:(\\typeof(THIS.privateState), \\type(org.jmlspecs.lang.JMLDataGroup)); ..."
+JmlTree.eol+"\t\t\tVALUE: THIS\t === THIS"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_privateState_1345\t === ???"
+JmlTree.eol+"\t\t\tVALUE: null\t === NULL"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_privateState_1345 == null\t === ???"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_privateState_1345 == null || THIS.java.lang.Object_privateState_1345 instanceof org.jmlspecs.lang.JMLDataGroup && <:(\\typeof(THIS.java.lang.Object_privateState_1345), \\type(org.jmlspecs.lang.JMLDataGroup))\t === ???"
+JmlTree.eol+"/tt/TestJava.java:2:  \tassume ImplicitAssume THIS.objectState == null || THIS.objectState instanceof org.jmlspecs.lang.JMLDataGroup && <:(\\typeof(THIS.objectState), \\type(org.jmlspecs.lang.JMLDataGroup)); ..."
+JmlTree.eol+"\t\t\tVALUE: THIS\t === THIS"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_objectState_1211\t === ???"
+JmlTree.eol+"\t\t\tVALUE: null\t === NULL"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_objectState_1211 == null\t === ???"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_objectState_1211 == null || THIS.java.lang.Object_objectState_1211 instanceof org.jmlspecs.lang.JMLDataGroup && <:(\\typeof(THIS.java.lang.Object_objectState_1211), \\type(org.jmlspecs.lang.JMLDataGroup))\t === ???"

+JmlTree.eol+" \t//Assume parameter type, allocation, and nullness"
+JmlTree.eol+"/tt/TestJava.java:3:  \tassume ImplicitAssume -2147483648 <= i && i <= 2147483647;"
+JmlTree.eol+"\t\t\tVALUE: -2147483648\t === ???"
+JmlTree.eol+"\t\t\tVALUE: i_81\t === 2"
+JmlTree.eol+"\t\t\tVALUE: -2147483648 <= i_81\t === ???"
+JmlTree.eol+"\t\t\tVALUE: -2147483648 <= i_81 && i_81 <= 2147483647\t === ???"
+JmlTree.eol+" \t//Assume invariants for java.lang.Object"
+JmlTree.eol+" \t//Assume invariants for tt.TestJava"
+JmlTree.eol+" \t//Assume Preconditions"
+JmlTree.eol+" \t//try..."
+JmlTree.eol+" \t//Method Body"
+JmlTree.eol+"/tt/TestJava.java:4:  \tint j = 5"
+JmlTree.eol+"\t\t\tVALUE: 5\t === 5"
+JmlTree.eol+"\t\t\tVALUE: j\t === 5"
+JmlTree.eol+"/tt/TestJava.java:5:  \tj = j + i"
+JmlTree.eol+"\t\t\tVALUE: j\t === 5"
+JmlTree.eol+"\t\t\tVALUE: i\t === 2"
+JmlTree.eol+"\t\t\tVALUE: j + i\t === 7"
+JmlTree.eol+"\t\t\tVALUE: j = j + i\t === 7"
+JmlTree.eol+"/tt/TestJava.java:6:  \tassert Assert j != 7;"
+JmlTree.eol+"\t\t\tVALUE: j\t === 7"
+JmlTree.eol+"\t\t\tVALUE: 7\t === 7"
+JmlTree.eol+"\t\t\tVALUE: j != 7\t === false"
+JmlTree.eol+"/tt/TestJava.java:6:  Invalid assertion (Assert)"
+JmlTree.eol
+JmlTree.eol;

        main.addOptions("-method=m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ code_java_math */ public class TestJava { \n"
                
                +"  public void m1(int i) {\n"
                +"       int j = 5;\n"
                +"       j = j + i;\n"
                +"       //@ assert j != 7;\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method m1",12
                );
        String output = output();
        String error = errorOutput();
        Assert.assertEquals("",error);
        Assert.assertEquals(expectedOut,output);
    }

    // FIXME - the ??? is the trace values
    
    /** This String declaration and assignment */
    @Test
    public void testFieldTrace() {
        String expectedOut =""
+JmlTree.eol+"TRACE of tt.TestJava.m1(int)"
+JmlTree.eol+" \t//Declare pre-state value of formals"
+JmlTree.eol+" \t//Assume axioms"
+JmlTree.eol+" \t//Assume static final constant fields"
+JmlTree.eol+" \t//Assume field type, allocation, and nullness"
+JmlTree.eol+"/tt/TestJava.java:4:  \tassume ImplicitAssume -2147483648 <= THIS.objectTimesFinalized && THIS.objectTimesFinalized <= 2147483647; ..."
+JmlTree.eol+"\t\t\tVALUE: -2147483648\t === ???"
+JmlTree.eol+"\t\t\tVALUE: THIS\t === THIS"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_objectTimesFinalized_9235\t === ???"
+JmlTree.eol+"\t\t\tVALUE: -2147483648 <= THIS.java.lang.Object_objectTimesFinalized_9235\t === ???"
+JmlTree.eol+"\t\t\tVALUE: -2147483648 <= THIS.java.lang.Object_objectTimesFinalized_9235 && THIS.java.lang.Object_objectTimesFinalized_9235 <= 2147483647\t === ???"
+JmlTree.eol+"/tt/TestJava.java:2:  \tassume ImplicitAssume THIS.theString == null || THIS.theString instanceof java.lang.String && <:(\\typeof(THIS.theString), \\type(java.lang.String)); ..."
+JmlTree.eol+"\t\t\tVALUE: THIS\t === THIS"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_theString_6988\t === ???"
+JmlTree.eol+"\t\t\tVALUE: null\t === NULL"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_theString_6988 == null\t === ???"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_theString_6988 == null || THIS.java.lang.Object_theString_6988 instanceof java.lang.String && <:(\\typeof(THIS.java.lang.Object_theString_6988), \\type(java.lang.String))\t === ???"
+JmlTree.eol+"/tt/TestJava.java:4:  \tassume ImplicitAssume -2147483648 <= THIS.theHashCode && THIS.theHashCode <= 2147483647; ..."
+JmlTree.eol+"\t\t\tVALUE: -2147483648\t === ???"
+JmlTree.eol+"\t\t\tVALUE: THIS\t === THIS"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_theHashCode_2129\t === ???"
+JmlTree.eol+"\t\t\tVALUE: -2147483648 <= THIS.java.lang.Object_theHashCode_2129\t === ???"
+JmlTree.eol+"\t\t\tVALUE: -2147483648 <= THIS.java.lang.Object_theHashCode_2129 && THIS.java.lang.Object_theHashCode_2129 <= 2147483647\t === ???"
+JmlTree.eol+"/tt/TestJava.java:2:  \tassume ImplicitAssume THIS.owner == null || THIS.owner instanceof java.lang.Object && <:(\\typeof(THIS.owner), \\type(java.lang.Object)); ..."
+JmlTree.eol+"\t\t\tVALUE: THIS\t === THIS"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_owner_1585\t === ???"
+JmlTree.eol+"\t\t\tVALUE: null\t === NULL"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_owner_1585 == null\t === ???"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_owner_1585 == null || THIS.java.lang.Object_owner_1585 instanceof java.lang.Object && <:(\\typeof(THIS.java.lang.Object_owner_1585), \\type(java.lang.Object))\t === ???"
+JmlTree.eol+"/tt/TestJava.java:2:  \tassume ImplicitAssume THIS.privateState == null || THIS.privateState instanceof org.jmlspecs.lang.JMLDataGroup && <:(\\typeof(THIS.privateState), \\type(org.jmlspecs.lang.JMLDataGroup)); ..."
+JmlTree.eol+"\t\t\tVALUE: THIS\t === THIS"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_privateState_1345\t === ???"
+JmlTree.eol+"\t\t\tVALUE: null\t === NULL"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_privateState_1345 == null\t === ???"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_privateState_1345 == null || THIS.java.lang.Object_privateState_1345 instanceof org.jmlspecs.lang.JMLDataGroup && <:(\\typeof(THIS.java.lang.Object_privateState_1345), \\type(org.jmlspecs.lang.JMLDataGroup))\t === ???"
+JmlTree.eol+"/tt/TestJava.java:2:  \tassume ImplicitAssume THIS.objectState == null || THIS.objectState instanceof org.jmlspecs.lang.JMLDataGroup && <:(\\typeof(THIS.objectState), \\type(org.jmlspecs.lang.JMLDataGroup)); ..."
+JmlTree.eol+"\t\t\tVALUE: THIS\t === THIS"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_objectState_1211\t === ???"
+JmlTree.eol+"\t\t\tVALUE: null\t === NULL"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_objectState_1211 == null\t === ???"
+JmlTree.eol+"\t\t\tVALUE: THIS.java.lang.Object_objectState_1211 == null || THIS.java.lang.Object_objectState_1211 instanceof org.jmlspecs.lang.JMLDataGroup && <:(\\typeof(THIS.java.lang.Object_objectState_1211), \\type(org.jmlspecs.lang.JMLDataGroup))\t === ???"
+JmlTree.eol+"/tt/TestJava.java:4:  \tassume ImplicitAssume -2147483648 <= THIS.k && THIS.k <= 2147483647;"

+JmlTree.eol+"\t\t\tVALUE: -2147483648\t === ???"
+JmlTree.eol+"\t\t\tVALUE: THIS\t === THIS"
+JmlTree.eol+"\t\t\tVALUE: THIS.k_71\t === ???"
+JmlTree.eol+"\t\t\tVALUE: -2147483648 <= THIS.k_71\t === ???"
+JmlTree.eol+"\t\t\tVALUE: -2147483648 <= THIS.k_71 && THIS.k_71 <= 2147483647\t === ???"
+JmlTree.eol+" \t//Assume parameter type, allocation, and nullness"
+JmlTree.eol+"/tt/TestJava.java:4:  \tassume ImplicitAssume -2147483648 <= i && i <= 2147483647;"
+JmlTree.eol+"\t\t\tVALUE: -2147483648\t === ???"
+JmlTree.eol+"\t\t\tVALUE: i_95\t === 2"
+JmlTree.eol+"\t\t\tVALUE: -2147483648 <= i_95\t === ???"
+JmlTree.eol+"\t\t\tVALUE: -2147483648 <= i_95 && i_95 <= 2147483647\t === ???"
+JmlTree.eol+" \t//Assume invariants for java.lang.Object"
+JmlTree.eol+" \t//Assume invariants for tt.TestJava"
+JmlTree.eol+" \t//Assume Preconditions"
+JmlTree.eol+" \t//try..."
+JmlTree.eol+" \t//Method Body"
+JmlTree.eol+"/tt/TestJava.java:5:  \tk = 5 + i"
+JmlTree.eol+"\t\t\tVALUE: 5\t === 5"
+JmlTree.eol+"\t\t\tVALUE: i\t === 2"
+JmlTree.eol+"\t\t\tVALUE: 5 + i\t === 7"
+JmlTree.eol+"\t\t\tVALUE: k = 5 + i\t === 7"
+JmlTree.eol+"/tt/TestJava.java:6:  \tassert Assert k != 7;"
+JmlTree.eol+"\t\t\tVALUE: k\t === 7"
+JmlTree.eol+"\t\t\tVALUE: 7\t === 7"
+JmlTree.eol+"\t\t\tVALUE: k != 7\t === false"
+JmlTree.eol+"/tt/TestJava.java:6:  Invalid assertion (Assert)"
+JmlTree.eol
+JmlTree.eol;
        main.addOptions("-method=m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ code_java_math */ public class TestJava { \n"
                +"       int k;\n"
                
                +"  public void m1(int i) {\n"
                +"       k = 5 + i;\n"
                +"       //@ assert k != 7;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method m1",12
                );
        String output = output();
        String error = errorOutput();
        Assert.assertEquals("",error);
        Assert.assertEquals(expectedOut,output);
    }

}