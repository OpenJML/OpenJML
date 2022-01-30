package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class matchClasses  extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        useSystemSpecs = true;
        super.setUp();
        main.addOptions("-no-purityCheck");
        //main.addOptions("-jmldebug");
    }

    /** Test something very simple with no errors*/
    @Test public void testSimple() {
        helpTCF("$A/A.java",
                "public class A {  } class B {}");
    }
    
    @Test public void testDuplicate() {
        helpTCF("$A/A.java",
                "public class A {  } class A {}"
                ,"/$A/A.java:1: error: duplicate class: A",21
                ,"/$A/A.java:1: error: Associated declaration: /$A/A.java:1:",8
                );
    }
    
    @Test public void testModel() {
        helpTCF("$A/A.java",
                "public class A {  } /*@ model class B {} */"
                );
    }
    
    @Test public void testModelB() {
        helpTCF("$A/A.java",
                "public class A {  } /*@ class B {}*/ "
                ,"/$A/A.java:1: error: A method or type declaration within a JML annotation must be model: B",25
                );
    }
    
    @Test public void testModelC() {
        helpTCF("$A/A.java",
                "public class A {  } /*@ model */ class B {}"
                ,"/$A/A.java:1: error: A Java declaration (not within a JML annotation) may not be either ghost or model: B",34// FIXME - would prefer this is 25
                );
    }
    
    @Test public void testModelDup() {
        helpTCF("$A/A.java",
                "public class A {  } /*@ model  class A {} */"
                ,"/$A/A.java:1: error: duplicate class: A",32
                ,"/$A/A.java:1: error: Associated declaration: /$A/A.java:1:",8
                );
    }

    @Test public void testJmlSimple() {
        addMockFile("$A/A.jml", "public class A {  } class B {}");
        helpTCF("$A/A.java",
                "public class A {  } class B {}");
    }
    
    @Test public void testJmlNoMatch() {
        addMockFile("$A/A.jml", "public class A {  } class B {}");
        helpTCF("$A/A.java",
                "public class A {  } "
                ,"/$A/A.jml:1: error: There is no class to match this Java declaration in the specification file: B",21
                );
    }
    
    @Test public void testJmlExtra() {
        addMockFile("$A/A.jml", "public class A {  } ");
        helpTCF("$A/A.java",
                "public class A {  } class B {}"
                );
    }
    
    @Test public void testJmlDupIgnored() {
        addMockFile("$A/A.jml", "public class A {  } ");
        helpTCF("$A/A.java",
                "public class A {  } /*@ model class A {} */");
    }
    
    @Test public void testJmlDup() {
        addMockFile("$A/A.jml", "public class A {  } class A {}");
        helpTCF("$A/A.java",
                "  public class A {  } "
                ,"/$A/A.jml:1: error: duplicate class: A",21
                ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:1:",8
                );
    }
    
    @Test public void testJmlDup2() {
        addMockFile("$A/A.jml", "public class A {  } \n/*@ model class A {} */");
        helpTCF("$A/A.java",
                "  public class A {  } "
                ,"/$A/A.jml:2: error: This JML class declaration conflicts with an existing Java class with the same name: A",11
                ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:2:",8
                );
    }
    
    @Test public void testJmlDup3() {
        addMockFile("$A/A.jml", "public class A {  } \n/*@ class A {} */");
        helpTCF("$A/A.java",
                "public class A {  } "
                ,"/$A/A.jml:2: error: This JML class declaration conflicts with an existing Java class with the same name: A",5
                ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:2:",8
                );
    }
    
    @Test public void testJmlMatch() {
        addMockFile("$A/A.jml", "public class A {  } /*@ model class B {} */");
        helpTCF("$A/A.java",
                "  public class A {  } class B {}"
                ,"/$A/A.jml:1: error: This JML class declaration conflicts with an existing Java class with the same name: B",31
                ,"/$A/A.java:1: error: Associated declaration: /$A/A.jml:1:",23 
                );
    }
    
    @Test public void testJmlModel() {
        addMockFile("$A/A.jml", "public class A {  } /*@ model class B {} */");
        helpTCF("$A/A.java",
                "public class A {  } "
                );
    }
    
    @Test public void testJmlModel2() {
        addMockFile("$A/A.jml", "public class A {  } /*@  class B {} */");
        helpTCF("$A/A.java",
                "public class A {  } "
                ,"/$A/A.jml:1: error: A method or type declaration within a JML annotation must be model: B",26
                );
    }
    
    @Test public void testJmlModel3() {
        addMockFile("$A/A.jml", "public class A {  } /*@ model */ class B {} ");
        helpTCF("$A/A.java",
                "public class A {  } "
                ,"/$A/A.jml:1: error: There is no class to match this Java declaration in the specification file: B",34
                // The erroneous class is deleted, so no warning about the model modifier
                );
    }
    
    @Test public void testJmlModel4() {
        helpTCF("$A/A.java",
                "public class A {  } /*@ model */ class B {} "
                ,"/$A/A.java:1: error: A Java declaration (not within a JML annotation) may not be either ghost or model: B",34 // FIXME - better as 25
                );
    }
    
    @Test public void testSimpleField() {
        helpTCF("$A/A.java",
                "public class A { int j; } ");
    }
    
    @Test public void testSimpleFieldDup() {
        helpTCF("$A/A.java",
                "public class A { int j; int j; } "
                ,"/$A/A.java:1: error: variable j is already defined in class A",29
                );
    }
    
    @Test public void testSimpleFieldModelDup() {
        helpTCF("$A/A.java",
                "public class A { int j; \n/*@ model int j; */ } "
                ,"/$A/A.java:2: error: variable j is already defined in class A",15
                );
    }
    
    @Test public void testSimpleFieldModelDup2() {
        helpTCF("$A/A.java",
                "public class A { int j; \n/*@ model */ int j;} "
                ,"/$A/A.java:2: error: variable j is already defined in class A",18
                ,"/$A/A.java:2: error: A Java declaration (not within a JML annotation) may not be either ghost or model: A.j",18 // FIXME: position should be on model
                );
    }
    
    @Test public void testSimpleFieldModelDup3() {
        helpTCF("$A/A.java",
                "public class A { int j; \n/*@  int j; */} "
                ,"/$A/A.java:2: error: variable j is already defined in class A",10
                ,"/$A/A.java:2: error: A declaration within a JML annotation must be either ghost or model: A.j",10 // FIXME: Why this error if we already have marked it dup
                );
    }
    
    @Test public void testJmlSimpleField() {
        addMockFile("$A/A.jml", "public class A { int j; }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                );
    }
    
    @Test public void testJmlSimpleFieldTypeError() {
        addMockFile("$A/A.jml", "public class A { double j; }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                ,"/$A/A.jml:1: error: Type of field j in specification differs from type in source/binary: double vs. int",18
                ,"/$A/A.java:1: error: Associated declaration: /$A/A.jml:1:",22
                );
    }
    
    @Test public void testJmlSimpleFieldDup() {
        addMockFile("$A/A.jml", "public class A { /*@ model int j; */ }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                ,"/$A/A.jml:1: error: This JML field declaration conflicts with an existing field with the same name: A.j",32
                ,"/$A/A.java:1: error: Associated declaration: /$A/A.jml:1:",22
                );
    }
    
    @Test public void testJmlSimpleFieldDup2() {
        addMockFile("$A/A.jml", "public class A { int j; /*@ model int j; */ }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                ,"/$A/A.jml:1: error: This JML field declaration conflicts with an existing field with the same name: A.j",39
                ,"/$A/A.java:1: error: Associated declaration: /$A/A.jml:1:",22
                );
    }
    
    @Test public void testJmlSimpleFieldDup4() {
        addMockFile("$A/A.jml", "public class A { int j; \n/*@ model */ int j; }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
           //     ,"/$A/A.jml:2: error: A Java field declaration must not be marked either ghost or model: j (owner: A)",5
                ,"/$A/A.jml:2: error: This specification declaration of field A.j has the same name as a previous field declaration",18
                ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:2:",22
                );
    }
    
    @Test public void testJmlSimpleFieldDup3() {
        addMockFile("$A/A.jml", "public class A { \n/*@ int jjjj; */ }");
        helpTCF("$A/A.java",
                "public class A { int jjjj; } "
        //        ,"/$A/A.jml:2: error: A JML field declaration must be marked either ghost or model: jjjj (owner: A)",9
                ,"/$A/A.jml:2: error: This JML field declaration conflicts with an existing field with the same name: A.jjjj",9
                ,"/$A/A.java:1: error: Associated declaration: /$A/A.jml:2:",22
                );
    }
    
    @Test public void testJmlSimpleFieldNoMatch() {
        addMockFile("$A/A.jml", "public class A { int k; }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                ,"/$A/A.jml:1: error: There is no field to match this Java declaration in the specification file: A.k",22
                );
    }
    
    @Test public void testJmlSimpleFieldNoMatchOK() {
        addMockFile("$A/A.jml", "public class A { /*@ model int k; */ }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                );
    }
    
    @Test public void testJmlSimpleFieldNoMatch2() {
        addMockFile("$A/A.jml", "public class A { /*@  int k; */ }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                ,"/$A/A.jml:1: error: A declaration within a JML annotation must be either ghost or model: A.k",27
                );
    }
    
    @Test public void testJmlSimpleFieldNoMatch3() {
        addMockFile("$A/A.jml", "public class A { /*@ model */ int k; }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
      //  		,"/$A/A.jml:1: error: A Java field declaration must not be marked either ghost or model: k (owner: A)",22
                ,"/$A/A.jml:1: error: There is no field to match this Java declaration in the specification file: A.k",35
                );
    }
    
    @Test public void testSimpleMethod() {
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;} } ");
    }
    
    @Test public void testSimpleMethodDup() {
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;} int j(){return 0;} } "
                ,"/$A/A.java:1: error: method j() is already defined in class A",41
                );
    }
    
    @Test public void testSimpleMethodModelDup() {
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  \n/*@ model int j(){return 0;}  */ } "
                ,"/$A/A.java:2: error: method j() is already defined in class A",15 // TODO: Be nice to have an associated decl
                );
    }
    
    @Test public void testSimpleMethodModelDup2() {
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  \n/*@ model */ int j(){return 0;} } "
                ,"/$A/A.java:2: error: method j() is already defined in class A",18  // TODO: Be nice to have an associated decl
                ,"/$A/A.java:2: error: A Java method declaration must not be marked model: A.j()",5
                );
    }
    
    @Test public void testSimpleMethodModelDup3() {
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  \n/*@ int j(){return 0;}  */} "
                ,"/$A/A.java:2: error: method j() is already defined in class A",9
                ,"/$A/A.java:2: error: A JML method declaration must be marked model: A.j()",9 
                );
    }
    
    @Test public void testJmlSimpleMethod() {
        addMockFile("$A/A.jml", "public class A { int j();  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                );
    }
    
    @Test public void testJmlSimpleMethodWithBody() {
        addMockFile("$A/A.jml", "public class A { int j(){return 0;}  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:1: error: The specification of the method A.j() must not have a body",25
                );
    }
    
    @Test public void testJmlSimpleMethodTypeError() {
        addMockFile("$A/A.jml", "public class A { double j();  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:1: error: The return types of method A.j() are different in the specification and java files: double vs. int",18
// FIXME - should have an associated declaration
                );
    }
    
    @Test public void testJmlSimpleMethodTypeError2() {
        addMockFile("$A/A.jml", "public class A { int j(int k);  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:1: error: There is no method to match this Java declaration in the specification file: A.j(int)",22
 //               		+ "\n      A has j()",22
                );
    }
    
    @Test public void testJmlSimpleMethodDup() {
        addMockFile("$A/A.jml", "public class A { /*@ model int j(){return 0;}  */ }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:1: error: This JML method declaration conflicts with an existing method with the same signature: A.j()",32
                ,"/$A/A.java:1: error: Associated declaration: /$A/A.jml:1:",22
                );
    }
    
    @Test public void testJmlSimpleMethodDup2() {
        addMockFile("$A/A.jml", "public class A { int j(); \n/*@ model int j(){return 0;}  */ }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:2: error: This JML method declaration conflicts with an existing method with the same signature: A.j()",15
                ,"/$A/A.java:1: error: Associated declaration: /$A/A.jml:2:",22
                );
    }
    
    @Test public void testJmlSimpleMethodDup4() {
        addMockFile("$A/A.jml", "public class A { int j();  \n/*@ model */ int j(){return 0;}  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;} } "
                ,"/$A/A.jml:2: error: Method j() is already defined in class A",18
                ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:2:",22
                );
    }
    
    @Test public void testJmlSimpleMethodDup5() {
        addMockFile("$A/A.jml", "public class A { int j();  \n/*@ model */ int j(int k){return 0;}  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;} } "
                ,"/$A/A.jml:2: error: There is no method to match this Java declaration in the specification file: A.j(int)",18
       //         		+ "\n      A has j()",18
                );
    }
    
    @Test public void testJmlSimpleMethodDup3() {
        addMockFile("$A/A.jml", "public class A { \n/*@ int j();  */ }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:2: error: This JML method declaration conflicts with an existing method with the same signature: A.j()",9
                ,"/$A/A.java:1: error: Associated declaration: /$A/A.jml:2:",22
                );
    }
    
    @Test public void testJmlSimpleMethodNoMatch() {
        addMockFile("$A/A.jml", "public class A { int k(){return 0;}  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:1: error: There is no method to match this Java declaration in the specification file: A.k()",22
                );
    }
    
    @Test public void testJmlSimpleMethodNoMatchOK() {
        addMockFile("$A/A.jml", "public class A { /*@ model int k();  */ }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                );
    }
    
    @Test public void testJmlSimpleMethodNoMatch2() {
        addMockFile("$A/A.jml", "public class A { \n/*@  int k(){return 0;}  */ }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:2: error: A JML method declaration must be marked model: A.k()",10 
                );
    }
    
    @Test public void testJmlSimpleMethodNoMatch3() {
        addMockFile("$A/A.jml", "public class A { \n/*@ model */ int k(){return 0;}  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:2: error: There is no method to match this Java declaration in the specification file: A.k()",18
                );
    }
    
    @Test public void testJmlMethodIgnored() {
        addMockFile("$A/A.jml", "public class A { \n/*@ model int k(){return 0;} */ }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;} \n/*@ model int j(); */ } "
                );
    }
    
    @Test public void testJmlFieldIgnored() {
        addMockFile("$A/A.jml", "public class A { \n int j; /*@ model int k; */ }");
        helpTCF("$A/A.java",
                "public class A { int j; \n/*@ model int j; */ } "
                );
    }
    

    // FIXME - need all these corresponding tests for nested classes
}

