package tests;

public class escold extends escnew {

    protected void setUp() throws Exception {
        super.setUp();
        options.put("-newesc",null);
        options.put("-nullableByDefault",null);
        options.put("-nonnullByDefault","");
    }
    
    public void testAssignable2() {
        // FIXME - skip until problem in escnew is fixed
    }
    
    public void testNullThrow() {
        // FIXME - skip until problem in escnew is fixed
    }
    
    public void testUnreachable() {
        // FIXME - skip until problem in escnew is fixed
    }
    
    public void testNullSynchronized() {
        // old esc did not check for this problem
    }
    
    public void testPostcondition4() {
        // old esc did not check for this problem
    }
    
    public void testAssignable5() {
        noAssociatedDeclaration = true;
        super.testAssignable5();
    }
    
    public void testAssignable1() {
        noAssociatedDeclaration = true;
        super.testAssignable5();
    }
    
    public void testAssignable3() {
        noAssociatedDeclaration = true;
        super.testAssignable5();
    }
    
    public void testAssignable4() {
        noAssociatedDeclaration = true;
        super.testAssignable5();
    }
    
    public void testAssignable6() {
        noAssociatedDeclaration = true;
        super.testAssignable5();
    }
}
