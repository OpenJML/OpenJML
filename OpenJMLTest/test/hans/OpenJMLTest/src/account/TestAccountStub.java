package account;

import org.jmlspecs.utils.JmlAssertionError;

import unitTest_Remove.TestCase;

public class TestAccountStub extends TestCase
{

  public TestAccountStub(String name)
  {
    super(name);
  }
  
  public void test (int i) 
  { 
    switch (i) { 
      case 1:
        new AccountStub(0); break; 
      case 2:
        new AccountStub(100); break;
      case 3: 
        try { new AccountStub(-1); assert false; }
        catch (JmlAssertionError e){}; break;
      
      case 4: 
        new AccountStub(100).balance(); 
        break;
      case 5: 
        new AccountStub(0).balance();  
        break;
      case 6:
        Account acc = new Account(300);
        assert acc.balance() == 300;
        break;
      default: break;
    }
  }
  
  public static final int testCount = 9; 
}
