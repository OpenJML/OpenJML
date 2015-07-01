package account;

import org.jmlspecs.utils.JmlAssertionError;

import unitTest_Remove.TestCase;

public class TestAccount extends TestCase
{  
  public TestAccount(String name)
  {
    super(name);
  }
  
  public void test (int i) 
  {
    switch (i) { 
      
      case 1:
        new Account(1); break;
      case 2:
        new Account(100); break;
      case 3: 
        try { new Account(0); assert false; }  
        catch (JmlAssertionError e) { }; 
        break;  
        
      case 4: 
        new Account(100).balance(); break; 
        
      case 5: 
        try { Account acc = new Account(300);
              acc.withdraw(0); assert false;}
        catch (JmlAssertionError e){ }; 
        break;        
      case 6: 
        new Account(300).withdraw(1); break;
      case 7: 
        new Account(300).withdraw(100); break;
      case 8: 
        new Account(300).withdraw(300); break;
      case 9: 
        try { new Account(300).withdraw(301); assert false;}
        catch (JmlAssertionError e) { } break;      
     
      default: break;
    }
  }
  
  public static final int testCount = 9; 
}
