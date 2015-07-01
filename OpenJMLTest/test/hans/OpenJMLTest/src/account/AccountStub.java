package account;

public class AccountStub implements IAccount
{
    private  int bal;    
    
    public AccountStub(int amt) {
      bal = amt;
    }
 
    public int balance()
    {
      return bal;
    }
    
    public void withdraw (int amt) { 
      bal -= amt; 
    }
    
    // used for JML annotation only (not public)
    int getBalance() {
    	return bal;
    }
}