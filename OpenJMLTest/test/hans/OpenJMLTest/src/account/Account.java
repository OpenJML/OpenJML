
package account;

public class Account 
{
  private final int MAX_BALANCE = 300;
  private int bal;
  
  public Account(int amt) {
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
  
  //used for JML annotation only (not public)
  int getMaxBalance() {
  	return MAX_BALANCE;
  }
}

