 class BankAccount {
    //@ public model instance int balance_;
    //@ public instance invariant balance_ >= 0; 
}

 interface BankAccount2 {
	    //@ public model instance int balance_;
	    //@ public instance invariant balance_ >= 0; 
	}

public class RegularBankAccount extends BankAccount {
    private /*@spec_public*/ int balance;
    //@ represents balance_ = balance;

    public RegularBankAccount()
    {
        balance = 0;
    }
}

 class RegularBankAccount2 implements BankAccount2 {
    private /*@spec_public*/ int balance;
    //@ represents balance_ = balance;

    public RegularBankAccount2()
    {
        balance = 0;
    }
}