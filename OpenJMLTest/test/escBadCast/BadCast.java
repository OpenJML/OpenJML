// From DMZ - 10/16/2013

public class BadCast {
    public int my_dollars;
    public int my_cents;
    
    public boolean equals(final Object the_other) {
        boolean result = false;
        
        if (this == the_other) {
          result = true;
          // @ show this, the_other, result;
        } else if (the_other != null && the_other.getClass() == getClass()) {
          final BadCast other_cash = (BadCast) the_other;
          //@ show other_cash.my_dollars, other_cash.my_cents, my_dollars, my_cents;
          result = other_cash.my_dollars == my_dollars && 
                   other_cash.my_cents == my_cents;
        	result = false;
        }
        //@ show this, the_other, the_other.getClass(), getClass(), this==the_other, \typeof(this) == \type(Object), result;
        return result;
      }
}

class BadCast2 {
    public int my_dollars;
    public int my_cents;

    public boolean equalsx(final Object the_other) {
        boolean result = false;
        
        if (this == the_other) {
          result = true;
        } else if (the_other != null && the_other instanceof BadCast2) {
          final BadCast2 other_cash = (BadCast2) the_other;
          result = other_cash.my_dollars == my_dollars && 
                   other_cash.my_cents == my_cents;
        }
        
        return result;
      }
}