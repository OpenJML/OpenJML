public interface Date {

   /*@ model instance int year = 1;
       model instance int month = 1;
       model instance int day = 1; @*/

    //@ ensures \result == this.month;
    /*@ pure @*/ int month();

    //@ ensures \result == this.day;
    /*@ pure @*/ int day();

    //@ ensures \result == this.year;
    /*@ pure @*/ int year();

   /*@ ensures \result == (this.year == birth.year) && this.month == birth.month && this.day == birth.day; @*/
   public /*@ pure @*/ boolean equals(Date birth);

}
