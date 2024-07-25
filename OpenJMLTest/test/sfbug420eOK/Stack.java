package stack;


public interface Stack{
	/*@
	  @public invariant count()>=0;
	  @*/

	//-RAC@ model instance public \datagroup state;
	//-RAC@ public instance model int max;
	//-RAC@ public instance model int count; //@ in state;
	
	//-RAC@ ensures \result == count;
	//@ pure
	//@ helper
	int count();

	//@ requires 1 <= i <= count();
	//@ pure
	int itemAt (int i);

	//@ ensures \result==(count()==0);
	//@ pure
	boolean isEmpty ( );

	//-RAC@ assignable state;  // FIXME - no way to say that internalCount[*] may change
	//-RAC@ requires count() < max;
	//@ ensures \result ==> count() == \old(count()) + 1;
	// @ ensures \result ==> item==(top());
	//@ ensures (\forall int i; 1 <= i <=\old(count()); itemAt(i)==\old(itemAt(i)));
	boolean push(int item);

	//@ requires count() > 0;
	//@ ensures \result == itemAt(count());
	//@ pure
	int top();

	boolean remove ( );

}
