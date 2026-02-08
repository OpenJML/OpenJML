package stack;


public interface Stack{
	/*@
	  @ public invariant 0 <= count <= items.length;
	  @*/

	//-RAC@ public instance model int count;
	//-RAC@ public instance model int[] items;
	
	//-RAC@ ensures \result == count;
	//@ strictly_pure
	//@ helper
	int count();

	//@ requires 1 <= i <= count;
	//-RAC@  ensures \result == items[i-1];
	//@ strictly_pure
	int itemAt (int i);

	//@ ensures \result==(count==0);
	//@ strictly_pure
	boolean isEmpty ( );

	//-RAC@ assignable count, items[*];
	//@ ensures (\result && count() == \old(count) + 1) || (!\result && count() == \old(count));
	//@ ensures \result ==> item==(top());
    //@ ensures (\forall int i; 0 <= i < \old(count()); items[i] == \old(items[i]));
    //@ ensures (\forall int i; 1 <= i <= \old(count()); itemAt(i)==items[i-1]);
    //@ ensures (\forall int i; 1 <= i <= \old(count()); itemAt(i)==\old(itemAt(i)));
	boolean push(int item);

	//@ requires count() >= 1;
	//@ ensures \result == itemAt(count);
	//@ pure
	int top();

	//@ writes count, items;
	//@ ensures \result == (\old(count) != 0);
	//@ ensures !\result ==> (count == 0 && \old(count) ==0);
	boolean remove ( );

}
