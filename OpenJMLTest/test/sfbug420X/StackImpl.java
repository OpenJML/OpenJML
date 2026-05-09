package stack;

public class StackImpl implements Stack {
		
	/*@ spec_public */ private int maxSize = 50;
	/*@ spec_public */ private int[] internalStack; //@ in items;
	/*@ spec_public */ private int stackCounter; //@ in count;
	//@ public represents count = stackCounter;
	//@ public represents items = internalStack;
	//@ public invariant maxSize == 50;
	//@ public invariant stackCounter <= internalStack.length;
	//@ public invariant internalStack.length >= maxSize;
	
	//@ ensures count == 0;
	//@ ensures stackCounter == 0;
	//@ ensures count() == 0;
	@SuppressWarnings("unchecked")
	public StackImpl() {
		internalStack = new int[maxSize];
		stackCounter = 0;
	}
	
	//@ also ensures \result == stackCounter;
	//@ strictly_pure
	//@ helper
	public int count() {
		return stackCounter;
	}

	//@ also requires 1 <= i <= count();
    //@ ensures \result == internalStack[i-1];
	//@ strictly_pure
	public int itemAt(int i) {
		return internalStack[i-1];
	}

	//@ strictly_pure
	public boolean isEmpty() {
		return stackCounter == 0;
	}

	//@ also 
	//@   writes count, internalStack[*]; 
	//@   ensures \old(stackCounter < maxSize) <==> \result;
	//@   ensures \result ==> stackCounter == \old(stackCounter) + 1;
	//@   ensures !\result ==> stackCounter == \old(stackCounter);
	//@   ensures \result ==> internalStack[stackCounter-1] == item;
	public boolean push(int item) {
	    //@ assert (\forall int i; 1 <= i <= \old(count()); itemAt(i)==items[i-1]);
	    if(stackCounter >= maxSize) {
	        //@ assert (\forall int i; 1 <= i <= \old(count); itemAt(i)==items[i-1]);
	        return false;
	    }
		internalStack[stackCounter] = item;
		stackCounter++;
		return true;
	}

	public int top() {
		return internalStack[stackCounter-1];
	}

	public boolean remove() {
		if(stackCounter == 0) return false;
				stackCounter--;
		return true;
	}
	
	public static void main(String[] args) {
		Stack s = new StackImpl(); // Here s is typed as Stack so we only know the specs of Stack.push
		//@ assert s.count == 0;
		boolean b1 = s.push(2);
        //@ assert b1 ==> s.count == 1;
		boolean b2 = s.push(2);
        //@ assert b2 ==> s.count == 2;
		boolean b3 = s.push(2);
        //@ assert b3 ==> s.count() == 3;
		if (!(b1 && b2 && b3)) return;
		//@ assert s.count == 3;
//		System.out.println(s.itemAt(1));
//		System.out.println(s.itemAt(2));
//		System.out.println(s.itemAt(3));
	}

	public static void main1(String[] args) {
		StackImpl s = new StackImpl(); // Here s is a StackImpl and we know the StackImpl specs of push
		//@ assert s.count == 0;
		boolean b1 = s.push(2);
		//@ assert b1 && s.count == 1;
		boolean b2 = s.push(2);
		//@ assert b2 && s.count == 2;
		boolean b3 = s.push(2);
		//@ assert b3 && s.count == 3;
		//@ show b1, b2, b3, s.maxSize, s.stackCounter;
		//@ assert b1 && b2 && b3;
		//@ assert s.count() == 3;
		//@ assert s.count == 3;
		//@ assert s.stackCounter == 3;
//		System.out.println(s.itemAt(1));
//		System.out.println(s.itemAt(2));
//		System.out.println(s.itemAt(3));
	}

}
