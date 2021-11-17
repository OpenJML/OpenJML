package stack;

public class StackImpl implements Stack {
		
	/*@ spec_public */ private int maxSize = 50; //@ in max;
	/*@ spec_public */ private int[] internalStack;
	/*@ spec_public */ private int stackCounter; //-RAC@ in count;
	
	//@ public represents count = stackCounter;
	//@ public represents max = maxSize;
	//@ public invariant internalStack.length == max;

	@SuppressWarnings("unchecked")
	public StackImpl() {
		internalStack = new int[maxSize];
		stackCounter = 0;
	}
	
	//@ also ensures \result == stackCounter;
	//@ pure
	//@ helper
	public int count() {
		return stackCounter;
	}

	//@ also
	//@ requires 1 <= i <= count();
	//@ ensures \result == internalStack[i-1];
	//@ pure helper
	public int itemAt(int i) {
		return internalStack[i-1];
	}

	//@ pure helper
	public boolean isEmpty() {
		return internalStack.length == 0;
	}

	public boolean push(int item) {
		if(stackCounter + 1 > maxSize) return false;
		internalStack[stackCounter] = item; // FIXME - why does this not violate the frame condition
		stackCounter = stackCounter + 1;
		// @ assert item == internalStack[stackCounter-1];
		// @ assert item==(top()); // FIXME - uncommenting this makes a postcondition fail - but the equlaivalent line above is OK
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
		Stack s = new StackImpl();
		s.push(2);
		s.push(2);
		s.push(2);
		System.out.println(s.itemAt(1));
		System.out.println(s.itemAt(2));
		System.out.println(s.itemAt(3));
	}

}
