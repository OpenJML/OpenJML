interface Counter {
    //@ public model instance int counter;

    /*@ requires counter < Integer.MAX_VALUE;
      @ assigns counter;
      @ ensures counter == 5;
     */
    void increment();
}

class CounterImpl implements Counter {
    //@ spec_public
    private int internalCounter = 0; //@ in counter;

    //@ public represents counter = internalCounter;

    @Override
    public void increment() {
        internalCounter++;
    }
}
