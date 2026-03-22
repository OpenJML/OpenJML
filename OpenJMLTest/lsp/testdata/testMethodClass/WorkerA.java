/**
 * First implementation of IWorker.  Also declares a non-interface method
 * {@code doubleWork} that is NOT an override of any IWorker method, making it
 * available as a test case for cross-file method rename without inheritance
 * complications.
 */
public class WorkerA implements IWorker {

    private int count = 0;

    //@ requires amount >= 0;
    //@ ensures \result == amount * 2;
    public int doWork(int amount) {
        count += amount;
        return amount * 2;
    }

    //@ ensures \result != null;
    public String getStatus() {
        return "A:" + count;
    }

    /**
     * Doubles the amount and returns it.
     * This method is NOT declared in IWorker — it is WorkerA-specific.
     * It can therefore be renamed without breaking any interface contract.
     *
     * //@ requires amount >= 0;
     * //@ ensures \result == 2 * amount;
     */
    public int doubleWork(int amount) {
        return 2 * amount;
    }
}
