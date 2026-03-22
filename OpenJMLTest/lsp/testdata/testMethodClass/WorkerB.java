/**
 * Second implementation of IWorker.  The rename of a method in IWorker or
 * WorkerA must also update WorkerB's implementation.
 */
public class WorkerB implements IWorker {

    private int count = 0;

    //@ requires amount >= 0;
    public int doWork(int amount) {
        count += amount;
        return amount;
    }

    public String getStatus() {
        return "B:" + count;
    }
}
