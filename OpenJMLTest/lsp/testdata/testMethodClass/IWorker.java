/**
 * Interface whose method names are used to test go-to-definition, find-references,
 * and rename across multiple implementing classes.
 */
public interface IWorker {

    //@ ensures \result >= 0;
    int doWork(int amount);

    //@ ensures \result != null;
    String getStatus();
}
