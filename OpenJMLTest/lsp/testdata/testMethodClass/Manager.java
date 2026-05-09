/**
 * Consumer of IWorker.  Holds a reference to an IWorker for interface-dispatch
 * calls and also a concrete WorkerA reference for direct-dispatch calls.
 *
 * <p>Having a concrete WorkerA field ensures that Manager.java pulls WorkerA.java
 * (and WorkerB.java via the second field) into the same IAPI compilation context,
 * enabling cross-file symbol-identity reference finding.
 */
public class Manager {

    /** Interface-typed field — calls on this go through IWorker symbol. */
    private IWorker worker;

    /**
     * Concrete-typed fields — calls on these resolve directly to WorkerA/WorkerB
     * symbols, not IWorker symbols.  This makes cross-file reference finding work
     * for WorkerA-specific (non-override) methods like {@code doubleWork}.
     */
    private WorkerA concreteA = new WorkerA();
    private WorkerB concreteB = new WorkerB();

    public Manager(IWorker w) {
        this.worker = w;
    }

    //@ requires amount >= 0;
    //@ ensures \result >= 0;
    public int delegateWork(int amount) {
        return worker.doWork(amount);
    }

    //@ ensures \result != null;
    public String getReport() {
        return worker.getStatus();
    }

    /**
     * Calls the WorkerA-specific {@code doubleWork} method via a concrete type.
     * Because {@code concreteA} has static type {@code WorkerA}, the call resolves
     * to {@code WorkerA.doubleWork.sym} — the same Symbol object as the declaration
     * in WorkerA.java.  This enables cross-file find-references and rename for
     * {@code doubleWork} without any interface dispatch ambiguity.
     */
    public int fastWork(int amount) {
        return concreteA.doubleWork(amount);
    }
}
