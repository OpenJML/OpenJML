import java.util.Queue;
public class Test {
    void f1(Queue<Integer> q) {
        //@ loop_modifies q.content.*; // fails
        //@ loop_invariant \invariant_for(q);
        while (!q.isEmpty())
            q.poll();
    }
    

    void f2(Queue<Integer> q) {
        //@ loop_invariant \invariant_for(q);
        //@ loop_modifies q.content; // fails
        // loop_modifies q.content.size; // works
        while (!q.isEmpty())
            q.poll();
    }
}