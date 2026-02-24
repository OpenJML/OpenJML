import java.util.Queue;
import java.util.PriorityQueue;

public class Mismatched {
    void mismatched(PriorityQueue<Object> q) { // Using Queue instead of PriorityQueue works
        q.add(null);
    }
}

// Queue.jml allows a null argument. PriorityQueue has no specs so it inherits Queue.jml's specs. 