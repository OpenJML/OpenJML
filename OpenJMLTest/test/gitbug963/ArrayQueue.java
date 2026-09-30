public class ArrayQueue<E> implements BoundedQueue<E> {
// Bounded queue implemented as a rotating array.
private E[] a; //@ in max, q; // contains the queue between head (included) and last (excluded)
private int head; //@ in q;
private int last; //@ in q;
private int size; //@ in q;
/*@ 
private invariant a != null;
private invariant 0 <= size <= a.length; // number of elements in the queue
private invariant 0 <= head < a.length; // index of the first element (if any)
private invariant 0 <= last < a.length; // index of the future last element, not yet in the queue
private invariant (head+size) % a.length == last;
private represents max = a.length;
private represents q = (size == 0) ? \seq.empty()
: (head < last) ? \seq.of(a[head..last-1])
: \seq.of(a[head..a.length-1])+\seq.of(a[0..last-1]);
@*/

/*@ requires m > 0;
 @ ensures q == \seq.<E>empty();
 @ ensures max == m;
 @ pure
 @*/
public ArrayQueue(int m) {
    E[] a = new E[m];
    head = last = size = 0;
}

public boolean isEmpty() {
    return size == 0;
}

public int size() {
    return size;
}

public int capacity() {
    return a.length;
}

//@ ensures \result <==> size() == capacity();
public boolean isFull() {
    return size == a.length;
}

public boolean add(E x) {
    if (!isFull()) {
        size++;
        a[last] = x;
        last = (last++) % a.length;
        return true; // has been added
    } else throw new IllegalStateException("Queue is full");
}

public E remove() {
    if (!isEmpty()) {
        size--;
        E result = a[head];
        head = (head++) % a.length;
        return result;  // can be null (when containsNull is true)
    }
    return null;
}

public E peek() {
    if (!isEmpty())
        return a[head]; // can be null (when containsNull is true)
    else return null;
}
}
