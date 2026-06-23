import java.util.*;

public interface BoundedQueue<E> {

// similar to java.util.Queue but specified as bounded
//@ model public instance \seq<E> q; // in JML version < 2, use JMLObjectSequence
//@ model public instance int max; // The capacity (maximal size) of the queue, fixed at creation
//@ public constraint max == \old(max);
//@ public invariant size() <= max;

/* @ requires m > 0;
  @ ensures q == \seq.<E>empty();
  @ ensures max == m;
  @ pure
  BoundedQueue<E>(int m);  //creates an empty queue of capacity m. Constructors are forbidden in Java interfaces.
  */

// current number of items in the queue
//@ ensures \result == q.length();
//@ strictly_pure
int size();

//@ ensures \result == max;
//@ pure
int capacity();

//@ ensures \result == (size() == 0);
//@ strictly_pure
boolean isEmpty();

// according to the Java description of a queue, 'add' will return true if element o is really added,
// but will never return false and instead raise IllegalStateException when it fails.
/*@ requires size() < max;
@ ensures size() == \old(size()) + 1;
@ ensures  q == \old(q)+\seq.<E>of(o);
@ ensures \result;  // returns true
@ assignable q;
@ also
@ exceptional_behaviour
@ requires size() == max;    //full
@ assignable \nothing;
@ signals (IllegalStateException e);
 @*/
boolean add(E o);

// Returns and removes the head of the queue.
/*@  normal_behavior
  @   requires !isEmpty();
  @   assignable q;
  @   ensures \result == \old(q[0]);
  @   ensures (\forall int i; 0 < i < q.length; q[i-1] == \old(q[i]));
  @   ensures size() == \old(size()) -1;
@ also
@ exceptional_behaviour
@ requires size() == 0;
@   assignable \nothing;
@ signals (NoSuchElementException e);
 @*/
E remove();

// Returns the head of the queue, or null if empty.
/*@ normal_behavior
  @   requires !isEmpty();
  @   ensures \result == q[0];
 @ also
 @ normal_behavior
 @ requires isEmpty();
 @   ensures \result == null;
 @ pure
  @*/
E peek();
}