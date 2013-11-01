// Problem reported by DMZ on 10/30

/**
 * Implements a doubly linked list.
 * 
 * @author Kevin Vigue
 * @version 9/18/2013
 * @param <T> Type stored in list.
 */
public class DoublyLinkedList<T>
{
  /**
   * The linked list node after this one.
   * 
   * @author Kevin Vigue
   * @version 9/18/2013
   */
  private DoublyLinkedList<T> my_next;
  
  /**
   * The linked list node before this one.
   * 
   * @author Kevin Vigue
   * @version 9/18/2013
   */
  private DoublyLinkedList<T> my_prev;
  
  /**
   * The value stored in this linked list node.
   * 
   * @author Kevin Vigue
   * @version 9/18/2013
   */
  private T my_value;
  
  /**
   * Constructor that takes a value.
   * 
   * @author Kevin Vigue
   * @version 9/18/2013
   * @param a_value Data to be stored in my_value.
   */
  public DoublyLinkedList(final T a_value)
  {
    my_next = null;
    my_prev = null;
    my_value = a_value;
  }
  
  /**
   * Constructor that lets you specify my_prev, my_value, and my_next.
   * 
   * @author Kevin Vigue
   * @version 9/18/2013
   * @param a_prev Doubly linked list that comes before this one.
   * @param a_value Value to be stored in this node.
   * @param a_next Doubly linked list that comes after this one.
   */
  public DoublyLinkedList(final DoublyLinkedList<T> a_prev, final T a_value,
                          final DoublyLinkedList<T> a_next)
  {
    my_next = a_next;
    my_prev = a_prev;
    my_value = a_value;
  }
  
  /**
   * Getter for my_value.
   * 
   * @author Kevin Vigue
   * @version 9/18/2013
   * @return The value in this node.
   */
  public T getValue()
  {
    return my_value;
  }
  
  /**
   * Setter for my_value.
   * 
   * @author Kevin Vigue
   * @version 9/18/2013
   * @param a_value New value for this node.
   */
  public void setValue(final T a_value)
  {
    my_value = a_value;
  }
  
  /**
   * Getter for my_prev.
   * 
   * @author Kevin Vigue
   * @version 9/18/2013
   * @return The doubly linked list before this one.
   */
  public DoublyLinkedList<T> getPrev()
  {
    return my_prev;
  }
  
  /**
   * Setter for my_prev.
   * 
   * @author Kevin Vigue
   * @version 9/18/2013
   * @param a_doubly_linked_list New node to come before this one.
   */
  public void setPrev(final DoublyLinkedList<T> a_doubly_linked_list)
  {
    // A doubly linked list's next is not itself.
    assert a_doubly_linked_list != this : "Attempt to set prev to self.";
    my_prev = a_doubly_linked_list;
  }
  
  /**
   * Getter for my_next.
   * 
   * @author Kevin Vigue
   * @version 9/18/2013
   * @return The doubly linked list after this one.
   */
  public DoublyLinkedList<T> getNext()
  {
    return my_next;
  }
  
  /**
   * Setter for my_next.
   * 
   * @author Kevin Vigue
   * @version 9/18/2013
   * @param a_doubly_linked_list New node to come after this one.
   */
  public void setNext(final DoublyLinkedList<T> a_doubly_linked_list)
  {
    // A doubly linked list's prev is not itself.
    assert a_doubly_linked_list != this : "Attempt to set next to self.";
    my_next = a_doubly_linked_list;
  }
  
  /**
   * Removes this node from the larger doubly linked list structure.
   * 
   * @author Kevin Vigue
   * @version 9/18/2013
   */
  public void remove()
  {
    if (my_prev != null)
    {
      my_prev.setNext(my_next);
    }
    if (my_next != null)
    {
      my_next.setPrev(my_prev);
    }
  }
}
