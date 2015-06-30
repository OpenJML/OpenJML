package freeboogie.ast.gen;

/**
 * Interface for stream location tracking.
 * 
 * When a {@code Location} object {@code n} is created using the default 
 * constructor it should point just <i>before</i> the beginning
 * of the stream. The location {@code n.advance(a).advance(b).advance(c)}
 * should reflect the position of element {@code c} given that it is
 * preceded (only by) {@code a} and {@code b}.
 * 
 * Note that subclasses implementations of {@code advance} will return
 * {@code Location<T>} instead of something more specific because Java
 * does not allow covariant return types. As a results some casts will
 * be necessary.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 * @param <T> the type of the stream element
 */
public abstract class Location<T> {
  
  /**
   * Advance the location by one element.
   * @param element the last element eaten (read) from the stream
   * @return a location that points at {@code element}, given that 
   *   {@code this} points just before
   */
  public abstract Location<T> advance(T element);
  
  /**
   * Returns a human-readable description of the location of the last
   * element received as a parameter by advance.
   * 
   * @return a human-readable description of the location
   */
  @Override
  public abstract String toString();

}
