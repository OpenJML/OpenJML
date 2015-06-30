package freeboogie.util;

/**
 * Has the abstract method {@code go}. To be used as a closure.
 *
 * @author rgrig 
 * @author reviewed by TODO
 * @param <T> the type of the parameter of {@code go}
 */
public abstract class Closure<T> {
  /**
   * Process {@code t}
   * @param t what to process
   */
  abstract public void go(T t);
}
